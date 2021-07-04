use std::{path::PathBuf, thread};

use clap::{crate_description, crate_version, AppSettings, Clap};
use crsp_base::processor::{
    ControlEvent, Key, KeyState, PartialOffscreenDrawing, Processor, ProcessorEvent,
};
use pixels::{Pixels, SurfaceTexture};
use rodio::{OutputStream, Sink};
use tracing::{debug, error, info, warn};
use tracing_subscriber::{self, fmt::format::FmtSpan, EnvFilter};
use winit::{
    dpi::{LogicalPosition, LogicalSize, PhysicalSize},
    event::{ElementState, Event, VirtualKeyCode, WindowEvent},
    event_loop::{ControlFlow, EventLoop},
};

use crate::tone::EmulatorTone;

mod tone;

// TODO: make colors configurable (at runtime)
/// RGB color for the pixel on-state
const COLOR_PIXEL_ON: [u8; 3] = [0xFF, 0xFF, 0xFF];
/// RGB color for the pixel off-state
const COLOR_PIXEL_OFF: [u8; 3] = [0x00, 0x00, 0x00];

trait TryIntoKey {
    type Error;

    fn try_into_key(&self) -> Result<Key, Self::Error>;
}

impl TryIntoKey for VirtualKeyCode {
    type Error = ();

    fn try_into_key(&self) -> Result<Key, Self::Error> {
        use VirtualKeyCode::*;

        // TODO: only works for german keyboard layout
        match *self {
            // row 1
            Key1 => Ok(Key::K1),
            Key2 => Ok(Key::K2),
            Key3 => Ok(Key::K3),
            Key4 => Ok(Key::KC),
            // row 2
            Q => Ok(Key::K4),
            W => Ok(Key::K5),
            E => Ok(Key::K6),
            R => Ok(Key::KD),
            // row 3
            A => Ok(Key::K7),
            S => Ok(Key::K8),
            D => Ok(Key::K9),
            F => Ok(Key::KE),
            // row 4
            Y => Ok(Key::KA),
            X => Ok(Key::K0),
            C => Ok(Key::KB),
            V => Ok(Key::KF),
            _ => Err(()),
        }
    }
}

trait IntoKeyState {
    fn into_key_state(&self) -> KeyState;
}

impl IntoKeyState for ElementState {
    fn into_key_state(&self) -> KeyState {
        match *self {
            ElementState::Pressed => KeyState::Pressed,
            ElementState::Released => KeyState::NotPressed,
        }
    }
}

#[derive(Debug, Clap)]
#[clap(
    version = crate_version!(),
    author = "Hans Christian Schmitz",
    about = crate_description!(),
    setting = AppSettings::ColoredHelp
)]
struct CliOpts {
    /// The path to the file containing the ROM.
    /// The file's contents will be loaded into the emulator's memory,
    /// starting at address 0x200.
    rom_file: PathBuf,
    /// The clipping/wrapping behavior for sprites that are drawn partially offscreen.
    #[clap(
        short,
        long,
        default_value = "clip-xy",
        possible_values = &["clip-xy", "clip-x-wrap-y", "wrap-x-clip-y", "wrap-xy"]
    )]
    partial_offscreen_drawing: String,
}

// TODO: decide where to use logging and where to panic with .except()

fn main() -> Result<(), pixels::Error> {
    let cli_opts = CliOpts::parse();

    tracing_subscriber::fmt()
        .pretty()
        .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let event_loop = EventLoop::<ProcessorEvent>::with_user_event();

    let (window, size) = create_window(
        &event_loop,
        "crsp",
        PhysicalSize::new(
            Processor::SCREEN_WIDTH as u32,
            Processor::SCREEN_HEIGHT as u32,
        ),
    );
    let surface_texture = SurfaceTexture::new(size.width, size.height, &window);
    let mut pixels = Pixels::new(
        Processor::SCREEN_WIDTH as u32,
        Processor::SCREEN_HEIGHT as u32,
        surface_texture,
    )?;

    let (_stream, stream_handle) = OutputStream::try_default().unwrap();
    let sink = Sink::try_new(&stream_handle).unwrap();
    sink.set_volume(0.5);
    sink.pause();

    let sine_source = EmulatorTone::new(440.0);
    sink.append(sine_source);

    let program = &std::fs::read(cli_opts.rom_file).unwrap();
    let processor = Processor::builder()
        //.skip_call_machine_subroutine()
        .partial_offscreen_drawing(match cli_opts.partial_offscreen_drawing.as_str() {
            "clip-xy" => PartialOffscreenDrawing::ClipXY,
            "clip-x-wrap-y" => PartialOffscreenDrawing::ClipXWrapY,
            "wrap-x-clip-y" => PartialOffscreenDrawing::WrapXClipY,
            "wrap-xy" => PartialOffscreenDrawing::WrapXY,
            _ => unreachable!("restricted to the above strings by clap possible_values"),
        })
        .program(&program)
        .unwrap()
        .build();
    let mut screen = processor.screen().clone();
    let (control_event_sender, processor_event_receiver, processor_join_handle) = processor.start();

    let mut control_event_sender = Some(control_event_sender);
    let mut processor_join_handle = Some(processor_join_handle);

    let mut waiting_for_key_press = true;

    let event_loop_proxy = event_loop.create_proxy();
    thread::Builder::new()
        .name("processor event forwarder".to_owned())
        .spawn(move || loop {
            let event = match processor_event_receiver.recv() {
                Ok(event) => event,
                Err(_) => break, // event sender closed, stop
            };
            match event_loop_proxy.send_event(event) {
                Ok(()) => (),
                Err(_) => break, // event loop closed, stop
            }
        })
        .expect("could not spawn processor event forwarder thread");

    event_loop.run(move |event, _, control_flow| {
        *control_flow = ControlFlow::Wait;
        match event {
            Event::WindowEvent { event, .. } => match event {
                WindowEvent::Resized(size) => pixels.resize_surface(size.width, size.height),
                WindowEvent::CloseRequested => {
                    // dropping this will make the processor stop
                    drop(control_event_sender.take().unwrap());
                    // stop audio
                    sink.stop();
                    // wait for processor to stop
                    let processor_runner_result = processor_join_handle
                        .take()
                        .unwrap()
                        .join()
                        .expect("processor thread panicked");
                    if let Err(error) = processor_runner_result {
                        // We are shutting down,
                        // so the error shouldn't be handled graphically anymore.
                        // Logging doesn't hurt though.
                        warn!(?error, "error occurred running the CHIP-8 ROM");
                    }

                    *control_flow = ControlFlow::Exit;
                }
                WindowEvent::Focused(_) => (),
                WindowEvent::KeyboardInput {
                    input:
                        winit::event::KeyboardInput {
                            state,
                            virtual_keycode: Some(virtual_keycode),
                            ..
                        },
                    ..
                } => {
                    debug!(?virtual_keycode, ?state, "key state changed");
                    if virtual_keycode == VirtualKeyCode::Escape && state == ElementState::Pressed {
                        info!("escape key pressed, exiting...");
                        *control_flow = ControlFlow::Exit;
                    } else {
                        virtual_keycode.try_into_key().ok().map(|key| {
                            if state == ElementState::Pressed {
                                waiting_for_key_press = false;
                            }
                            control_event_sender
                                .as_mut()
                                .unwrap()
                                .send(ControlEvent::KeyStateChange {
                                    key,
                                    new_state: state.into_key_state(),
                                })
                                .expect("processor stopped due to error or panic");
                            // TODO: handle graphically
                        });
                    }
                }
                WindowEvent::ModifiersChanged(_) => (),
                WindowEvent::ThemeChanged(_) => todo!(), // maybe some time
                _ => (),
            },
            Event::Suspended => todo!(),
            Event::Resumed => todo!(),
            Event::UserEvent(ProcessorEvent::ErrorEncountered { .. }) => {
                // TODO: handle graphically (e.g. with the option of restarting while skipping unsupported instructions)
                *control_flow = ControlFlow::Exit
            }
            Event::UserEvent(ProcessorEvent::ScreenUpdate { new_screen }) => {
                screen = new_screen;
                window.request_redraw();
            }
            Event::UserEvent(ProcessorEvent::WaitForKeyPress) => waiting_for_key_press = true,
            Event::UserEvent(ProcessorEvent::StartPlayingSound) => sink.play(),
            Event::UserEvent(ProcessorEvent::StopPlayingSound) => sink.pause(),
            Event::RedrawRequested(_) => {
                pixels
                    .get_frame()
                    .chunks_exact_mut(4)
                    .zip(
                        screen
                            .iter()
                            .copied()
                            .flat_map(|byte| (0..8).rev().map(move |i| byte >> i & 1 > 0)),
                    )
                    .for_each(|(frame_pixel, screen_pixel_on)| {
                        frame_pixel[0..3].copy_from_slice(if screen_pixel_on {
                            &COLOR_PIXEL_ON
                        } else {
                            &COLOR_PIXEL_OFF
                        }); // RGB
                        frame_pixel[3] = 0xFF; // alpha
                    });
                if pixels
                    .render()
                    .map_err(|error| {
                        error!(
                            ?error,
                            "pixels failed to draw pixel buffer to surface texture"
                        )
                    })
                    .is_err()
                {
                    *control_flow = ControlFlow::Exit;
                    return;
                }
            }
            _ => (),
        }
    });
}

fn create_window<T>(
    event_loop: &EventLoop<T>,
    title: &str,
    pixel_buffer_size: PhysicalSize<u32>,
) -> (winit::window::Window, PhysicalSize<u32>) {
    let pixel_buffer_size: PhysicalSize<f64> = pixel_buffer_size.cast();

    let window = winit::window::WindowBuilder::new()
        .with_visible(false)
        .with_title(title)
        .build(event_loop)
        .unwrap();

    let hidpi_factor = window.scale_factor();
    let (monitor_width, monitor_height) = {
        if let Some(monitor) = window.current_monitor() {
            let size = monitor.size().to_logical(hidpi_factor);
            (size.width, size.height)
        } else {
            (pixel_buffer_size.width, pixel_buffer_size.height)
        }
    };

    // Scale to two thirds of the smaller dimension of the monitor,
    // relative to the size of the pixel buffer.
    let scale = [
        (monitor_width / pixel_buffer_size.width),
        (monitor_height / pixel_buffer_size.height),
    ]
    .iter()
    .copied()
    .map(|scale| (scale * 2.0 / 3.0).round().max(1.0))
    .reduce(|min_scale, scale| min_scale.min(scale))
    .unwrap();

    // Smaller than pixel_buffer_size logical pixels doesn't really make sense.
    let min_size = pixel_buffer_size.to_logical::<f64>(hidpi_factor);

    let default_size = LogicalSize::new(
        pixel_buffer_size.width * scale,
        pixel_buffer_size.height * scale,
    );

    let upper_left_of_centered = LogicalPosition::new(
        (monitor_width - default_size.width) / 2.0,
        (monitor_height - default_size.height) / 2.0,
    );

    window.set_min_inner_size(Some(min_size));
    window.set_inner_size(default_size);
    window.set_outer_position(upper_left_of_centered);
    window.set_visible(true);

    let physical_default_size = default_size.to_physical::<f64>(hidpi_factor);

    (
        window,
        PhysicalSize::new(
            physical_default_size.width.round() as u32,
            physical_default_size.height.round() as u32,
        ),
    )
}
