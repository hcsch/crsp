use std::time::Duration;

use rodio::Source;

/// An infinite source that produces a sinusoidal tone with some overtones.
///
/// Always has a rate of 48kHz and one channel.
#[derive(Clone, Debug)]
pub struct EmulatorTone {
    frequency: f32,
    current_sample: usize,
}

impl EmulatorTone {
    /// The maximum amplitudes of the harmonics of this tone.
    /// All harmonics are added up and scaled to have a total maximum amplitude of one,
    /// so these maximum amplitudes merely describe the mixing ratio.
    /// Includes the amplitude for the base frequency for convenience.
    const HARMONICS_MAX_AMPLITUDES: [f32; 5] = [
        1.0,       // fundamental tone
        1.0 / 2.0, // 1. overtone
        1.0 / 3.0, // 2. overtone
        1.0 / 5.0, // 3. overtone
        1.0 / 7.0, // 4. overtone
    ];

    pub fn new(frequency: f32) -> Self {
        Self {
            frequency,
            current_sample: 0,
        }
    }
}

impl Iterator for EmulatorTone {
    type Item = f32;

    fn next(&mut self) -> Option<f32> {
        let time = self.current_sample as f32 / self.sample_rate() as f32;

        self.current_sample = self.current_sample.wrapping_add(1);

        let sample = Self::HARMONICS_MAX_AMPLITUDES
            .iter()
            .copied()
            .enumerate()
            .map(|(harmonic, max_amplitude)| {
                (2.0 * std::f32::consts::PI * self.frequency * harmonic as f32 * time).sin()
                    * max_amplitude
            })
            .sum::<f32>()
            / Self::HARMONICS_MAX_AMPLITUDES.iter().sum::<f32>();

        Some(sample)
    }
}

impl Source for EmulatorTone {
    fn current_frame_len(&self) -> Option<usize> {
        None
    }

    fn channels(&self) -> u16 {
        1
    }

    fn sample_rate(&self) -> u32 {
        48_000
    }

    fn total_duration(&self) -> Option<Duration> {
        None
    }
}
