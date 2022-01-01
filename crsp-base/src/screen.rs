use std::fmt::{Debug, Write};

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Screen {
    pub pixel_data: [u8; Self::WIDTH_BYTES as usize * Self::HEIGHT as usize],
}

impl Screen {
    pub const WIDTH_BYTES: usize = 8;
    pub const WIDTH: u8 = Self::WIDTH_BYTES as u8 * u8::BITS as u8;
    pub const HEIGHT: u8 = 32;

    /// Draw byte to `screen` at position `byte_x*8` and `y`.
    /// Does not take `&mut self` so it can be called while iterating over a sprite in `self.memory`.
    ///
    /// Returns `true` if a set pixel has been unset, `false` otherwise.
    fn draw_byte(&mut self, byte_x: usize, y: usize, byte: u8) -> bool {
        // A one in the original byte and the shifted sprite byte's bits
        // will result in a set pixel being unset.
        let set_pixel_unset = (self.pixel_data[byte_x + y * Self::WIDTH_BYTES as usize] & byte) > 0;

        self.pixel_data[byte_x + y * Self::WIDTH_BYTES as usize] ^= byte;

        set_pixel_unset
    }

    pub fn draw_sprite(
        &mut self,
        x: u8,
        y: u8,
        sprite: &[u8],
        partial_offscreen_drawing: PartialOffscreenDrawing,
    ) -> bool {
        let x = (x % Self::WIDTH) as usize;
        let y = (y % Self::HEIGHT) as usize;
        let mut set_pixel_unset = false;

        for (i, sprite_byte) in sprite.iter().copied().enumerate() {
            // Wrap y if we should, else we're done for the entire sprite.
            let y = if y + i < Self::HEIGHT as usize
                || (y + i >= Self::HEIGHT as usize && partial_offscreen_drawing.should_wrap_y())
            {
                (y + i) % Self::HEIGHT as usize
            } else {
                break;
            };

            set_pixel_unset |= self.draw_byte(x / 8, y, sprite_byte >> (x % 8));

            // If x is exactly at the start of a screen byte, we're done.
            // We're also done if the next byte is offscreen and we shouldn't wrap in X.
            if x % 8 == 0
                || (x + 7 >= Self::WIDTH as usize && !partial_offscreen_drawing.should_wrap_x())
            {
                continue;
            }

            // Draw remaining bits into next byte (possibly wrapping around in X)

            let rem_sprite_byte = sprite_byte << (8 - (x % 8));
            let rem_x = (x + (8 - (x % 8))) % Self::WIDTH as usize;

            set_pixel_unset |= self.draw_byte(rem_x / 8, y, rem_sprite_byte);
        }

        set_pixel_unset
    }

    pub fn clear(&mut self) {
        self.pixel_data.fill(0);
    }
}

impl Default for Screen {
    fn default() -> Self {
        Self {
            pixel_data: [0; Self::WIDTH_BYTES as usize * Self::HEIGHT as usize],
        }
    }
}

impl Debug for Screen {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            writeln!(f, "Screen(")?;
            for c in self
                .pixel_data
                .array_chunks()
                .flat_map(|row: &[u8; Self::WIDTH_BYTES]| {
                    row.iter()
                        .copied()
                        .flat_map(|screen_byte| {
                            (0..8)
                                .rev()
                                .map(move |i| if screen_byte >> i & 1 > 0 { '#' } else { '_' })
                        })
                        .chain(['\n'])
                })
            {
                f.write_char(c)?;
            }
            write!(f, ")")
        } else {
            f.debug_tuple("Screen").field(&self.pixel_data).finish()
        }
    }
}

/// Drawing behavior for sprites that are partially offscreen.
///
/// Sprites that are drawn at coordinates fully offscreen will *always*
/// have the modulo of the screen size applied to their coordinates.
/// The partial offscreen drawing behavior will be applied after this.
/// See also [`Instruction::DrawSprite`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialOffscreenDrawing {
    /// Clip offscreen parts of sprites in both X and Y.
    ClipXY,
    /// Clip offscreen parts of sprites in X, wrap in Y.
    ClipXWrapY,
    /// Wrap offscreen parts of sprites in X, clip in Y.
    WrapXClipY,
    /// Wrap offscreen parts of sprites in both X and Y.
    WrapXY,
}

impl Default for PartialOffscreenDrawing {
    fn default() -> Self {
        Self::ClipXY
    }
}

impl PartialOffscreenDrawing {
    pub fn should_wrap_x(self) -> bool {
        match self {
            Self::WrapXY | Self::WrapXClipY => true,
            _ => false,
        }
    }

    pub fn should_wrap_y(self) -> bool {
        match self {
            Self::WrapXY | Self::ClipXWrapY => true,
            _ => false,
        }
    }
}
