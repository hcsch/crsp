macro_rules! pixel_to_bit {
    (#) => {
        1
    };
    (,) => {
        0
    };
}

macro_rules! sprite_4x5_font {
    (
        $(
            $(
                ($pixel0:tt $pixel1:tt $pixel2:tt $pixel3:tt)
            )*
            ------
        )*
    ) => {
        [
            $(
                $(
                    // Shift pixels into high nibble / left half of the sprite.
                    (pixel_to_bit!($pixel0) << 7
                        & pixel_to_bit!($pixel1) << 6
                        & pixel_to_bit!($pixel2) << 5
                        & pixel_to_bit!($pixel3) << 4),
                )*
            )*
        ]
    };
}

/// A sprite font of all hexadecimal digits for the CHIP-8.
pub enum Font {
    /// A blocky font.
    Blocky,
    /// A rounder font.
    Round,
}

impl Font {
    /// Length of the font sprite data in bytes.
    pub const LEN: usize = 5 * (0xF + 1);

    /// Get a reference to the font's sprite data bytes.
    ///
    /// Since a CHIP-8 sprite is always one byte wide,
    /// the low nibble is 0 for all of these character sprites.
    /// The actual symbols are in the high nibble only.
    pub const fn bytes(&self) -> &[u8; 5 * (0xF + 1)] {
        match self {
            Self::Blocky => &SPRITE_4X5_FONT_BLOCKY,
            Self::Round => &SPRITE_4X5_FONT_ROUND,
        }
    }
}

impl Default for Font {
    fn default() -> Self {
        Self::Round
    }
}

/// A blocky 4x5 sprite font of the hexadecimal digits.
const SPRITE_4X5_FONT_BLOCKY: [u8; Font::LEN] = sprite_4x5_font![
    (####)
    (#,,#)
    (#,,#)
    (#,,#)
    (####)
    ------
    (,,#,)
    (,,#,)
    (,,#,)
    (,,#,)
    (,,#,)
    ------
    (####)
    (,,,#)
    (####)
    (#,,,)
    (####)
    ------
    (####)
    (,,,#)
    (####)
    (,,,#)
    (####)
    ------
    (#,,#)
    (#,,#)
    (####)
    (,,,#)
    (,,,#)
    ------
    (####)
    (#,,,)
    (####)
    (,,,#)
    (####)
    ------
    (####)
    (#,,,)
    (####)
    (#,,#)
    (####)
    ------
    (####)
    (,,,#)
    (,,,#)
    (,,,#)
    (,,,#)
    ------
    (####)
    (#,,#)
    (####)
    (#,,#)
    (####)
    ------
    (####)
    (#,,#)
    (####)
    (,,,#)
    (####)
    ------
    (####)
    (#,,#)
    (####)
    (#,,#)
    (#,,#)
    ------
    (###,)
    (#,,#)
    (####)
    (#,,#)
    (###,)
    ------
    (####)
    (#,,,)
    (#,,,)
    (#,,,)
    (####)
    ------
    (###,)
    (#,,#)
    (#,,#)
    (#,,#)
    (###,)
    ------
    (####)
    (#,,,)
    (####)
    (#,,,)
    (####)
    ------
    (####)
    (#,,,)
    (####)
    (#,,,)
    (#,,,)
    ------
];

/// A rounder 4x5 sprite font of the hexadecimal digits.
const SPRITE_4X5_FONT_ROUND: [u8; Font::LEN] = sprite_4x5_font![
    (,##,)
    (#,,#)
    (#,,#)
    (#,,#)
    (,##,)
    ------
    (,,#,)
    (,##,)
    (,,#,)
    (,,#,)
    (,###)
    ------
    (###,)
    (,,,#)
    (,,##)
    (,##,)
    (####)
    ------
    (###,)
    (,,,#)
    (####)
    (,,,#)
    (###,)
    ------
    (#,,#)
    (#,,#)
    (,###)
    (,,,#)
    (,,,#)
    ------
    (####)
    (#,,,)
    (###,)
    (,,,#)
    (###,)
    ------
    (,###)
    (#,,,)
    (###,)
    (#,,#)
    (,##,)
    ------
    (####)
    (,,,#)
    (,,#,)
    (,#,,)
    (,#,,)
    ------
    (,##,)
    (#,,#)
    (,##,)
    (#,,#)
    (,##,)
    ------
    (,##,)
    (#,,#)
    (,###)
    (,,,#)
    (###,)
    ------
    (,##,)
    (#,,#)
    (####)
    (#,,#)
    (#,,#)
    ------
    (###,)
    (#,,#)
    (####)
    (#,,#)
    (###,)
    ------
    (,##,)
    (#,,#)
    (#,,,)
    (#,,#)
    (,##,)
    ------
    (###,)
    (#,,#)
    (#,,#)
    (#,,#)
    (###,)
    ------
    (,###)
    (#,,,)
    (####)
    (#,,,)
    (,###)
    ------
    (,###)
    (#,,,)
    (####)
    (#,,,)
    (#,,,)
    ------
];
