macro_rules! pixel_to_bit {
    (#) => {
        1
    };
    (,) => {
        0
    };
}

macro_rules! make_giant_array {
    ($($elem:expr,)*) => {
        [
            $($elem),*
        ]
    };
}

macro_rules! sprite_4x5_font {
    ($($(($pixel0:tt $pixel1:tt $pixel2:tt $pixel3:tt))* ------)*) => {
        make_giant_array![
            $(
                    $(
                        (pixel_to_bit!($pixel0) << 7
                            & pixel_to_bit!($pixel1) << 6
                            & pixel_to_bit!($pixel2) << 5
                            & pixel_to_bit!($pixel3) << 4),
                    )*
            )*
        ]
    };
}

pub enum Font {
    Blocky,
    Round,
}

impl Font {
    pub const fn bytes(&self) -> &[u8; 5 * (0xF + 1)] {
        match self {
            Self::Blocky => &SPRITE_4X5_FONT_BLOCKY,
            Self::Round => &SPRITE_4X5_FONT_ROUND,
        }
    }
}

/// A blocky 4x5 sprite font of the hexadecimal digits.
///
/// Since a CHIP-8 sprite is always one byte wide,
/// the low nibble is 0 for all of these character sprites.
/// The actual symbols are in the high nibble only.
pub const SPRITE_4X5_FONT_BLOCKY: [u8; 5 * (0xF + 1)] = sprite_4x5_font![
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
///
/// Since a CHIP-8 sprite is always one byte wide,
/// the low nibble is 0 for all of these character sprites.
/// The actual symbols are in the high nibble only.
pub const SPRITE_4X5_FONT_ROUND: [u8; 5 * (0xF + 1)] = sprite_4x5_font![
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
