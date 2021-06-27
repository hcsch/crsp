# crsp (WIP)
A CHIP-8 emulator written in Rust.

## WIP
So far only headless processor emulation code has been written
(in [crsp-base](crsp-base))
and that is also still lacking some timing, sound and screen related code.
The main crate [crsp](crsp) will contain code for a GUI binary for this emulator.

## Naming
(CHIP(-8) → crisp) + Rust (rs) = crsp

## License
This project is licensed under the [MIT license](LICENSE).

## References used

Matthew Mikolay's
[CHIP‐8 Technical Reference](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Technical-Reference#references),
[CHIP‐8 Instruction Set](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Instruction-Set),
and [CHIP‐8 Extensions Reference](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Extensions-Reference).

[The Wikipedia article on CHIP-8](https://en.wikipedia.org/wiki/CHIP-8).

Jackson Sommerich's
[Chip 8 Instruction Scheduling and Frequency](https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html)
([archived](https://web.archive.org/web/20210626163444/https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html) for posterity),
which in turn is based on Laurence Scotford's
[Chip 8 on the COSMAC VIP](https://web.archive.org/web/20170224084655/http://laurencescotford.co.uk/?p=405),
which I have also read some parts of.
