# crsp (WIP)

[![crates.io](https://img.shields.io/crates/v/crsp?style=flat-square)](https://crates.io/crates/crsp)
[![License](https://img.shields.io/badge/license-MIT-blue?style=flat-square)](https://github.com/hcsch/crsp/blob/master/LICENSE)

A CHIP-8 emulator written in Rust.

## WIP
The emulator already supports running a CHIP-8 ROM specified as a CLI argument,
but some aspects of the emulator still need to be made configurable.

So far there is also no option for configuring the emulator graphically
(e.g. loading a ROM through a file chooser dialog, displaying errors with recovery options, etc.).

## Running

```sh
cargo run --release -- <rom-file>
```

For a more detailed description see the output of
```sh
cargo run -- --help
```

## Logs / Traces

The emulator uses the [tracing](https://crates.io/crates/tracing)
and [tracing-subscriber](https://crates.io/crates/tracing-subscriber)
crates for logging/tracing.

To have the emulator print events to stdout at various levels of verbosity,
run it with the environment variable `RUST_LOG` set to one of
`error`, `warn`, `info`, `debug` and `trace`, or use a more complex filter as described
[here](https://docs.rs/tracing-subscriber/0.2.19/tracing_subscriber/filter/struct.EnvFilter.html).
Errors and warnings will be printed to stdout by default.

Example:
```sh
RUST_LOG="crsp=debug,crsp-base=debug" cargo run --release -- <rom-file>
```
This will print all events with level `debug` or higher from the `crsp` and `crsp-base` crates.

## Naming
(CHIP(-8) → crisp) + Rust (rs) = crsp

## License
This project is licensed under the [MIT license](LICENSE).

## References
- [CHIP‐8 Technical Reference](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Technical-Reference#references) - Matthew Mikolay
- [CHIP‐8 Instruction Set](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Instruction-Set) - Matthew Mikolay
- [CHIP‐8 Extensions Reference](https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Extensions-Reference) - Matthew Mikolay
- [CHIP-8 (Wikipedia)](https://en.wikipedia.org/wiki/CHIP-8) - Wikipedia
- [Chip 8 Instruction Scheduling and Frequency](https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html) ([Archive](https://web.archive.org/web/20210626163444/https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html)) - Jackson Sommerich
- [Chip 8 on the COSMAC VIP: Instruction Index](https://web.archive.org/web/20170224084655/http://laurencescotford.co.uk/?p=405) - Lawrence Scotford
