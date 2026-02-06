# hwlocality-sys: The low-level bindings below hwlocality

[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
[![On crates.io](https://img.shields.io/crates/v/hwlocality-sys.svg)](https://crates.io/crates/hwlocality-sys)
[![On docs.rs](https://docs.rs/hwlocality-sys/badge.svg)](https://docs.rs/hwlocality-sys/)
[![Continuous Integration](https://img.shields.io/github/actions/workflow/status/HadrienG2/hwlocality/ci.yml?branch=main)](https://github.com/HadrienG2/hwlocality/actions?query=workflow%3A%22Continuous+Integration%22)
[![CII Best Practices Summary](https://img.shields.io/cii/summary/7876)](https://www.bestpractices.dev/en/projects/7876)
![Requires rustc
1.84.0+](https://img.shields.io/badge/rustc-1.84.0+-lightgray.svg)

This crate contains the low-level unsafe Rust -> C FFI bindings to
[hwloc](http://www.open-mpi.org/projects/hwloc), that are used to implement the
safe [hwlocality](https://github.com/HadrienG2/hwlocality) bindings.

Depending on your needs, you can either link to a `libhwloc` that is
pre-installed on your computer or have `hwlocality` build its own copy
`libhwloc` internally. Please read [the "Prerequisites" section of the
hwlocality README](https://github.com/HadrienG2/hwlocality#prerequisites) for
more information about these two options.

Like any C API, the `hwlocality-sys` low-level bindings are highly unsafe to
use, and it is advised that you use the safe `hwlocality` bindings instead
whenever possible. If you encounter any issue with the safe bindings that
prevents you from using them and forces you to use the unsafe C API directly,
please report them in the issue tracker so we get them fixed.
