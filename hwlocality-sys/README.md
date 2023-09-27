# hwlocality-sys: The low-level bindings below hwlocality

This crate contains the low-level unsafe Rust -> C FFI bindings to
[hwloc](http://www.open-mpi.org/projects/hwloc), that are used to implement the
safe [hwlocality](https://github.com/HadrienG2/hwlocality) bindings.

Like any C API, these low-level bindings are highly unsafe to use, and it is
advised that you use the safe bindings instead whenever possible.

If you encounter any issue with the safe bindings that prevents you from using
them and forces you to use the unsafe C API directly, please report it to me.
