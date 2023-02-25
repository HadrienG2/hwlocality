# hwlocality: Rust bindings for the hwloc library

[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
[![On crates.io](https://img.shields.io/crates/v/hwlocality.svg)](https://crates.io/crates/hwlocality)
[![On docs.rs](https://docs.rs/hwlocality/badge.svg)](https://docs.rs/hwlocality/)
[![Continuous Integration](https://github.com/HadrienG2/hwlocality/workflows/Continuous%20Integration/badge.svg)](https://github.com/HadrienG2/hwlocality/actions?query=workflow%3A%22Continuous+Integration%22)

## What is this?

To optimize programs for parallel performance on all hardware, you must accept
that on many common platforms,
[symmetric multiprocessing](https://en.wikipedia.org/wiki/Symmetric_multiprocessing)
is a lie. "CPUs" detected by the operating system often have inequal access
to shared resources like caches, DRAM and I/O peripherals, sometimes even
inequal specifications (as in Arm big.LITTLE, Apple Mx and Intel Adler Lake),
and significant performance gains can be achieved by taking this into account in
your code.

This is the latest maintained Rust binding to
[hwloc](http://www.open-mpi.org/projects/hwloc), a C library from Open MPI
for detecting the hierarchical topology of modern architectures. This includes
objects such as NUMA memory nodes, sockets, shared data & instruction caches,
cores, and simultaneous multi threading.

It is based on and still shares some code and design with previous,
now-unmaintained attempts to write Rust hwloc bindings at
[Ichbinjoe/hwloc2-rs](https://github.com/Ichbinjoe/hwloc2-rs) and
[daschl/hwloc-rs](https://github.com/daschl/hwloc-rs), but it does not aim for
API compatibility with them. Indeed, many changes have been made with respect to
hwloc2-rs in the aim of improving ergonomics, performance, and removing avenues
for Undefined Behaviour like assuming pointers are non-null or union fields are
valid when nobody tells you they will always be.

## Prerequisites

A system installed with hwloc >=2.0.0 and associated development packages installed.

By default, compatibility with all hwloc 2.x versions is aimed for, which means
features from newer versions in the 2.x series (or, in the near future,
compatibility with breaking changes from the 3.x series) are not provided by
default. To tune this compatibility compromise, you can use Cargo features
(TODO explain how once implemented).

Beware that some Linux distributions provide older hwloc versions. You may have
to install it from [source code](https://www.open-mpi.org/projects/hwloc/).

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
hwlocality = "1.0.0"
```

Here is a quick example which walks the `Topology` and prints it out:

```rust
use hwlocality::Topology;

fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    for depth in 0..topology.depth() {
        println!("*** Objects at depth {depth}");

        for (idx, object) in topology.objects_at_depth(depth).enumerate() {
            println!("{idx}: {object}");
        }
    }

    Ok(())
}
```

You can also [look at](https://github.com/hadrieng2/hwlocality/tree/master/examples)
more examples, if you want to run them check out the next section below.

## Running Examples

The library ships with examples, and to run them you need to clone the repository
and then run them through `cargo run --example=`.

```text
$ git clone https://github.com/hadrieng2/hwlocality.git
$ cd hwloc-rs
```

To run an example (which will download the dependencies and build it) you can
use `cargo run -example=`:

```text
$ cargo run --example=walk_tree
   Compiling hwlocality v1.0.0 (/home/hadrien/Bureau/Programmation/hwlocality)
    Finished dev [unoptimized + debuginfo] target(s) in 0.45s
     Running `target/debug/examples/walk_tree`
*** Printing overall tree
Machine: #0
 Package: #0
  L3 (20MB): #0
   L2 (256KB): #0
    L1d (32KB): #0
     Core: #0
      PU: #0
      PU: #10
   L2 (256KB): #1
    L1d (32KB): #1
     Core: #1
      PU: #1
      PU: #11
   L2 (256KB): #2
    L1d (32KB): #2
     Core: #2
      PU: #2
      PU: #12
   L2 (256KB): #3
    L1d (32KB): #3
     Core: #3
      PU: #3
      PU: #13
   L2 (256KB): #4
    L1d (32KB): #4
     Core: #4
      PU: #4
      PU: #14
   L2 (256KB): #5
    L1d (32KB): #5
     Core: #5
      PU: #5
      PU: #15
   L2 (256KB): #6
    L1d (32KB): #6
     Core: #6
      PU: #6
      PU: #16
   L2 (256KB): #7
    L1d (32KB): #7
     Core: #7
      PU: #7
      PU: #17
   L2 (256KB): #8
    L1d (32KB): #8
     Core: #8
      PU: #8
      PU: #18
   L2 (256KB): #9
    L1d (32KB): #9
     Core: #9
      PU: #9
      PU: #19
```

## hwloc API coverage

Most of the features from the hwloc 2.x series are now supported. But some
specialized features could not make it for various reasons. [Issues with the
"api coverage" label](https://github.com/HadrienG2/hwlocality/issues?q=is%3Aopen+is%3Aissue+label%3A%22api+coverage%22) keep track of unimplemented features, and are a great place to
look for potential contributions to this library if you have time!

If you are already familiar with the hwloc C API, you will also be happy to
know that [`#[doc(alias)]` attributes](https://doc.rust-lang.org/rustdoc/advanced-features.html#add-aliases-for-an-item-in-documentation-search)
are extensively used so that you can search the documentation for hwloc API
entities like "hwloc_bitmap_t" or "hwloc_set_cpubind" and be redirected to the
suggested replacement in the Rust API.

The rare exceptions to this rule are notions that are not needed due to
ergonomics improvements permitted by the Rust type system, such as manual
destructors (just let Drop take care of it) or argument-clarification flags like
`HWLOC_MEMBIND_BYNODESET` (just pass `NodeSet` or a `CpuSet` to the memory
binding operations and that flag will internally be set/cleared automatically).

## License

This project uses the MIT license, please see the
[LICENSE](https://github.com/hadrieng2/hwlocality/blob/master/LICENSE) file for
more information.
