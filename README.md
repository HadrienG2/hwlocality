# hwloc2-rs: Rust bindings for the hwloc library

[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
[![crates.io](http://meritbadge.herokuapp.com/hwloc2)](https://crates.io/crates/hwloc2)

This project is a successor to
[daschl/hwloc-rs](https://github.com/daschl/hwloc-rs), except that this library
supports 2.x.x versions of hwloc. This library tries to maintain most of the
API layer that [daschl/hwloc-rs](https://github.com/daschl/hwloc-rs) set forth.


[Hwloc](http://www.open-mpi.org/projects/hwloc) is a C library from Open MPI
for detecting the hierarchical topology of modern architectures. This includes
objects such as NUMA memory nodes, sockets, shared data & instruction caches,
cores, and simultaneous multi threading.

## Prerequisites

A system installed with hwloc >=2.2.0 and associated development packages installed.

Beware that some Linux distributions provide older hwloc versions. You may have
to install it from source.

You can download the source from <https://www.open-mpi.org/projects/hwloc/>.

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
hwloc2 = "2.2.0"
```

Here is a quick example which walks the `Topology` and prints it out:

```rust
use hwloc2::Topology;

fn main() {
	let topo = Topology::new().unwrap();

	for i in 0..topo.depth() {
		println!("*** Objects at level {}", i);

		for (idx, object) in topo.objects_at_depth(i.into()).enumerate() {
			println!("{}: {}", idx, object);
		}
	}
}
```

You can also [look at](https://github.com/ichbinjoe/hwloc2-rs/tree/master/examples)
more examples, if you want to run them check out the next section below.

## Running Examples
The library ships with examples, and to run them you need to clone the repository
and then run them through `cargo run --example=`.

```text
$ git clone https://github.com/ichbinjoe/hwloc2-rs.git
$ cd hwloc-rs
```

To run an example (which will download the dependencies and build it) you can
use `cargo run -example=`:

```text
$ cargo run --example=walk_tree
   Compiling hwloc2 v2.2.0 (/home/hadrien/Bureau/Programmation/hwloc2-rs)
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

## License
This project uses the MIT license, please see the
[LICENSE](https://github.com/ichbinjoe/hwloc2-rs/blob/master/LICENSE) file for
more information.
