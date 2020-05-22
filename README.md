# hwloc2-rs
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

A system installed with hwloc 2.2.0.

Please note, this is _not_ the default version installed by package managers of
many mainstream distributions right now. You will probably have to install it
from source:

You can download the source from https://www.open-mpi.org/projects/hwloc/

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
hwloc2 = "2.2.0"
```

Next, add this to your crate root:

```rust
extern crate hwloc2;
```

Here is a quick example which walks the `Topology` and prints it out:

```rust
extern crate hwloc2;

use hwloc2::Topology;

fn main() {
	let topo = Topology::new().unwrap();

	for i in 0..topo.depth() {
		println!("*** Objects at level {}", i);

		for (idx, object) in topo.objects_at_depth(i).iter().enumerate() {
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

```
$ git clone https://github.com/ichbinjoe/hwloc2-rs.git
$ cd hwloc-rs
```

To run an example (which will download the dependencies and build it) you can
use `cargo run -example=`:

```
$ cargo run --example=walk_tree
   Compiling hwloc v2.2.0 (/directory/hwloc2-rs)
    Finished dev [unoptimized + debuginfo] target(s) in 0.54s
     Running `target/debug/examples/walk_tree`
*** Printing overall tree
Machine (): #0
 Package (): #0
  L3 (8192KB): #4294967295
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #0
      PU (): #0
      PU (): #8
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #1
      PU (): #1
      PU (): #9
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #2
      PU (): #2
      PU (): #10
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #3
      PU (): #3
      PU (): #11
  L3 (8192KB): #4294967295
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #4
      PU (): #4
      PU (): #12
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #5
      PU (): #5
      PU (): #13
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #6
      PU (): #6
      PU (): #14
   L2 (512KB): #4294967295
    L1d (32KB): #4294967295
     Core (): #7
      PU (): #7
      PU (): #15
```

## License
This project uses the MIT license, please see the
[LICENSE](https://github.com/ichbinjoe/hwloc2-rs/blob/master/LICENSE) file for
more information.
