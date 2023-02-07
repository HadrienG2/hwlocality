extern crate hwloc2;

use hwloc2::{Topology, TopologyObject};

/// Walk the topology in a tree-style and print it.
fn main() {
    let topo = Topology::new().unwrap();

    println!("*** Printing overall tree");
    print_children(&topo, topo.object_at_root(), 0);
}

fn print_children(topo: &Topology, obj: &TopologyObject, depth: usize) {
    let padding = std::iter::repeat(" ").take(depth).collect::<String>();
    println!("{}{}: #{}", padding, obj, obj.os_index());

    for child in obj.children() {
        print_children(topo, child, depth + 1);
    }
}
