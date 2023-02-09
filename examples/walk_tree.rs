use hwloc2::{objects::TopologyObject, Topology};

/// Walk the topology in a tree-style and print it.
fn main() {
    let topo = Topology::new().unwrap();

    println!("*** Printing overall tree");
    print_children(&topo, topo.root_object(), 0);
}

fn print_children(topo: &Topology, obj: &TopologyObject, depth: usize) {
    let padding = std::iter::repeat(" ").take(depth).collect::<String>();
    println!("{padding}{obj}: #{:?}", obj.os_index());

    for child in obj.normal_children() {
        print_children(topo, child, depth + 1);
    }
}
