use hwloc2::{objects::TopologyObject, Topology};

/// Walk the topology in a tree-style and print it.
fn main() {
    let topo = Topology::new().unwrap();

    println!("*** Printing overall tree");
    print_children(topo.root_object(), 0);
}

fn print_children(obj: &TopologyObject, depth: usize) {
    for _ in 0..depth {
        print!(" ");
    }
    println!("{obj}: #{:?}", obj.os_index().unwrap());

    for child in obj.normal_children() {
        print_children(child, depth + 1);
    }
}
