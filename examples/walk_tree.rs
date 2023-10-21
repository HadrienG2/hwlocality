use hwlocality::{object::TopologyObject, Topology};

/// Walk the topologylogy in a tree-style and print it.
fn main() -> eyre::Result<()> {
    let topology = Topology::new()?;

    println!("*** Topology tree");
    print_children(topology.root_object(), 0)?;

    Ok(())
}

fn print_children(obj: &TopologyObject, depth: usize) -> eyre::Result<()> {
    for _ in 0..depth {
        print!(" ");
    }
    print!("{obj}");
    if let Some(os_idx) = obj.os_index() {
        print!(" #{os_idx}");
    }
    println!();

    for child in obj.normal_children() {
        print_children(child, depth + 1)?;
    }

    Ok(())
}
