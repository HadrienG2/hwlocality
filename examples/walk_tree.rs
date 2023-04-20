use hwlocality::{objects::TopologyObject, Topology};

/// Walk the topologylogy in a tree-style and print it.
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    println!("*** Printing overall tree");
    print_children(topology.root_object(), 0)?;

    Ok(())
}

fn print_children(obj: &TopologyObject, depth: usize) -> anyhow::Result<()> {
    for _ in 0..depth {
        print!(" ");
    }
    println!("{obj}: #{:?}", obj.os_index());

    for child in obj.normal_children() {
        print_children(child, depth + 1)?;
    }

    Ok(())
}
