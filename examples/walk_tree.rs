use anyhow::Context;
use hwloc2::{objects::TopologyObject, Topology};

/// Walk the topology in a tree-style and print it.
fn main() -> anyhow::Result<()> {
    let topo = Topology::new()?;

    println!("*** Printing overall tree");
    print_children(topo.root_object(), 0)?;

    Ok(())
}

fn print_children(obj: &TopologyObject, depth: usize) -> anyhow::Result<()> {
    for _ in 0..depth {
        print!(" ");
    }
    println!(
        "{obj}: #{:?}",
        obj.os_index()
            .context("Objects in the normal hierarchy should have an OS index")?
    );

    for child in obj.normal_children() {
        print_children(child, depth + 1)?;
    }

    Ok(())
}
