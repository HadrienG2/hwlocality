use hwloc2::{depth::DepthError, objects::types::ObjectType, Topology};

/// Prints the number of packages.
fn main() -> anyhow::Result<()> {
    let topo = Topology::new()?;

    match topo.depth_for_type(ObjectType::Package) {
        Ok(depth) => println!("*** {} package(s)", topo.size_at_depth(depth)),
        Err(DepthError::None) => println!("*** No package object"),
        Err(DepthError::Multiple) => println!("*** Package objects exist at multiple depths"),
        Err(DepthError::Unknown(i)) => println!("*** Unknown error while probing packages: {i}"),
    }

    Ok(())
}
