use hwlocality::{
    object::{depth::TypeToDepthError, types::ObjectType},
    Topology,
};

/// Prints the number of packages.
fn main() -> eyre::Result<()> {
    let topology = Topology::new()?;

    match topology.depth_for_type(ObjectType::Package) {
        Ok(depth) => println!(
            "*** Found {} package(s) at depth {depth}",
            topology.num_objects_at_depth(depth)
        ),
        Err(TypeToDepthError::Nonexistent) => println!("*** No package object found"),
        Err(TypeToDepthError::Multiple) => println!("*** Package objects exist at multiple depths"),
    }

    Ok(())
}
