use hwloc2::Topology;

/// Walk the topology with an array style, from level 0 (always
/// the system level) to the lowest level (always the proc level).
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    for i in 0..topology.depth() {
        println!("*** Objects at level {}", i);

        for (idx, object) in topology.objects_at_depth(i).enumerate() {
            println!("{}: {}", idx, object);
        }
    }

    Ok(())
}
