use hwlocality::{object::depth::NormalDepth, Topology};

/// Walk the topology with an array style, from depth 0 (always Machine)
/// to the lowest depth (always logical processors).
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    for depth in NormalDepth::iter_range(NormalDepth::MIN, topology.depth()) {
        println!("*** Objects at depth {depth}");

        for (idx, object) in topology.objects_at_depth(depth).enumerate() {
            println!("{idx}: {object}");
        }
    }

    Ok(())
}
