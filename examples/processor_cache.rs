use anyhow::Context;
use hwlocality::{
    object::{attributes::ObjectAttributes, types::ObjectType},
    Topology,
};

/// Compute the amount of cache that the first logical processor
/// has above it.
fn main() -> anyhow::Result<()> {
    let topology = Topology::new()?;

    // Walk caches on an individual PU
    let first_pu = topology
        .objects_with_type(ObjectType::PU)
        .next()
        .context("At least one PU should be present")?;
    let (levels, size) = first_pu
        .ancestors()
        .filter_map(|ancestor| {
            if let Some(ObjectAttributes::Cache(cache)) = ancestor.attributes() {
                Some(cache.size().expect("Failed to probe cache size"))
            } else {
                None
            }
        })
        .fold((0, 0), |(levels, total_size), level_size| {
            (levels + 1, total_size + level_size)
        });
    println!(
        "*** Logical processor 0 is covered by {levels} caches totalling {} KiB",
        size / 1024
    );

    // Compute aggregate statistics on all available CPU caches
    let stats = topology
        .cpu_cache_stats()
        .context("CPU cache state unavailable")?;
    println!(
        "*** System-wide minimal data cache sizes per level: {:?}",
        stats.smallest_data_cache_sizes()
    );
    println!(
        "*** System-wide total data cache size per level: {:?}",
        stats.total_data_cache_sizes()
    );

    Ok(())
}
