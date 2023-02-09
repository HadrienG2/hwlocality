use hwloc2::{
    objects::{attributes::ObjectAttributes, types::ObjectType},
    Topology,
};

/// Compute the amount of cache that the first logical processor
/// has above it.
fn main() {
    let topo = Topology::new().unwrap();

    let pu = topo.objects_with_type(ObjectType::PU).next().unwrap();

    let mut parent = pu.parent();
    let mut levels = 0;
    let mut size = 0;

    while let Some(p) = parent {
        if let Some(ObjectAttributes::Cache(c)) = p.attributes() {
            levels += 1;
            size += c.size();
        }
        parent = p.parent();
    }

    println!(
        "*** Logical processor 0 has {} caches totalling {} KB",
        levels,
        size / 1024
    );
}
