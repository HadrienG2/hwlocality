//! CPU cache statistics

use crate::{
    objects::{attributes::ObjectAttributes, types::ObjectType},
    Topology,
};
use arrayvec::ArrayVec;

/// Data (or unified) caches levels supported by hwloc
const DATA_CACHE_LEVELS: &[ObjectType] = &[
    ObjectType::L1Cache,
    ObjectType::L2Cache,
    ObjectType::L3Cache,
    ObjectType::L4Cache,
    ObjectType::L5Cache,
];

/// CPU cache statistics
///
/// These statistics can be used in scenarios where you're not yet ready for
/// full locality-aware scheduling but just want to make sure that your code
/// will use CPU caches sensibly no matter which CPU core it's running on.
pub struct CPUCacheStats {
    /// Size of the smallest caches of each type
    smallest_data_cache_sizes: ArrayVec<u64, { DATA_CACHE_LEVELS.len() }>,

    /// Sum of the sizes of the caches of each type
    total_data_cache_sizes: ArrayVec<u64, { DATA_CACHE_LEVELS.len() }>,
}

impl CPUCacheStats {
    /// Compute CPU cache statistics
    pub fn new(topology: &Topology) -> Self {
        let mut smallest_data_cache_sizes = ArrayVec::new();
        let mut total_data_cache_sizes = ArrayVec::new();
        for &data_cache_level in DATA_CACHE_LEVELS {
            // Compute cache capacity stats for this cache level
            let mut smallest = u64::MAX;
            let mut total = 0;
            let mut found = false;
            for object in topology.objects_at_depth(
                topology
                    .depth_for_type(data_cache_level)
                    .expect("Data caches should only appear at one depth"),
            ) {
                let Some(ObjectAttributes::Cache(cache)) = object.attributes() else {
                    unreachable!("Caches should have cache attributes")
                };
                found = true;
                smallest = smallest.min(cache.size());
                total += cache.size();
            }

            // If at least one cache was found, record stats, otherwise abort:
            // If we didn't find cache level N, we won't find level N+1.
            if found {
                smallest_data_cache_sizes.push(smallest);
                total_data_cache_sizes.push(total);
            } else {
                break;
            }
        }
        Self {
            smallest_data_cache_sizes,
            total_data_cache_sizes,
        }
    }

    /// Smallest CPU data cache capacity at each cache level
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the minimal
    /// cache capacity at each level.
    ///
    /// You should tune sequential algorithms such that they fit in the first
    /// cache level, if not possible in the second cache level, and so on.
    pub fn smallest_data_cache_sizes(&self) -> &[u64] {
        &self.smallest_data_cache_sizes[..]
    }

    /// Total CPU data cache capacity at each cache level
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the total cache capacity at each
    /// level.
    ///
    /// You should tune parallel algorithms such that the total working set
    /// (summed across all threads) fits into the first cache level, if not
    /// possible in the second cache level, and so on.
    ///
    /// Beware that this is only a minimal requirement for cache locality, and
    /// programs honoring this criterion might still not achieve good cache
    /// performance due to CPU core heterogeneity or Non-Uniform Cache Access
    /// (NUCA) effects. To correctly handle these, you need to move to a fully
    /// locality-aware design with threads pinned to CPU cores and tree-like
    /// synchronization following the shape of the topology tree.
    ///
    /// That being said, you may manage to reduce NUCA effects at the cost of
    /// using a smaller fraction of your CPU cache capacity by making your
    /// parallel algorithm collectively fit into the smallest last-level cache.
    pub fn total_data_cache_sizes(&self) -> &[u64] {
        &self.total_data_cache_sizes[..]
    }
}
