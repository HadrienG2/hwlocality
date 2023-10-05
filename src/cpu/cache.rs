//! CPU cache statistics
//!
//! These statistics, which can be queried via
//! the [`Topology::cpu_cache_stats()`] method, can be used to perform simple
//! cache locality optimizations when your performance requirements do not call
//! for full locality-aware scheduling with manual task and memory pinning.
//!
//! This functionality is an hwlocality-specific extension to the hwloc API.

use crate::{
    object::{attributes::ObjectAttributes, types::ObjectType},
    topology::Topology,
};
use arrayvec::ArrayVec;
#[allow(unused)]
#[cfg(test)]
use pretty_assertions::{assert_eq, assert_ne};

/// # CPU cache statistics
impl Topology {
    /// Compute CPU cache statistics
    ///
    /// These statistics can be used to perform simple cache locality
    /// optimizations when your performance requirements do not call for full
    /// locality-aware scheduling with manual task and memory pinning.
    ///
    /// This functionality is an hwlocality-specific extension to the hwloc API.
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// let stats = topology.cpu_cache_stats();
    ///
    /// println!(
    ///     "Minimal data cache sizes: {:?}",
    ///     stats.smallest_data_cache_sizes()
    /// );
    /// println!(
    ///     "Minimal data cache sizes per thread: {:?}",
    ///     stats.smallest_data_cache_sizes_per_thread()
    /// );
    /// println!(
    ///     "Total data cache sizes: {:?}",
    ///     stats.total_data_cache_sizes()
    /// );
    ///
    /// assert_eq!(stats.smallest_data_cache_sizes().len(),
    ///            stats.smallest_data_cache_sizes_per_thread().len());
    /// assert_eq!(stats.smallest_data_cache_sizes().len(),
    ///            stats.total_data_cache_sizes().len());
    /// for ((smallest, smallest_per_thread), total) in
    ///     stats.smallest_data_cache_sizes().iter()
    ///         .zip(stats.smallest_data_cache_sizes_per_thread())
    ///         .zip(stats.total_data_cache_sizes())
    /// {
    ///     assert!(smallest_per_thread <= smallest);
    ///     assert!(smallest <= total);
    /// }
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn cpu_cache_stats(&self) -> CpuCacheStats {
        CpuCacheStats::new(self)
    }
}

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
/// These statistics can be used to perform simple cache locality optimizations
/// when your performance requirements do not call for full locality-aware
/// scheduling with manual task and memory pinning.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CpuCacheStats {
    /// Size of the smallest caches of each type
    smallest_data_cache_sizes: ArrayVec<u64, { DATA_CACHE_LEVELS.len() }>,

    /// Size per thread of the smallest caches of each type
    smallest_data_cache_sizes_per_thread: ArrayVec<u64, { DATA_CACHE_LEVELS.len() }>,

    /// Sum of the sizes of the caches of each type
    total_data_cache_sizes: ArrayVec<u64, { DATA_CACHE_LEVELS.len() }>,
}

impl CpuCacheStats {
    /// Compute CPU cache statistics
    pub fn new(topology: &Topology) -> Self {
        let mut smallest_data_cache_sizes = ArrayVec::new();
        let mut smallest_data_cache_sizes_per_thread = ArrayVec::new();
        let mut total_data_cache_sizes = ArrayVec::new();
        for &data_cache_level in DATA_CACHE_LEVELS {
            // Compute cache capacity stats for this cache level
            let mut smallest = u64::MAX;
            let mut smallest_per_thread = u64::MAX;
            let mut total = 0;
            let mut found = false;
            for object in topology.objects_with_type(data_cache_level) {
                let Some(ObjectAttributes::Cache(cache)) = object.attributes() else {
                    unreachable!("Caches should have cache attributes")
                };
                found = true;
                let num_threads = object
                    .cpuset()
                    .and_then(|set| set.weight())
                    .expect("Caches should have cpusets") as u64;
                let per_thread_size = cache.size() / num_threads;
                smallest = smallest.min(cache.size());
                smallest_per_thread = smallest_per_thread.min(per_thread_size);
                total += cache.size();
            }

            // If at least one cache was found, record stats, otherwise abort:
            // If we didn't find cache level N, we won't find level N+1.
            if found {
                smallest_data_cache_sizes.push(smallest);
                smallest_data_cache_sizes_per_thread.push(smallest_per_thread);
                total_data_cache_sizes.push(total);
            } else {
                break;
            }
        }
        Self {
            smallest_data_cache_sizes,
            smallest_data_cache_sizes_per_thread,
            total_data_cache_sizes,
        }
    }

    /// Smallest CPU data cache capacity at each cache level
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the minimal
    /// cache capacity at each level.
    ///
    /// You should tune sequential algorithms such that their working set is
    /// smaller than the first reported cache capacity, if not such that it is
    /// smaller than the second reported cache capacity, and so on.
    pub fn smallest_data_cache_sizes(&self) -> &[u64] {
        &self.smallest_data_cache_sizes[..]
    }

    /// Smallest CPU data cache capacity at each cache level, per thread
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the minimal
    /// cache capacity at each level, divided by the number of threads sharing
    /// that cache.
    ///
    /// In parallel algorithms where the fact that threads share cache cannot be
    /// leveraged, you should tune the sequential tasks processed by each
    /// thread such that they fit in the reported cache capacities.
    pub fn smallest_data_cache_sizes_per_thread(&self) -> &[u64] {
        &self.smallest_data_cache_sizes_per_thread[..]
    }

    /// Total CPU data cache capacity at each cache level
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the total cache capacity at each
    /// level.
    ///
    /// You should tune parallel algorithms such that the total working set
    /// (summed across all threads without double-counting shared resources)
    /// fits in the reported aggregated cache capacities.
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
