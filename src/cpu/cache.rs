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
use similar_asserts::assert_eq;

/// # CPU cache statistics
impl Topology {
    /// Compute CPU cache statistics, if cache sizes are known
    ///
    /// Returns None if cache size information is unavailable for at least some
    /// of the CPU caches on the system.
    ///
    /// These statistics can be used to perform simple cache locality
    /// optimizations when your performance requirements do not call for full
    /// locality-aware scheduling with careful task and memory pinning.
    ///
    /// This functionality is an hwlocality-specific extension to the hwloc API.
    ///
    /// # Examples
    ///
    /// ```
    /// # let topology = hwlocality::Topology::test_instance();
    /// #
    /// use eyre::eyre;
    ///
    /// let stats = topology
    ///     .cpu_cache_stats()
    ///     .ok_or_else(|| eyre!("CPU cache sizes are not known"))?;
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
    /// #
    /// # Ok::<(), eyre::Report>(())
    /// ```
    pub fn cpu_cache_stats(&self) -> Option<CpuCacheStats> {
        CpuCacheStats::new(self)
    }
}

/// CPU cache statistics
///
/// These statistics can be used to perform simple cache locality optimizations
/// when your performance requirements do not call for full locality-aware
/// scheduling with manual task and memory pinning.
//
// --- Implementation notes ---
//
// Not implementing Copy to leave room for future growth in case people really
// insist that I use a Vec instead of an ArrayVec someday.
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
    /// Compute CPU cache statistics, if cache sizes are known
    ///
    /// Returns None if cache size information is unavailable for at least some
    /// of the CPU caches on the system.
    pub fn new(topology: &Topology) -> Option<Self> {
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
                let cache_size = cache.size()?.get();
                let per_thread_size = cache_size / num_threads;
                smallest = smallest.min(cache_size);
                smallest_per_thread = smallest_per_thread.min(per_thread_size);
                total += cache_size;
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

        // Absence of L1 caches is not possible on current hardware, it
        // is just interpreted as cache info being unavailable overall
        (!smallest_data_cache_sizes.is_empty()).then_some(Self {
            smallest_data_cache_sizes,
            smallest_data_cache_sizes_per_thread,
            total_data_cache_sizes,
        })
    }

    /// Smallest CPU data cache capacity at each cache level
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the minimal
    /// cache capacity at each level.
    ///
    /// You should tune sequential algorithms such that they fit this effective
    /// cache hierarchy (first layer of loop blocking has a working set that can
    /// stay in the first reported cache capacity, second layer of loop blocking
    /// has a working set that can fit in the second reported capacity, etc.)
    pub fn smallest_data_cache_sizes(&self) -> &[u64] {
        &self.smallest_data_cache_sizes[..]
    }

    /// Smallest CPU data cache capacity at each cache level, per thread
    ///
    /// This tells you how many cache levels there are in the deepest cache
    /// hierarchy on this system, and what is the minimal cache capacity _per
    /// thread sharing a cache_ at each level.
    ///
    /// In parallel algorithms where all CPU threads are potentially used, and
    /// threads effectively share no common data, you should tune the private
    /// working set of each thread such that it fits this effective cache
    /// hierarchy (first layer of loop blocking has a working set that can stay
    /// in the first reported cache capacity, second layer of loop blocking has
    /// a working set that can fit in the second reported capacity, etc.).
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

/// Data (or unified) caches levels supported by hwloc
const DATA_CACHE_LEVELS: &[ObjectType] = &[
    ObjectType::L1Cache,
    ObjectType::L2Cache,
    ObjectType::L3Cache,
    ObjectType::L4Cache,
    ObjectType::L5Cache,
];

#[cfg(test)]
mod tests {
    use super::*;
    use similar_asserts::assert_eq;

    #[test]
    fn stats() {
        let topology = Topology::test_instance();
        let stats = topology.cpu_cache_stats();

        if let Some(stats) = stats {
            // All stats should cover the same number of cache levels
            let num_cache_levels = stats.smallest_data_cache_sizes().len();
            assert_eq!(
                num_cache_levels,
                stats.smallest_data_cache_sizes_per_thread().len()
            );
            assert_eq!(num_cache_levels, stats.total_data_cache_sizes().len());

            // Number of cache levels shouldn't exceed hwloc's ability
            assert!(num_cache_levels <= DATA_CACHE_LEVELS.len());

            // Now let's look at individual cache levels
            for (idx, cache_level) in DATA_CACHE_LEVELS.iter().copied().enumerate() {
                // Should only report nothing for levels with no known cache
                if idx >= num_cache_levels {
                    assert_eq!(topology.objects_with_type(cache_level).count(), 0);
                    continue;
                }

                // Stats should be accurate
                let cache_sizes_and_arities = topology.objects_with_type(cache_level).map(|obj| {
                    let arity = obj.cpuset().unwrap().weight().unwrap();
                    let Some(ObjectAttributes::Cache(cache)) = obj.attributes() else {
                        unreachable!()
                    };
                    (cache.size().unwrap().get(), arity)
                });
                assert_eq!(
                    stats.smallest_data_cache_sizes()[idx],
                    cache_sizes_and_arities
                        .clone()
                        .map(|(size, _)| size)
                        .min()
                        .unwrap()
                );
                assert_eq!(
                    stats.smallest_data_cache_sizes_per_thread()[idx],
                    cache_sizes_and_arities
                        .clone()
                        .map(|(size, arity)| size / arity as u64)
                        .min()
                        .unwrap()
                );
                assert_eq!(
                    stats.total_data_cache_sizes()[idx],
                    cache_sizes_and_arities
                        .clone()
                        .map(|(size, _)| size)
                        .sum::<u64>()
                );
            }
        } else {
            // Cache stats queries should only fail if hwloc failed to probe CPU
            // cache properties, overall or cache size specifically.
            if topology.objects_with_type(ObjectType::L1Cache).count() == 0 {
                return;
            }
            for &cache_level in DATA_CACHE_LEVELS {
                for obj in topology.objects_with_type(cache_level) {
                    let Some(ObjectAttributes::Cache(cache)) = obj.attributes() else {
                        unreachable!()
                    };
                    if cache.size().is_none() {
                        return;
                    }
                }
            }
            panic!("Cache stats query should not have failed");
        }
    }
}
