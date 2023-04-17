fn main() {
    let required_version = if cfg!(feature = "hwloc-2_8_0") {
        "2.8.0"
    } else if cfg!(feature = "hwloc-2_5_0") {
        "2.5.0"
    } else if cfg!(feature = "hwloc-2_4_0") {
        "2.4.0"
    } else if cfg!(feature = "hwloc-2_3_0") {
        "2.3.0"
    } else if cfg!(feature = "hwloc-2_2_0") {
        "2.2.0"
    } else if cfg!(feature = "hwloc-2_1_0") {
        "2.1.0"
    } else if cfg!(feature = "hwloc-2_0_4") {
        "2.0.4"
    } else {
        "2.0.0"
    };
    pkg_config::Config::new()
        .atleast_version(required_version)
        .probe("hwloc")
        .unwrap();
}
