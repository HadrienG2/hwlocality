#[cfg(feature = "bundled")]
use std::env;
#[cfg(feature = "bundled")]
use std::path::Path;
#[cfg(feature = "bundled")]
use std::path::PathBuf;
#[cfg(feature = "bundled")]
use std::process::Command;

#[cfg(feature = "bundled")]
fn fetch_hwloc(path: &Path, version: &str) {
    if !path.join("hwloc").join("Makefile.am").exists() {
        let r = Command::new("git")
            .args(&[
                "clone",
                "https://github.com/open-mpi/hwloc",
                "--depth",
                "1",
                "--branch",
                version,
            ])
            .current_dir(path.clone())
            .output();
        let m = r.expect("Failed to run git clone");
        assert!(
            m.status.success(),
            "git clone for hwloc returned failure code {}\n{:?}",
            m.status,
            m
        );
    }
}

#[cfg(feature = "bundled")]
fn compile_hwloc_autotools(p: PathBuf) -> PathBuf {
    let mut config = autotools::Config::new(p);
    config.reconf("-ivf").make_target("install").build()
}

#[cfg(feature = "bundled")]
fn compile_hwloc_cmake(build_path: &Path) -> PathBuf {
    let mut cfg = cmake::Config::new(build_path);
    if let Ok(profile) = env::var("HWLOC_BUILD_PROFILE") {
        cfg.profile(&profile);
    } else {
        cfg.profile("release");
    }

    // Allow specifying custom toolchain specifically for hwloc.
    if let Ok(toolchain) = env::var("HWLOC_TOOLCHAIN") {
        cfg.define("CMAKE_TOOLCHAIN_FILE", &toolchain);
    }
    cfg.build()
}

fn use_pkgconfig(required_version: &str, first_unsupported_version: &str) -> pkg_config::Library {
    let lib = pkg_config::Config::new()
        .range_version(required_version..first_unsupported_version)
        .statik(true)
        .probe("hwloc")
        .expect("Could not find a suitable version of hwloc");
    if cfg!(target_family = "unix") {
        for link_path in &lib.link_paths {
            println!(
                "cargo:rustc-link-arg=-Wl,-rpath,{}",
                link_path
                    .to_str()
                    .expect("Link path is not an UTF-8 string")
            );
        }
    }
    lib
}

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
    #[cfg(feature = "bundled")]
    {
		let git_dir = env::var("OUT_DIR").expect("No output directory given");
        let (source_version, first_unsupported_version) = match required_version
			.split('.')
			.next()
			.expect("No major version in required_version")
		{
			"2" => ("v2.x", "3.0.0"),
			other => panic!("Please add support for bundling hwloc v{other}.x"),
		};
        let mut hwloc_source_path = PathBuf::from(git_dir);
        fetch_hwloc(hwloc_source_path.as_path(), source_version);
        hwloc_source_path.push("hwloc");
        let cmake = cfg!(target_os = "windows")
            && hwloc_source_path
                .join("contrib")
                .join("windows-cmake")
                .join("CMakeLists.txt")
                .exists();
        let hwloc_compiled_path: PathBuf = if cmake {
            hwloc_source_path.push("contrib");
            hwloc_source_path.push("windows-cmake");
            compile_hwloc_cmake(hwloc_source_path.as_path())
        } else {
            compile_hwloc_autotools(hwloc_source_path)
        };

        #[cfg(target_os = "windows")]
        {
            println!("cargo:rustc-link-lib=static=hwloc");
            println!(
                "cargo:rustc-link-search={}",
                hwloc_compiled_path.join("lib").display()
            );
        }
        #[cfg(not(target_os = "windows"))]
        {
            env::set_var(
                "PKG_CONFIG_PATH",
                format!(
                    "{}",
                    hwloc_compiled_path.join("lib").join("pkgconfig").display()
                ),
            );
            use_pkgconfig(required_version, first_unsupported_version);
        }
    }
    #[cfg(not(feature = "bundled"))]
    {
		let first_unsupported_version = match required_version
			.split('.')
			.next()
			.expect("No major version in required_version")
		{
			"2" => "3.0.0",
			other => panic!("Please add support for hwloc v{other}.x"),
		};
        use_pkgconfig(required_version, first_unsupported_version);
    }
}
