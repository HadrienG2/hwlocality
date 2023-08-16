use std::env;
use std::path::Path;
use std::path::PathBuf;
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
        match r {
            Ok(m) => {
                if !m.status.success() {
                    eprintln!("git clone for hwloc returned {}", m.status);
                    eprintln!("{:?}", m);
                }
            }
            Err(e) => eprintln!("Error cloning hwloc {}", e),
        }
    }
}

#[cfg(feature = "bundled")]
fn get_os_from_triple(triple: &str) -> Option<&str> {
    triple.splitn(3, "-").nth(2)
}

#[cfg(feature = "bundled")]
fn compile_hwloc2_autotools(p: PathBuf) -> PathBuf {
    println!("dummy: path is {}", p.display());
    let mut config = autotools::Config::new(p);
    config.reconf("-ivf").make_target("install").build()
}

fn compile_hwloc2_cmake(build_path: &Path, target_os: &str) -> PathBuf {
    let mut cfg = cmake::Config::new(build_path);
    if let Ok(profile) = env::var("HWLOC_BUILD_PROFILE") {
        cfg.profile(&profile);
    } else {
        cfg.profile("release");
    }

    // Allow specifying custom toolchain specifically for SDL2.
    if let Ok(toolchain) = env::var("HWLOC_TOOLCHAIN") {
        cfg.define("CMAKE_TOOLCHAIN_FILE", &toolchain);
    } else {
        // Override __FLTUSED__ to keep the _fltused symbol from getting defined in the static build.
        // This conflicts and fails to link properly when building statically on Windows, likely due to
        // COMDAT conflicts/breakage happening somewhere.
        #[cfg(feature = "static-link")]
        cfg.cflag("-D__FLTUSED__");

        #[cfg(target_os = "linux")]
        {
            // Add common flag for affected version and above
            use version_compare::{compare_to, Cmp};
            if let Ok(version) = std::process::Command::new("cc")
                .arg("-dumpversion")
                .output()
            {
                let affected =
                    compare_to(std::str::from_utf8(&version.stdout).unwrap(), "10", Cmp::Ge)
                        .unwrap_or(true);
                if affected {
                    cfg.cflag("-fcommon");
                }
            }
        }
    }
    cfg.build()
}

fn main() {
    let git_dir = env::var("OUT_DIR").expect("No output directory given");
    let (required_version, source_version) = if cfg!(feature = "hwloc-2_8_0") {
        ("2.8.0", "v2.8")
    } else if cfg!(feature = "hwloc-2_5_0") {
        ("2.5.0", "v2.5")
    } else if cfg!(feature = "hwloc-2_4_0") {
        ("2.4.0", "v2.4")
    } else if cfg!(feature = "hwloc-2_3_0") {
        ("2.3.0", "v2.3")
    } else if cfg!(feature = "hwloc-2_2_0") {
        ("2.2.0", "v2.2")
    } else if cfg!(feature = "hwloc-2_1_0") {
        ("2.1.0", "v2.1")
    } else if cfg!(feature = "hwloc-2_0_4") {
        ("2.0.4", "v2.x")
    } else {
        ("2.0.0", "v2.0")
    };
    #[cfg(feature = "bundled")]
    {
        let mut hwloc2_source_path = PathBuf::from(git_dir);
        fetch_hwloc(hwloc2_source_path.as_path(), source_version);
        hwloc2_source_path.push("hwloc");
        let mut hwloc2_compiled_path: PathBuf = if hwloc2_source_path.join("contrib").join("windows-cmake").join("CMakeLists.txt").exists() {
            let target = env::var("TARGET").expect("Cargo build scripts always have TARGET");
            let target_os = get_os_from_triple(target.as_str()).unwrap();
            hwloc2_source_path.push("contrib");
            hwloc2_source_path.push("windows-cmake");
            compile_hwloc2_cmake(hwloc2_source_path.as_path(), target_os)
        }
        else {
            compile_hwloc2_autotools(hwloc2_source_path)
        };

        //#[cfg(target_os = "windows")]
        //std::fs::copy(hwloc2_compiled_path.join("lib").join("hwloc.lib").as_path(), hwloc2_compiled_path.join("lib").join("libhwloc.lib").as_path());

        #[cfg(target_os = "windows")]
        {
            println!("cargo:rustc-link-lib=static=hwloc");
            println!("cargo:rustc-link-search={}", hwloc2_compiled_path.join("lib").display());
        }
        #[cfg(not(target_os = "windows"))]
        {
            env::set_var("PKG_CONFIG_PATH", format!("{}", hwloc2_compiled_path.join("lib").join("pkgconfig").display()));
            let lib = pkg_config::Config::new()
                .atleast_version(required_version)
                .statik(true)
                .probe("hwloc")
                .expect("Could not find a suitable version of hwloc");
        }
    }
    #[cfg(not(feature = "bundled"))]
    {
        let lib = pkg_config::Config::new()
            .atleast_version(required_version)
            .statik(true)
            .probe("hwloc")
            .expect("Could not find a suitable version of hwloc");
        if cfg!(target_family = "unix") {
            for link_path in lib.link_paths {
                println!(
                    "cargo:rustc-link-arg=-Wl,-rpath,{}",
                    link_path
                        .to_str()
                        .expect("Link path is not an UTF-8 string")
                );
            }
        }
    }
}
