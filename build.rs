use std::env;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

#[cfg(feature = "bundled")]
fn fetch_hwloc(path: &Path, version: &str) {
    if !path.join("Makefile.am").exists() {
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
fn compile_hwloc2() -> PathBuf {
    let mut config = autotools::Config::new("hwloc");
    config.reconf("-ivf").make_target("install").build()
}

fn main() {
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
        let hwloc2_source_path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        fetch_hwloc(hwloc2_source_path.as_path(), source_version);
        let mut hwloc2_compiled_path: PathBuf = compile_hwloc2();
        hwloc2_compiled_path.push("lib");
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            hwloc2_compiled_path
                .to_str()
                .expect("Link path is not an UTF-8 string")
        );
        println!(
            "cargo:rustc-link-search={}",
            hwloc2_compiled_path
                .to_str()
                .expect("Link path is not an UTF-8 string")
        );
        println!("cargo:rustc-link-lib=static=hwloc");
        println!("cargo:rustc-link-lib=xml2");
        println!("cargo:rustc-link-lib=pciaccess");
        println!("cargo:rustc-link-lib=udev");
        println!(
            "cargo:rerun-if-changed={}",
            hwloc2_source_path.to_str().expect("Invalid source path")
        );
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
