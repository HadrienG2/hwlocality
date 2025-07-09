use std::sync::OnceLock;
#[cfg(feature = "vendored")]
mod vendored_deps {
    pub use flate2::read::GzDecoder;
    pub use sha3::{Digest, Sha3_256};
    pub use std::{
        env,
        path::{Path, PathBuf},
    };
    pub use tar::Archive;
}
#[cfg(feature = "vendored")]
use vendored_deps::*;

fn main() {
    // We don't need hwloc on docs.rs since it only builds the docs
    if std::env::var("DOCS_RS").is_err() {
        setup_hwloc();
    }
}

/// Configure the hwloc dependency
fn setup_hwloc() {
    // Determine the minimal supported hwloc version with current features
    let required_version = if cfg!(feature = "hwloc-2_11_0") {
        "2.11.0"
    } else if cfg!(feature = "hwloc-2_10_0") {
        "2.10.0"
    } else if cfg!(feature = "hwloc-2_8_0") {
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

    // If asked to build hwloc ourselves, do so
    #[cfg(feature = "vendored")]
    setup_vendored_hwloc(required_version);

    // If asked to use system hwloc, configure it using pkg-config
    #[cfg(not(feature = "vendored"))]
    find_hwloc(Some(required_version));
}

/// Use pkg-config to locate and use a certain hwloc release
fn find_hwloc(required_version: Option<&str>) -> pkg_config::Library {
    // Initialize pkg-config
    let mut config = pkg_config::Config::new();

    // Specify the required version range if instructed to do so
    if let Some(required_version) = required_version {
        let first_unsupported_version = match required_version
            .split('.')
            .next()
            .expect("No major version in required_version")
        {
            "2" => "3.0.0",
            other => panic!("Please add support for hwloc v{other}.x"),
        };
        config.range_version(required_version..first_unsupported_version);
    }

    // Run pkg-config
    let lib = config
        .statik(target_os() != "macos")
        .probe("hwloc")
        .expect("Could not find a suitable version of hwloc");

    // As it turns-out, pkg-config does not correctly set up the RPATHs for the
    // transitive dependencies of hwloc itself in static builds. Fix that.
    if target_family().split(',').any(|family| family == "unix") {
        for link_path in &lib.link_paths {
            println!(
                "cargo:rustc-link-arg=-Wl,-rpath,{}",
                link_path
                    .to_str()
                    .expect("Link path is not an UTF-8 string")
            );
        }
    }

    // Forward pkg-config output for futher consumption
    lib
}

/// Install hwloc ourselves
#[cfg(feature = "vendored")]
fn setup_vendored_hwloc(required_version: &str) {
    // Determine which version to fetch and where to fetch it
    let (source_version, sha3_digest) = match required_version
        .split('.')
        .next()
        .expect("No major version in required_version")
    {
        "2" => (
            "2.11.0",
            hex("90c5d4a368fbf6abdfb848ae0ac8aa9d5ba09af27064294130b2ff1727227f4e"),
        ),
        other => panic!("Please add support for bundling hwloc v{other}.x"),
    };
    let out_path = env::var("OUT_DIR").expect("No output directory given");

    // Fetch latest supported hwloc from git
    let source_path = fetch_hwloc(out_path, source_version, sha3_digest);

    // On Windows, we build using CMake because the autotools build
    // procedure does not work with MSVC, which is often needed on this OS
    if target_os() == "windows" {
        install_hwloc_cmake(source_path);
    } else {
        // On other OSes, we use autotools and pkg-config
        install_hwloc_autotools(source_path);
    }
}

/// Decode a hexadecimal digest into a stream of bytes
#[cfg(feature = "vendored")]
fn hex(hex: &'static str) -> Box<[u8]> {
    assert_eq!(hex.len() % 2, 0, "Digest string {hex:?} should contain full bytes, i.e. pairs of hex digits, but it contains an odd number of bytes");
    hex.as_bytes()
        .chunks_exact(2)
        .map(|hexdigit_pair| {
            hexdigit_pair.iter().copied().fold(0, |acc, mut hexdigit| {
                hexdigit = match hexdigit.to_ascii_lowercase() {
                    b'0'..=b'9' => hexdigit - b'0',
                    b'a'..=b'f' => hexdigit - b'a' + 10,
                    _ => {
                        panic!("Encountered byte that is not a hexadecimal digit in digest string {hex:?}")
                    }
                };
                acc * 16 + hexdigit
            })
        })
        .collect()
}

/// Fetch, check and extract an official hwloc tarball, return extracted path
#[cfg(feature = "vendored")]
fn fetch_hwloc(
    parent_path: impl AsRef<Path>,
    version: &str,
    sha3_digest: impl AsRef<[u8]>,
) -> PathBuf {
    // Predict location where tarball would be extracted
    let parent_path = parent_path.as_ref();
    let extracted_path = parent_path.join(format!("hwloc-{version}"));

    // Reuse any existing download
    if extracted_path.exists() {
        eprintln!("Reusing previous hwloc v{version} download");
        return extracted_path;
    }

    // Determine hwloc tarball URL
    let mut version_components = version.split('.');
    let major = version_components.next().expect("no major hwloc version");
    let minor = version_components.next().expect("no minor hwloc version");
    let url = format!(
        "https://download.open-mpi.org/release/hwloc/v{major}.{minor}/hwloc-{version}.tar.gz"
    );

    // Download hwloc tarball
    eprintln!("Downloading hwloc v{version} from URL {url}...");
    let tar_gz = ureq::get(url)
        .call()
        .expect("failed to GET hwloc source")
        .into_body()
        .read_to_vec()
        .expect("failed to parse hwloc source HTTP body");

    // Verify tarball integrity
    eprintln!("Verifying hwloc source integrity...");
    let mut hasher = Sha3_256::new();
    hasher.update(&tar_gz[..]);
    assert_eq!(
        &hasher.finalize()[..],
        sha3_digest.as_ref(),
        "downloaded hwloc source failed integrity check"
    );

    // Extract tarball
    eprintln!("Extracting hwloc source...");
    let tar = GzDecoder::new(&tar_gz[..]);
    let mut archive = Archive::new(tar);
    archive
        .unpack(parent_path)
        .expect("failed to extract hwloc source");

    // Predict location where tarball was extracted
    extracted_path
}

/// Compile hwloc using cmake, return local installation path
#[cfg(feature = "vendored")]
fn install_hwloc_cmake(source_path: impl AsRef<Path>) {
    // Locate CMake support files, make sure they are present
    // (should be the case on any hwloc release since 2.8)
    let cmake_path = source_path.as_ref().join("contrib").join("windows-cmake");
    assert!(
        cmake_path.join("CMakeLists.txt").exists(),
        "Need hwloc's CMake support to build on Windows (with MSVC)"
    );

    // Configure the CMake build
    let mut config = cmake::Config::new(cmake_path);

    // Allow specifying the CMake build profile
    if let Ok(profile) = env::var("HWLOC_BUILD_PROFILE") {
        config.profile(&profile);
    }

    // Allow specifying the build toolchain
    if let Ok(toolchain) = env::var("HWLOC_TOOLCHAIN") {
        config.define("CMAKE_TOOLCHAIN_FILE", &toolchain);
    }

    // Disable testing
    config.define("HWLOC_ENABLE_TESTING", "OFF");
    // Disable unnecessary CLI tools
    config.define("HWLOC_SKIP_LSTOPO", "1");
    config.define("HWLOC_SKIP_TOOLS", "1");

    // Set the mode to Release
    config.profile("Release");

    // Build hwloc
    let install_path = config.always_configure(false).build();

    // Configure our own build to use this hwloc
    println!("cargo:rustc-link-lib=static=hwloc");
    println!(
        "cargo:rustc-link-search={}",
        install_path.join("lib").display()
    );
}

/// Compile hwloc using autotools, return local installation path
#[cfg(feature = "vendored")]
fn install_hwloc_autotools(source_path: impl AsRef<Path>) {
    // Configure for static linking
    let mut config = autotools::Config::new(source_path);
    config.enable_static().disable_shared();
    if target_os() == "macos" {
        // macOS need some extra stuff to be linked for all symbols to be found
        config.ldflag("-F/System/Library/Frameworks -framework CoreFoundation");
        // And libxml2 must be linked in explicitly for some inexplicable reason
        if cfg!(feature = "vendored-extra") {
            println!("cargo:rustc-link-lib=xml2");
        }
    }

    // Disable optional features unless user explicitly asked for them
    if cfg!(not(feature = "vendored-extra")) {
        config
            .disable("cairo", None)
            .disable("io", None)
            .disable("libxml2", None);
    }

    // Run the build
    let install_path = config.fast_build(true).reconf("-ivf").build();

    // Compute the associated PKG_CONFIG_PATH
    let new_path = |lib_dir: &str| install_path.join(lib_dir).join("pkgconfig");
    let new_path = format!(
        "{}:{}",
        new_path("lib").display(),
        new_path("lib64").display()
    );

    // Combine it with any pre-existing PKG_CONFIG_PATH
    match env::var("PKG_CONFIG_PATH") {
        Ok(old_path) if !old_path.is_empty() => {
            env::set_var("PKG_CONFIG_PATH", format!("{new_path}:{old_path}"))
        }
        Ok(_) | Err(env::VarError::NotPresent) => env::set_var("PKG_CONFIG_PATH", new_path),
        Err(other_err) => panic!("Failed to check PKG_CONFIG_PATH: {other_err}"),
    }

    // Configure this build to use hwloc via pkg-config
    find_hwloc(None);
}

/// Cross-compilation friendly alternative to `cfg!(target_os)`
fn target_os() -> &'static str {
    static TARGET_OS: OnceLock<Box<str>> = OnceLock::new();
    TARGET_OS
        .get_or_init(|| {
            std::env::var("CARGO_CFG_TARGET_OS")
                .expect("Cargo should tell us what the target OS is")
                .into_boxed_str()
        })
        .as_ref()
}

/// Cross-compilation friendly alternative to `cfg!(target_family)`
fn target_family() -> &'static str {
    static TARGET_FAMILY: OnceLock<Box<str>> = OnceLock::new();
    TARGET_FAMILY
        .get_or_init(|| {
            std::env::var("CARGO_CFG_TARGET_FAMILY")
                .expect("Cargo should tell us what the target family is")
                .into_boxed_str()
        })
        .as_ref()
}
