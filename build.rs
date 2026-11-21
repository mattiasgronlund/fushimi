// Sets `cfg(fushimi_kernel_dispatch)` where the kernel of the elementary functions (`src/dyadic`)
// picks, at run time, between a copy of each entry compiled with the target feature `fma` and one
// with Dekker's products (`src/dyadic/level.rs`): on x86-64 targets without `fma`, such as plain
// `x86-64`, whose `Interval` uses the portable backend, and `x86-64-v2`, whose `Interval` uses
// `sse42` (see `src/simd.rs`), unless the feature `force-generic` asks for the portable backend
// and no dispatch. Every other build compiles one copy, with `HAS_FMA` (`src/simd/generic.rs`).
//
// The predicate is named once here, as a `cfg`, because about a hundred functions of the kernel
// carry `#[cfg_attr(fushimi_kernel_dispatch, inline(always))]`, which written out in full would not
// fit on a line.
//
// Sets `cfg(fushimi_generic_backend)` where `Interval` uses the portable backend
// (`src/simd/generic.rs`), as the arms of `src/simd.rs` select it: with `force-generic`, and on
// targets without a backend of their own, among them plain `x86-64`. It does not look at `docsrs`,
// where `src/simd.rs` takes `unimplemented.rs` and calls none of these functions, so that the cfg
// there only pins functions that nothing calls. Where it is set, some of the backend functions
// of `generic.rs` that `Baseline` calls (`src/simd/token.rs`) are pinned in or out of line, as
// `Baseline` says; elsewhere they are the slow paths of another backend, and are left to LLVM
// as before.
// `cfg(fushimi_sse42_backend)` is set where it uses `sse42` (`src/simd/x86_64.rs`), whose
// `mul_add_ru` is then out of line, and where `Baseline` calls its forwarder
// `mul_add_ru_exported` unless `docsrs` is set, at which this does not look either, as `Baseline`
// and `CrateBaseline` say.

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rustc-check-cfg=cfg(fushimi_kernel_dispatch)");
    // Set in RUSTFLAGS to make the dispatch take the Dekker copies on a CPU that has `fma`, to
    // test and count them there (`src/dyadic/level.rs`).
    println!("cargo::rustc-check-cfg=cfg(fushimi_force_no_fma)");
    // `CARGO_CFG_TARGET_FEATURE` lists the target features of the target CPU and of
    // `-Ctarget-feature`, as `cfg(target_feature)` does.
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let has = |feature: &str| features.split(',').any(|f| f == feature);
    let force_generic = env::var_os("CARGO_FEATURE_FORCE_GENERIC").is_some();
    if arch == "x86_64" && !has("fma") && !force_generic {
        println!("cargo::rustc-cfg=fushimi_kernel_dispatch");
    }
    println!("cargo::rustc-check-cfg=cfg(fushimi_generic_backend)");
    let own_backend = arch == "aarch64"
        || (arch == "x86_64" && has("sse4.2"))
        || (arch == "wasm32" && has("simd128"));
    if force_generic || !own_backend {
        println!("cargo::rustc-cfg=fushimi_generic_backend");
    }
    println!("cargo::rustc-check-cfg=cfg(fushimi_sse42_backend)");
    if arch == "x86_64"
        && has("sse4.2")
        && !(has("avx") && has("fma"))
        && !has("avx512f")
        && !force_generic
    {
        println!("cargo::rustc-cfg=fushimi_sse42_backend");
    }
}
