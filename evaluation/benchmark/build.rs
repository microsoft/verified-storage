use std::env;

#[cfg(target_os = "linux")]
extern crate bindgen;

#[cfg(target_os = "linux")]
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=../viper_wrapper/viper_wrapper.hpp");
    println!("cargo:rerun-if-changed=../viper_wrapper/viper_wrapper.cpp");

    let viper_wrapper_path = PathBuf::from("../viper_wrapper")
        .canonicalize()
        .expect("cannot canonicalize path");

    let headers_path = viper_wrapper_path.join("viper_wrapper.hpp");
    let headers_path_str = headers_path.to_string_lossy();

    // This is the path to the intermediate object file for our library.
    let obj_path = viper_wrapper_path.join("viper_wrapper.o");
    // This is the path to the static library file.
    let lib_path = viper_wrapper_path.join("libviper_wrapper.a");

    let java_home = env::var("JAVA_HOME").unwrap();

    // build object file for the viper wrapper
    // based on instructions from https://rust-lang.github.io/rust-bindgen/non-system-libraries.html
    if !std::process::Command::new("clang++")
        .arg("-c")
        .arg("-I../viper/include")
        .arg("-I../viper/benchmark")
        .arg("-I../viper_deps/concurrentqueue")
        .arg("-I../viper_deps/benchmark/include")
        .arg("-I../viper_deps/libpmemobj-cpp/include")
        .arg(format!("-I{java_home}/include"))
        .arg(format!("-I{java_home}/include/linux"))
        // .arg("-DVIPER_BUILD_BENCHMARKS=ON")
        // .arg("-DVIPER_PMDK_PATH=/usr/share/pmdk")
        // .arg("-DLIBPMEMOBJ++_PATH=/usr/lib/x86_64-linux-gnu")
        .arg("-mclwb")
        .arg("-std=c++17")
        .arg("-o")
        .arg(&obj_path)
        .arg(viper_wrapper_path.join("viper_wrapper.cpp"))
        .output()
        .expect("could not spawn `clang`")
        .status
        .success()
    { panic!("could not compile object file") }

    // build the static library file for the viper wrapper
    if !std::process::Command::new("ar")
        .arg("rcs")
        .arg(lib_path)
        .arg(obj_path)
        .output()
        .expect("could not spawn `ar`")
        .status
        .success()
    { panic!("could not emit library file"); }

    println!("cargo:rustc-link-search={}", viper_wrapper_path.to_str().unwrap());
    println!("cargo:rustc-link-lib=static=viper_wrapper");
    println!("cargo:rustc-link-lib=benchmark");
    println!("cargo:rustc-link-lib=pmem");
    println!("cargo:rustc-link-lib=pmempool");
    println!("cargo:rustc-link-lib=pmemobj");

    let bindings = bindgen::Builder::default()
        .header(headers_path_str)
        .clang_args(&[
            "-I../viper/include", 
            "-I/usr/include/c++/14", 
            "-I/usr/include/x86_64-linux-gnu/c++/14",
            "-I../concurrentqueue",
            "-I../viper_wrapper",
            "-I../viper/benchmark",
            "-I../viper_deps/libpmemobj-cpp/include",
            "-xc++",
            "-std=c++17",
            "-w"])
        .allowlist_type("ViperDB.*")
        .allowlist_type(".*viperdb.*")
        .allowlist_function(".*viperdb.*")
        .allowlist_var(".*viperdb.*")
        // .opaque_type(".*ViperDB.*")
        .opaque_type("ViperDB")
        .opaque_type("std::.*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .size_t_is_usize(false)
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from("./src/");
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}