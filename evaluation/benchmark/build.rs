#[cfg(target_os = "linux")]
extern crate bindgen;

#[cfg(target_os = "linux")]
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=wrapper.h");

    let bindings = bindgen::Builder::default()
        .clang_args(&[
            "-I../viper/include", 
            "-I/usr/include/c++/14", 
            "-I/usr/include/x86_64-linux-gnu/c++/14",
            "-I../concurrentqueue",
            "-xc++",
            "-std=c++17",
            "-w"])
        .size_t_is_usize(false)
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from("./src/");
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}