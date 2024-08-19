extern crate bindgen;

use std::path::PathBuf;

fn main() {
    println!("cargo:rustc-link-search=libpmemlog1");
    println!("cargo:rustc-link-lib=pmemlog");
    println!("cargo:rustc-link-lib=pmem");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from("./src/");
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
