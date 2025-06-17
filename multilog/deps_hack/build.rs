#[cfg(target_os = "linux")]
extern crate bindgen;

#[cfg(all(target_os = "linux", feature = "pmem"))]
use std::path::PathBuf;

#[cfg(all(target_os = "linux", feature = "pmem"))]
fn setup_linux_pmem()
{
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

fn main() {
    #[cfg(all(target_os = "linux", feature = "pmem"))]
    setup_linux_pmem();
}
