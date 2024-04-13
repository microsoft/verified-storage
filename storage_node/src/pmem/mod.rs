pub mod device_t;
// #[cfg(windows)]
// pub mod pmemfile_t;
#[cfg(target_os = "linux")]
pub mod linux_pmemfile_t;
// pub mod pmemmock_t;
pub mod pmemspec_t;
pub mod pmemutil_v;
pub mod serialization_t;
pub mod timestamp_t;
