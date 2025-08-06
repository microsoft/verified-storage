#[cfg(all(target_os = "linux", feature = "pmem"))]
pub mod linux_pmemfile_t;
#[cfg(target_os = "windows")]
pub mod windows_pmemfile_t;
#[cfg(any(target_os = "macos", all(target_os = "linux", not(feature = "pmem"))))]
pub mod mmap_pmemfile_t;

pub mod crashinv_t;
pub mod crc_t;
pub mod hamming_t;
pub mod hamming_v;
pub mod pmemmock_t;
pub mod pmemspec_t;
pub mod pmemutil_v;
pub mod pmcopy_t;
pub mod power_t;
pub mod power_sound_t;
pub mod power_v;
// pub mod subregion_v;
pub mod traits_t;

// Proof of correspondence between prophecy-based model of persistent
// memory durability and an explicit asynchronous model of persistent
// memory writes.
pub mod pmem_async_equiv_t;
pub mod pmem_async_equiv_v;
pub mod pmem_async_spec_t;
