#[cfg(target_os = "linux")]
pub const PM_DEV: &str = "/dev/pmem0";
#[cfg(target_os = "linux")]
pub const MOUNT_POINT: &str = "/mnt/pmem";
#[cfg(target_os = "linux")]
pub const KVSTORE_FILE: &str = "/mnt/pmem/capybarakv";

#[cfg(target_os = "windows")]
pub const PM_DEV: &str = "C:\\pmem";
#[cfg(target_os = "windows")]
pub const MOUNT_POINT: &str = PM_DEV;
#[cfg(target_os = "windows")]
pub const KVSTORE_FILE: &str = "C:\\pmem\\capybarakv";

// TODO: read these from config file
pub const KVSTORE_ID: u128 = 1234;
pub const REGION_SIZE: u64 = 1024*1024*1024*15;

// TODO: read these from a config file?
pub const NUM_KEYS: u64 = 3125000;

// for use in the full startup experiment
// 1024*1024*1024*115 / (1024 + 1024*512 + 128) (approximately)
// 115GB CapybaraKV instances uses 100% of PM device
// the extra 128 bytes accounts for metadata and CRCs 
pub const CAPYBARAKV_MAX_KEYS: u64 = 30000; 