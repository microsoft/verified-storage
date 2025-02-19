use crate::capybarakv_client::*;
use crate::kv_interface::*;
use crate::{TestKey, TestValue, TestListElem, NUM_KEYS};

use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

const TEST_CONFIG_FILE_PATH: &str = "../capybarakv_test_config.toml";

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn append_and_read1() {
        CapybaraKvClient::<TestKey, TestValue, TestListElem>::setup_from_config_file(TEST_CONFIG_FILE_PATH).unwrap();
    }
}
