use crate::capybarakv_client::*;
use crate::kv_interface::*;
use crate::{TestKey, TestValue, TestListElem, NUM_KEYS, KEY_LEN, VALUE_LEN};

use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

const TEST_CONFIG_FILE_PATH: &str = "../capybarakv_test_config.toml";

// IMPORTANT NOTE: these must be run with --test-threads=1 to prevent them 
// from being run in parallel.

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn append_and_read1() {
        // Append some elements to a key's list and read them back

        let list_len: usize = 10;

        let config = CapybaraKvClient::<TestKey, TestValue, TestListElem>::setup_from_config_file(TEST_CONFIG_FILE_PATH).unwrap();
        {
            // new scope since client has to be dropped before we can call cleanup
            let mut client = CapybaraKvClient::<TestKey, TestValue, TestListElem>::start_from_config(&config).unwrap();
           
            // insert a new key
            let value = TestValue { value: [0u8; VALUE_LEN] };
            let key = TestKey { key: [1u8; KEY_LEN] };
            client.put(&key, &value).unwrap();

            // append to the list
            for i in 0..list_len {
                let new_list_elem = TestListElem { start: i as u64, end: i as u64 };
                client.append_to_list(&key, new_list_elem).unwrap();
            }

            // read the contents of the list back.
            let list = client.read_list(&key).unwrap();
            for i in 0..list_len {
                assert!(list[i].start == i as u64);
                assert!(list[i].end == i as u64);
            }
        }
        CapybaraKvClient::<TestKey, TestValue, TestListElem>::cleanup_from_config(&config);
    }

    #[test]
    fn append_and_read2() {
        // Append some elements to a key's list and read them back

        let num_keys: usize = 30;
        let list_entries: usize = 10;
        
        let config = CapybaraKvClient::<TestKey, TestValue, TestListElem>::setup_from_config_file(TEST_CONFIG_FILE_PATH).unwrap();
        {   
            // new scope since client has to be dropped before we can call cleanup
            let mut client = CapybaraKvClient::<TestKey, TestValue, TestListElem>::start_from_config(&config).unwrap();
            
            // insert multiple keys
            let value = TestValue { value: [0u8; VALUE_LEN] };
            let mut keys = Vec::new();
            for i in 0..num_keys {
                let key = TestKey { key: [i as u8; KEY_LEN] };
                keys.push(key);
                client.put(&key, &value).unwrap();
            }

            // append to each of the lists. outer loop iterates over # of 
            // elements and inner loop over keys to make it slightly more 
            // complicated
            for i in 0..list_entries {
                for j in 0..num_keys {
                    let key = keys[j];
                    let new_list_elem = TestListElem { start: i as u64, end: i as u64 };
                    client.append_to_list(&key, new_list_elem).unwrap();
                }
            }

            // read each list back and check that its contents are correct
            for i in 0..num_keys {
                let key = TestKey { key: [i as u8; KEY_LEN] };
                let list = client.read_list(&key).unwrap();
                for j in 0..list_entries {
                    assert!(list[j].start == j as u64);
                    assert!(list[j].end == j as u64);
                }
            }
        }
        CapybaraKvClient::<TestKey, TestValue, TestListElem>::cleanup_from_config(&config);
    }

    #[test]
    fn append_and_trim() {
        // Append some elements to a key's list and read them back

        let num_keys: usize = 10;
        let list_entries: usize = 10;
        
        let config = CapybaraKvClient::<TestKey, TestValue, TestListElem>::setup_from_config_file(TEST_CONFIG_FILE_PATH).unwrap();
        {   
            // new scope since client has to be dropped before we can call cleanup
            let mut client = CapybaraKvClient::<TestKey, TestValue, TestListElem>::start_from_config(&config).unwrap();
            
            // insert multiple keys
            let value = TestValue { value: [0u8; VALUE_LEN] };
            let mut keys = Vec::new();
            for i in 0..num_keys {
                let key = TestKey { key: [i as u8; KEY_LEN] };
                keys.push(key);
                client.put(&key, &value).unwrap();
            }

            // append to each of the lists. outer loop iterates over # of 
            // elements and inner loop over keys to make it slightly more 
            // complicated
            for i in 0..list_entries {
                for j in 0..num_keys {
                    let key = keys[j];
                    let new_list_elem = TestListElem { start: i as u64, end: i as u64 };
                    client.append_to_list(&key, new_list_elem).unwrap();
                }
            }

            // trim from each list. the ith list has i elements trimmed 
            // to test different trim lengths.
            for i in 0..num_keys {
                let key = TestKey { key: [i as u8; KEY_LEN] };
                client.trim_list(&key, i).unwrap();
            }

            for i in 0..num_keys {
                let key = TestKey { key: [i as u8; KEY_LEN] };
                let list = client.read_list(&key).unwrap();
                assert!(list.len() == list_entries - i);
                for j in 0..list.len(){
                    assert!(list[j].start == (j + i) as u64);
                    assert!(list[j].end == (j + i) as u64);
                }
            }

        }
        CapybaraKvClient::<TestKey, TestValue, TestListElem>::cleanup_from_config(&config);
    }
}
