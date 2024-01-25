#[cfg(test)]
extern crate proptest;
use proptest::prelude::*;
use rand::Rng;
use rand::seq::SliceRandom;
use crate::metadata_kv::MetadataStore;
use crate::tiering_engine::{TieringEngine, ExtentMetadataWithTiering};
use std::collections::HashMap;

fn divide_into_random_segments(vec: &Vec<u8>, num_segments: usize) -> Vec<Vec<u8>> {
    let mut rng = rand::thread_rng();
    let mut segments = Vec::new();
    let mut start = 0;

    // Ensure we have at least one segment and not more segments than elements
    let num_segments = num_segments.min(vec.len()).max(1);
    let mut split_points: Vec<usize> = (1..vec.len()).collect();

    // Shuffle and pick the first `num_segments - 1` split points
    split_points.shuffle(&mut rng);
    split_points.truncate(num_segments - 1);
    split_points.sort_unstable();

    // Create each segment based on the split points
    for end in split_points.into_iter() {
        segments.push(vec[start..end].to_vec());
        start = end;
    }

    // Add the last segment
    segments.push(vec[start..].to_vec());

    // Validation: Combine the segments and compare with the original vector
    let combined: Vec<u8> = segments.iter().flatten().copied().collect();
    assert_eq!(combined, *vec);

    segments
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]

    /// Property test for `TieringEngine` using randomized data and operations.
    /// 
    /// The test creates a simulated environment with two extents and a series of randomized operations
    /// to simulate a real-world use case of the tiering engine. It tests the tiering engine's ability to handle
    /// various scenarios, including appending index data to extents, starting and ending tiering processes,
    /// and ensuring the data integrity and metadata states are consistent throughout the process.
    ///
    /// # Test Steps:
    /// 1. Initialize an `MetadataStore` with two extents.
    /// 2. Create a temporary `tiered_store` to track tiered data for validation.
    /// 3. Generate random data segments and divide them into random segments for each extent.
    /// 4. Perform a series of randomized operations:
    ///    - Append segments to extents.
    ///    - Start or end tiering processes.
    /// 5. After the randomized operations, ensure any in-progress tiering is completed.
    /// 6. Validate that the tiering process was correctly handled:
    ///    - Check if the `index_inflight_tiering_length` is zero, indicating no ongoing tiering.
    ///    - Verify that the `index_tiered_length` matches the expected length.
    ///    - Confirm that the index data is empty and the `tiered_store` contains all original data.
    ///
    /// # Parameters:
    /// - `data_segments`: Randomly generated vector of bytes, representing index data.
    /// - `num_segments`: Random number of segments to split the data into.
    /// - `num_operations`: Random number of operations to perform on the data.
    ///
    /// The test uses a mixture of deterministic logic and randomized operations to thoroughly
    /// exercise the functionality of the `TieringEngine`. It includes comprehensive assertions to
    /// validate the correctness of the engine under various conditions.
    #[test]
    fn tiering_engine_property_test(data_segments in prop::collection::vec(any::<u8>(), 16..=1024),
                                    num_segments in 1usize..=16,
                                    num_operations in 1usize..=128) {    
        let mut store = MetadataStore::<ExtentMetadataWithTiering, u8>::new();
        store.create_metadata("extent1".to_string());
        store.create_metadata("extent2".to_string());

        let mut tiered_store: HashMap<String, Vec<u8>> = HashMap::new();
        tiered_store.insert("extent1".to_string(), vec![]);
        tiered_store.insert("extent2".to_string(), vec![]);

        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();
        let mut rng = rand::thread_rng();

        // Divide data_segments into random segments
        let segments_extent1 = divide_into_random_segments(&data_segments, num_segments);
        let mut segments_extent1_iter = segments_extent1.into_iter();
        let segments_extent2 = divide_into_random_segments(&data_segments, num_segments);
        let mut segments_extent2_iter = segments_extent2.into_iter();

        let mut ops = Vec::new();
        for _ in 0..rng.gen_range(1..=num_operations) {
            match rng.gen_range(0..4) {
                0 => {
                    if let Some(segment) = segments_extent1_iter.next() {
                        store.append_index("extent1", &segment);
                        ops.push(format!("[0] append_index(extent1, {:?})", segment));
                    }
                },
                1 => {
                    if let Some(segment) = segments_extent2_iter.next() {
                        store.append_index("extent2", &segment);
                        ops.push(format!("[1] append_index(extent2, {:?})", segment));
                    }
                },
                2 => {
                    let extent_key = if rng.gen() { "extent1" } else { "extent2" };
                    let is_tiering_in_progress = store.read_metadata(extent_key).unwrap().index_inflight_tiering_length > 0;
                    engine.tier_extent_start(&mut store, extent_key);
                    if !is_tiering_in_progress {
                        let data = store.read_index(extent_key).unwrap();
                        tiered_store.get_mut(extent_key).unwrap().extend(data);
                        ops.push(format!("[2] tier_extent_start({} {:?})", extent_key, data));
                    }
                },
                _ => {
                    let extent_key = if rng.gen() { "extent1" } else { "extent2" };
                    engine.tier_extent_end(&mut store, extent_key);
                    ops.push(format!("[4] tier_extent_end({})", extent_key));
                }
            }
        }

        for extent_key in ["extent1".to_string(), "extent2".to_string()].iter() {
            // in case there is a tiering in progress, complete it
            engine.tier_extent_end(&mut store, extent_key);
            assert_eq!(store.read_metadata(extent_key).unwrap().index_inflight_tiering_length, 0);

            // tier index data if any
            engine.tier_extent_start(&mut store, extent_key);
            let data = store.read_index(extent_key).unwrap();
            tiered_store.get_mut(extent_key).unwrap().extend(data);
            engine.tier_extent_end(&mut store, extent_key);

            assert_eq!(store.read_metadata(extent_key).unwrap().index_inflight_tiering_length, 0);
            assert_eq!(store.read_index(extent_key).unwrap(), &vec![]);
        }

        // copmlete the remaining segments if any
        for _ in 0..num_segments {
            if let Some(segment) = segments_extent1_iter.next() {
                let extent_key = "extent1";
                store.append_index(extent_key, &segment);
                engine.tier_extent_start(&mut store, extent_key);
                let data = store.read_index(extent_key).unwrap();
                tiered_store.get_mut(extent_key).unwrap().extend(data);
                engine.tier_extent_end(&mut store, extent_key);
            }
            if let Some(segment) = segments_extent2_iter.next() {
                let extent_key = "extent2";
                store.append_index(extent_key, &segment);
                engine.tier_extent_start(&mut store, extent_key);
                let data = store.read_index(extent_key).unwrap();
                tiered_store.get_mut(extent_key).unwrap().extend(data);
                engine.tier_extent_end(&mut store, extent_key);
            }            
        }

        for extent_key in ["extent1".to_string(), "extent2".to_string()].iter() {
            assert_eq!(store.read_metadata(extent_key).unwrap().index_inflight_tiering_length, 0, "ops: {:?}", ops);
            assert_eq!(store.read_metadata(extent_key).unwrap().index_tiered_length, data_segments.len(), "ops: {:?}", ops);
            assert_eq!(store.read_index(extent_key).unwrap(), &vec![], "ops: {:?}", ops);
            assert_eq!(tiered_store.get(extent_key).unwrap(), &data_segments, "ops: {:?}", ops);
        }
    }
}
