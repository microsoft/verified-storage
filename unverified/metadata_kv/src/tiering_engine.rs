use crate::metadata_kv::{Metadata, MetadataStore};

// metadata with tiering
pub trait MetadataWithTiering: Metadata {
    fn get_inflight_tiering_length(&self) -> usize;
    fn start_tiering(&mut self, length: usize);
    fn end_tiering(&mut self);
}

#[derive(Clone, Debug)]
pub struct ExtentMetadataWithTiering {
    pub index_tiered_length: usize,
    pub index_inflight_tiering_length: usize,
}

impl Metadata for ExtentMetadataWithTiering {
    fn new() -> Self {
        ExtentMetadataWithTiering {
            index_tiered_length: 0,
            index_inflight_tiering_length: 0,
        }
        }

    fn update(&mut self, other: Self) {
        self.index_tiered_length = other.index_tiered_length;
        self.index_inflight_tiering_length = other.index_inflight_tiering_length;
    }
}

impl MetadataWithTiering for ExtentMetadataWithTiering {
    fn get_inflight_tiering_length(&self) -> usize {
        self.index_inflight_tiering_length
    }

    fn start_tiering(&mut self, length: usize) {
        self.index_inflight_tiering_length = length;
    }

    fn end_tiering(&mut self) {
        if self.index_inflight_tiering_length > 0 {
            self.index_tiered_length += self.index_inflight_tiering_length;
            self.index_inflight_tiering_length = 0;
        }
    }
}

/// `TieringEngine` is responsible for managing the tiering process of extents
/// within an `ExtentMetadataStore`. It provides functionalities to start and 
/// end the tiering process for a given extent.
///
/// The tiering process involves updating metadata and manipulating index data
/// associated with an extent. This engine ensures that tiering operations are
/// performed safely and correctly, based on the current state of the metadata.

pub struct TieringEngine<M> where M: MetadataWithTiering {
    _marker: std::marker::PhantomData<M>,
}

impl<M> TieringEngine::<M> where M: MetadataWithTiering {
    pub fn new() -> TieringEngine<M> {
        TieringEngine {
            _marker: std::marker::PhantomData,
        }
    }

    /// Starts the tiering process for a given extent.
    ///
    /// This function takes a mutable reference to an `ExtentMetadataStore` and the
    /// key of the extent. If the `index_inflight_tiering_length` of the extent's metadata
    /// is zero, it updates this value to the current length of the index data,
    /// indicating that the tiering process has started. If tiering is already in progress,
    /// this function acts as a no-op.    
    pub fn tier_extent_start<I>(&self, store: &mut MetadataStore<M, I>, key: &str) where I: Clone {
        // get the length of the index data (immutable borrow)
        let index_data_length = if let Some(index_data) = store.read_index(&key) {
            Some(index_data.len())
        } else {
            None
        };
    
        // perform the mutation (mutable borrow)
        if let Some(metadata) = store.metadata_store.get_mut(key) {
            if metadata.get_inflight_tiering_length() == 0 {
                if let Some(length) = index_data_length {
                    metadata.start_tiering(length);
                }
            }
        }
    }
    
    /// Ends the tiering process for a given extent.
    ///
    /// This function also takes a mutable reference to an `ExtentMetadataStore` and the
    /// key of the extent. If tiering is in progress (indicated by a non-zero 
    /// `index_inflight_tiering_length`), it trims the index data by removing the 
    /// first `index_inflight_tiering_length` bytes and updates the metadata accordingly.
    /// If no tiering is in progress, it is a no-op.    
    pub fn tier_extent_end<I>(&self, store: &mut MetadataStore<M, I>, key: &str) where I: Clone {
        // perform the trimming operation, which requires a mutable borrow of `store`
        if let Some(metadata) = store.metadata_store.get(key) {
            if metadata.get_inflight_tiering_length() > 0 {
                store.trim_index_data(key, metadata.get_inflight_tiering_length());
            }
        }
    
        // update the metadata, which again requires a mutable borrow of `store`
        if let Some(metadata) = store.metadata_store.get_mut(key) {
            metadata.end_tiering();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_test_store() -> MetadataStore::<ExtentMetadataWithTiering, u8> {
        let mut store = MetadataStore::<ExtentMetadataWithTiering, u8>::new();
        store.create_metadata("test_extent".to_string());
        store.append_index("test_extent", &[1, 2, 3]);
        store
    }

    #[test]
    fn test_tier_extent_start() {
        let mut store = setup_test_store();
        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();

        engine.tier_extent_start(&mut store, "test_extent");
        let metadata = store.read_metadata("test_extent").unwrap();
        assert_eq!(metadata.index_inflight_tiering_length, 3);
    }

    #[test]
    fn test_tier_extent_start_no_op_if_already_in_progress() {
        let mut store = setup_test_store();
        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();

        engine.tier_extent_start(&mut store, "test_extent");
        let initial_metadata = store.read_metadata("test_extent").unwrap().clone();
        store.append_index("test_extent", &[4, 5, 6, 7, 8]);
        engine.tier_extent_start(&mut store, "test_extent");
        let metadata = store.read_metadata("test_extent").unwrap();

        assert_eq!(metadata.index_inflight_tiering_length, initial_metadata.index_inflight_tiering_length);
    }

    #[test]
    fn test_tier_extent_end() {
        let mut store = setup_test_store();
        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();

        engine.tier_extent_start(&mut store, "test_extent");
        engine.tier_extent_end(&mut store, "test_extent");
        let metadata = store.read_metadata("test_extent").unwrap();

        assert_eq!(metadata.index_inflight_tiering_length, 0);
        assert_eq!(metadata.index_tiered_length, 3);
    }

    #[test]
    fn test_tier_extent_start_append_end() {
        let mut store = setup_test_store();
        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();

        engine.tier_extent_start(&mut store, "test_extent");
        store.append_index("test_extent", &[4, 5, 6, 7, 8]);
        engine.tier_extent_end(&mut store, "test_extent");
        let metadata = store.read_metadata("test_extent").unwrap();

        assert_eq!(metadata.index_inflight_tiering_length, 0);
        assert_eq!(metadata.index_tiered_length, 3);
    }

    #[test]
    fn test_tier_extent_end_no_op_if_not_in_progress() {
        let mut store = setup_test_store();
        let engine = TieringEngine::<ExtentMetadataWithTiering>::new();

        let initial_metadata = store.read_metadata("test_extent").unwrap().clone();
        engine.tier_extent_end(&mut store, "test_extent");
        let metadata = store.read_metadata("test_extent").unwrap();

        assert_eq!(metadata.index_inflight_tiering_length, initial_metadata.index_inflight_tiering_length);
        assert_eq!(metadata.index_tiered_length, initial_metadata.index_tiered_length);
        assert_eq!(metadata.index_tiered_length, 0);
    }
}
