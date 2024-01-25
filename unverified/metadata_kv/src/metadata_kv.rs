use std::collections::HashMap;

/// The `MetadataStore` module provides an in-memory key-value store, specialized
/// for managing extent metadata (`ExtentMetadata`) and index data (`IndexData`).
/// This module is designed to facilitate operations on two different types of data structures:
/// fixed-length data (metadata) and variable-length data (index).
///
/// `Metadata` is a fixed-length data structure used to store metadata about extents.
/// It includes fields like `index_tiered_length` and `index_inflight_tiering_length`,
/// which are crucial for the tiering process.
///
/// `Index` is a variable-length data structure represented as a `Vec<u8>`, used
/// to store index data associated with extents. It allows operations like appending
/// and overwriting data.
///
/// The `MetadataStore` struct serves as the core of this module, providing
/// a unified interface to manage both metadata and index data associated with
/// various extents. It supports operations like creating extents, reading, updating,
/// and deleting metadata, as well as appending and overwriting index data.
///
/// This module is designed with a focus on simplicity and efficiency, suitable for
/// scenarios where an in-memory, non-concurrent data store is sufficient.

pub trait Metadata {
    fn new() -> Self;
    fn update(&mut self, other: Self);
}

// Generic struct for Index data
pub struct Index<I> {
    data: Vec<I>,
}

impl<I> Index<I> {
    pub fn new() -> Self {
        Index { data: Vec::new() }
    }

    // pub fn append(&mut self, item: I) {
    //     self.data.push(item);
    // }

    // pub fn trim_start(&mut self, amount: usize) {
    //     if amount <= self.data.len() {
    //         self.data.drain(0..amount);
    //     }
    // }

    // pub fn overwrite(&mut self, new_data: Vec<I>) {
    //     self.data = new_data;
    // }
}

// Define the KV store with generic Metadata and Index
pub struct MetadataStore<M, I> where M: Metadata {
    pub metadata_store: HashMap<String, M>,
    index_store: HashMap<String, Index<I>>,
}

impl<M, I> MetadataStore<M, I> where M: Metadata, I: Clone {
    pub fn new() -> MetadataStore<M, I> {
        MetadataStore {
            metadata_store: HashMap::new(),
            index_store: HashMap::new(),
        }
    }

    pub fn create_metadata(&mut self, key: String) {
        self.metadata_store.insert(key.clone(), M::new());
        self.index_store.insert(key, Index::new());
    }

    pub fn read_metadata(&self, key: &str) -> Option<&M> {
        self.metadata_store.get(key)
    }

    pub fn update_metadata(&mut self, key: &str, data: M) {
        if let Some(metadata) = self.metadata_store.get_mut(key) {
            metadata.update(data);
        }
    }

    pub fn delete_metadata(&mut self, key: &str) {
        self.metadata_store.remove(key);
        self.index_store.remove(key);
    }

    pub fn read_index(&self, key: &str) -> Option<&Vec<I>> {
        if let Some(data) = self.index_store.get(key) {
            Some(&data.data)
        } else {
            None
        }
    }

    pub fn append_index(&mut self, key: &str, additional_data: &[I]) {
        if let Some(index) = self.index_store.get_mut(key) {
            index.data.extend_from_slice(additional_data);
        }
    }

    pub fn overwrite_index(&mut self, key: String, new_data: Index<I>) {
        self.index_store.insert(key, new_data);
    }

    pub fn trim_index_data(&mut self, key: &str, trim_length: usize) {
        if let Some(index_data) = self.index_store.get_mut(key) {
            if trim_length <= index_data.data.len() {
                index_data.data.drain(0..trim_length);
            }
        }
    }        
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct ToyMetadata {
        pub length: usize,
    }
    
    impl Metadata for ToyMetadata {
        fn new() -> Self {
            ToyMetadata {
                length: 0,
            }
        }
    
        fn update(&mut self, other: Self) {
            self.length = other.length;
        }
    }

    #[test]
    fn test_create_metadata_and_read() {
        let mut store = MetadataStore::<ToyMetadata, u8>::new();
        let key = "test_extent".to_string();

        store.create_metadata(key.clone());
        let metadata = store.read_metadata(&key);

        assert!(metadata.is_some());
        assert_eq!(metadata.unwrap().length, 0);
    }

    #[test]
    fn test_update_metadata() {
        let mut store = MetadataStore::<ToyMetadata, u8>::new();
        let key = "test_extent".to_string();

        store.create_metadata(key.clone());
        let new_metadata = ToyMetadata {
            length: 10,
        };

        store.update_metadata(&key, new_metadata);

        let updated_metadata = store.read_metadata(&key).unwrap();
        assert_eq!(updated_metadata.length, 10);
    }

    #[test]
    fn test_append_and_overwrite_index() {
        let mut store = MetadataStore::<ToyMetadata, u8>::new();
        let key = "test_extent".to_string();

        store.create_metadata(key.clone());
        store.append_index(&key, &[1, 2, 3]);

        let index_data = store.read_index(&key).unwrap();
        assert_eq!(index_data, &vec![1, 2, 3]);

        store.overwrite_index(key.clone(), Index::<u8> { data: vec![4, 5, 6] });
        let new_index_data = store.read_index(&key).unwrap();
        assert_eq!(new_index_data, &vec![4, 5, 6]);
    }

    #[test]
    fn test_trim_index_data() {
        let mut store = MetadataStore::<ToyMetadata, u8>::new();
        
        // Create an extent with initial index data
        let key = "test_extent".to_string();
        store.create_metadata(key.clone());
        let initial_data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        store.append_index(&key, &initial_data);

        // Trim the index data
        let trim_length = 5; // Length to trim from the beginning
        store.trim_index_data(&key, trim_length);

        // Retrieve the trimmed data and verify its length and contents
        let trimmed_data = store.read_index(&key).unwrap();
        assert_eq!(trimmed_data.len(), initial_data.len() - trim_length);
        assert_eq!(*trimmed_data, initial_data[trim_length..]);
    }    

    #[test]
    fn test_delete_metadata() {
        let mut store = MetadataStore::<ToyMetadata, u8>::new();
        let key = "test_extent".to_string();

        store.create_metadata(key.clone());
        store.delete_metadata(&key);

        assert!(store.read_metadata(&key).is_none());
        assert!(store.read_index(&key).is_none());
    }
}
