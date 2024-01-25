mod metadata_kv;
mod tiering_engine;
mod tiering_engine_proptest;
use crate::metadata_kv::MetadataStore;
use crate::tiering_engine::{TieringEngine, ExtentMetadataWithTiering};

fn main() {
    let mut store = MetadataStore::<ExtentMetadataWithTiering, u8>::new();

    store.create_metadata("test_extent".to_string());
    store.append_index("test_extent", &[1, 2, 3]);

    let tiering_engine = TieringEngine::new();
    tiering_engine.tier_extent_start(&mut store, "test_extent");
    tiering_engine.tier_extent_end(&mut store, "test_extent");
}