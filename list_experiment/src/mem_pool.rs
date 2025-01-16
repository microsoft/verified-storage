pub trait MemoryPool: Sized {
    fn len(&self) -> u64;
}
