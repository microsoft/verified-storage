use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmemspec_t::*;

verus! {

    pub struct VolatileMemoryMockingPersistentMemory
    {
        contents: Vec<u8>
    }

    impl PersistentMemory for VolatileMemoryMockingPersistentMemory {
        closed spec fn view(self) -> Seq<u8>
        {
            self.contents@
        }

        closed spec fn inv(self) -> bool
        {
            self.contents.len() <= u64::MAX
        }

        #[verifier::external_body]
        fn new(capacity: u64) -> (result: Result<Self, ()>)
        {
            Ok(Self {contents: vec![0; capacity as usize]})
        }

        #[verifier::external_body]
        closed spec fn impervious_to_corruption(self) -> bool
        {
            unimplemented!()
        }

        fn get_capacity(&self) -> (result: u64)
        {
            // TODO: handle errors
            self.contents.len() as u64//.try_into().unwrap()
        }

        #[verifier::external_body]
        fn read(&self, addr: u64, num_bytes: u64) -> (out: (Vec<u8>, Ghost<Seq<int>>))
        {
            // TODO: handle errors
            let addr_usize: usize = addr as usize;//.try_into().unwrap();
            let num_bytes_usize: usize = num_bytes as usize;//.try_into().unwrap();
            (
                self.contents[addr_usize..addr_usize+num_bytes_usize].to_vec(),
                Ghost(Seq::<int>::new(num_bytes as nat, |i: int| i + addr)),
            )
        }

        #[verifier::external_body]
        fn write(&mut self, addr: u64, bytes: &[u8])
        {
            // TODO: handle errors
            let addr_usize: usize = addr as usize;//.try_into().unwrap();
            self.contents.splice(addr_usize..addr_usize+bytes.len(), bytes.iter().cloned());
        }
    }

}
