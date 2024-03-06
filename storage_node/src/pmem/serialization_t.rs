use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    // In order to serialize an object straight onto PM, we need functions
    // that serialize to a given raw pointer, and also have a byte-level
    // ghost representation so that we can do crash consistency proofs.
    // first idea is for the caller to provide a function that serializes/
    // deserializes self to a specific offset/raw address. Ideally the
    // implementor would not have to use unsafe code; that would hopefully
    // be only in the pm functions that invoke the serde methods.
    // Given the serialized length of the object (which we prove is correct),
    // PM could obtain a mutable slice from a raw pointer to PM and pass
    // that to the serialization function?

    // first things to try because they might not work:
    // - calling serialize() in a pm method
    // - implementing serialize() for something (mostly re: copying into the slice)

    // rust doesn't yet support trait generics (generic methods in traits that are not otherwise
    // generic, I guess?) which I think are required here. The whole PersistentMemoryRegions trait
    // should not be generic because there can be multiple serializable types that we want to
    // be able to write, and making PersistentMemoryRegions generic would restrict us to only
    // a single type. has to be at a low enough level to serialize the bytes directly to PM, so we
    // can't move it up to a higher level of abstraction or make it more concrete...
    // talk to Chris about this.

    pub trait Serializable : Sized {
        spec fn spec_serialize(&self) -> Seq<u8>;

        spec fn serialized_len(&self) -> int;

        fn get_serialized_len(&self) -> (out: u64)
            ensures
                out == self.spec_serialize().len()
        ;

        fn serialize(&self, destination: &mut [u8])
            requires
                old(destination)@.len() == self.spec_serialize().len(),
            ensures
                destination@ =~= self.spec_serialize(),
        ;

        fn deserialize(source: &[u8]) -> Self;
    }
}
