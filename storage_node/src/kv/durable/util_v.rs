use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This enum replaces Options in views of durable components 
    // where the difference between a fully-valid entry and an entry
    // that has been initialized but not yet made valid is important
    pub enum DurableEntry<T> {
        Valid(T),
        Tentative(T),
        Invalid
    }

    impl<T> DurableEntry<T> {
        pub open spec fn unwrap_valid(self) -> T 
            recommends
                self matches Self::Valid(_)
        {
            self.get_Valid_0()
        }

        #[verifier::inline]
        #[allow(non_snake_case)]
        pub open spec fn get_Valid_0(self) -> T {
            get_variant_field(self, "Valid", "0")
        }
    }
}