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

    pub proof fn lemma_pushing_new_element_retains_no_duplicates<T>(s: Seq<T>, x: T)
        requires
            s.no_duplicates(),
            !s.contains(x)
        ensures
            s.push(x).no_duplicates()
    {
    }

    pub proof fn lemma_push_effect_on_contains<T>(s: Seq<T>, x: T)
        ensures
            forall|t: T| s.contains(t) ==> #[trigger] s.push(x).contains(t),
            forall|t: T| #[trigger] s.push(x).contains(t) ==> s.contains(t) || t == x,
            s.push(x).contains(x),
    {
        assert forall|t: T| s.contains(t) implies #[trigger] s.push(x).contains(t) by {
            let j = choose|j: int| 0 <= j < s.len() && s[j] == t;
            assert(s.push(x)[j] == t);
        }
        assert forall|t: T| #[trigger] s.push(x).contains(t) implies s.contains(t) || t == x by {
            let j = choose|j: int| 0 <= j < s.push(x).len() && s.push(x)[j] == t;
            if j < s.len() {
                assert(s[j] == t);
            }
            else {
                assert(t == x);
            }
        }
        assert(s.push(x).contains(x)) by {
            let j = s.len() as int;
            assert(s.push(x)[j] == x);
        }
    }

    pub proof fn lemma_drop_last_from_no_duplicates_effect<T>(s: Seq<T>)
        requires
            s.no_duplicates(),
            s.len() > 0,
        ensures
            forall|t: T| s.contains(t) ==> #[trigger] s.drop_last().contains(t) || t == s.last(),
            forall|t: T| #[trigger] s.drop_last().contains(t) ==> s.contains(t) && t != s.last(),
            s.drop_last().no_duplicates(),
    {
        assert forall|t: T| s.contains(t) implies #[trigger] s.drop_last().contains(t) || t == s.last() by {
            let j = choose|j: int| 0 <= j < s.len() && s[j] == t;
            if j == s.len() - 1 {
                assert(t == s.last());
            }
            else {
                assert(s.drop_last()[j] == t);
            }
        }
    }
            
}
