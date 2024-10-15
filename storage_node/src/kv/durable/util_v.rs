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

    pub proof fn lemma_concat_of_disjoint_seqs_has_no_duplicates<T>(a: Seq<T>, b: Seq<T>)
        requires
            a.no_duplicates(),
            b.no_duplicates(),
            a.to_set().disjoint(b.to_set())
        ensures 
            (a + b).no_duplicates()
    {
        let a_set = a.to_set();
        let b_set = b.to_set();
        let concat = a + b;

        a.unique_seq_to_set();
        b.unique_seq_to_set();

        assert(forall |e| a.contains(e) <==> a_set.contains(e));
        assert(forall |e| b.contains(e) <==> b_set.contains(e));
        assert(forall |e| a.contains(e) ==> !b.contains(e));
        assert(forall |e| b.contains(e) ==> !a.contains(e));

        assert(concat.subrange(0, a.len() as int) == a);
        assert(concat.subrange(a.len() as int, concat.len() as int) == b);

        assert forall |i, j| {
            &&& 0 <= i < a.len()
            &&& 0 <= j < b.len()
        } implies a[i] != b[j] by {
            assert(a.contains(a[i]));
            assert(!b.contains(a[i]));
        }
    }

    pub proof fn lemma_concat_seq_equal_to_set<T>(s1: Seq<T>, s2: Seq<T>)
        requires 
            s1.no_duplicates(),
            s2.no_duplicates(),
            forall |i: int, j: int| {
                &&& 0 <= i < s1.len()
                &&& 0 <= j < s2.len()
            } ==> s1[i] != s2[j],
        ensures 
            s1.to_set() + s2.to_set() == (s1 + s2).to_set()
    {
        assert(forall |i: int| 0 <= i < s1.len() ==> #[trigger] s1[i] == (s1 + s2)[i]);
        assert(forall |i: int| 0 <= i < s2.len() ==> #[trigger] s2[i] == (s1 + s2)[s1.len() + i]);
        assert(s1.to_set() + s2.to_set() == (s1 + s2).to_set());
    }

    pub proof fn lemma_seq_push_to_set_equivalent_to_seq_to_set_insert<T>(s: Seq<T>, x: T)
        ensures
            s.push(x).to_set() == s.to_set().insert(x)
    {
        let s1 = s.push(x).to_set();
        let s2 = s.to_set().insert(x);
        assert(s1 =~= s2) by {
            assert(forall|t: T| s1.contains(t) ==> s2.contains(t));
            assert forall|t: T| s2.contains(t) implies s1.contains(t) by {
                if t == x {
                    assert(s.push(x)[s.len() as int] == x);
                }
                else {
                    assert(s.to_set().contains(t));
                    let j: int = choose|j: int| 0 <= j < s.len() && s[j] == t;
                    assert(s.push(x)[j] == t);
                }
            }
        }
    }
}
