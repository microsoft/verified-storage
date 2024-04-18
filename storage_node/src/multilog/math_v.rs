use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

/// Computes `x % y`. This is useful where we want to trigger on a
/// modulo operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn modulus(x: int, y: int) -> int {
    x % y
}

/// Computes the boolean `x <= y`. This is useful where we want to
/// trigger on a `<=` operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn is_le(x: int, y: int) -> bool {
    x <= y
}

// Note: add and sub are defined in vstd/math.rs but not public
// for use outside the vstd crate
/// This function adds two integers together. It's sometimes
/// useful as a substitute for `+` in triggers that feature
/// function invocations, since mathematical operators can't be
/// mixed with function invocations in triggers.
pub open spec fn add1(x: int, y: int) -> int {
    x + y
}

/// This function subtracts two integers. It's sometimes useful as
/// a substitute for `-` in triggers that feature function
/// invocations, since mathematical operators can't be mixed with
/// function invocations in triggers.
pub open spec fn sub1(x: int, y: int) -> int {
    x - y
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that `x` can be expressed as `d` times the quotient `x / d` plus
/// the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{
    assert(x == d * (x / d) + (x % d)) by {
        lemma_fundamental_div_mod_nonlinear(x, d);
    }
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires
        0 < m,
    ensures
        (m * a + b) % m == b % m,
    decreases
            (if a > 0 {
                a
            } else {
                -a
            }),
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (m * u + b) % m == b % m;
    lemma_mul_induction(f);
    assert(f(a));
}

/// Proof that a natural number x divided by a larger natural number
/// gives a remainder equal to x. Specifically, because `x < m`, we
/// know `x % m == x`.
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        x % m == x,
{
    lemma_small_mod_nonlinear(x, m);
}

/// This function states various useful properties about the modulo
/// operator when the divisor is `n`.
pub open spec fn mod_auto(n: int) -> bool
    recommends
        n > 0,
{
    &&& (n % n == 0 && (-n) % n == 0)
    &&& (forall|x: int| #[trigger] ((x % n) % n) == x % n)
    &&& (forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x)
    &&& mod_auto_plus(n)
    &&& mod_auto_minus(n)
}


/// Proof of `mod_auto(n)`, which states various useful properties
/// about the modulo operator when the divisor is the positive number
/// `n`
pub proof fn lemma_mod_auto(n: int)
    requires
        n > 0,
    ensures
        mod_auto(n),
{
    lemma_mod_basics(n);
    lemma_mul_auto();
    assert forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        } by {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == xq * n + xr);
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr + yr < n {
            lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
        } else {
            lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
        }
    }
    assert forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        } by {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == n * (x / n) + (x % n));
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr - yr >= 0 {
            lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
        } else {  // xr - yr < 0
            lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
        }
    }
}


/// Proof that multiplication is commutative, distributes over
/// addition, and distributes over subtraction
pub proof fn lemma_mul_auto()
    ensures
        mul_auto(),
{
    lemma_mul_commutes();
    lemma_mul_distributes();
}

/// Proof of the fundamental theorem of division and modulo: That for
/// any positive divisor `d` and any integer `x`, `x` is equal to `d`
/// times `x / d` plus `x % d`.
#[verifier::nonlinear]
pub proof fn lemma_fundamental_div_mod_nonlinear(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{}

/// Proof that a natural number `x` divided by a larger natural number
/// `m` gives a remainder equal to `x`
#[verifier(nonlinear)]
pub proof fn lemma_small_mod_nonlinear(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        #[trigger] modulus(x as int, m as int) == x as int,
{}

/// Proof that multiplication distributes over addition in this
/// specific case, i.e., that `x * (y + z)` equals `x * y` plus `x * z`
#[verifier::nonlinear]
pub proof fn lemma_mul_is_distributive_add_nonlinear(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
{
}

/// Proof that dividing a non-negative integer by a larger integer results in a quotient of 0
#[verifier::nonlinear]
pub proof fn lemma_small_div_nonlinear()
    ensures
        forall|x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger] (x / d) == 0,
{
}

/// Proof of Euclid's division lemma, i.e., that any integer `x`
/// modulo any positive integer `m` is in the half-open range `[0, m)`.
#[verifier(nonlinear)]
pub proof fn lemma_mod_range_nonlinear(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= #[trigger] modulus(x, m) < m,
{
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. Specifically, `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (-m + b) % m == b % m,
{
    lemma_mod_auto(m);
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in the base case of 0, and proves correctness of
/// inductive steps both upward and downward from the base case. This
/// lemma invokes induction to establish that the predicate holds for
/// all integers.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, 1))`.
/// `add1(i, 1)` is just `i + 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i <= 0`, `f(i) ==> f(sub1(i, 1))`.
/// `sub1(i, 1)` is just `i - 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_mul_induction(f: spec_fn(int) -> bool)
    requires
        f(0),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
        forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
    ensures
        forall|i: int| #[trigger] f(i),
{
    assert forall|i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the sum `x % n + y % n`: (1) It's in the range
/// `[0, n)` and it's equal to `(x + y) % n`. (2) It's in the range
/// `[n, n + n)` and it's equal to `(x + y) % n + n`.
pub open spec fn mod_auto_plus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the difference `x % n - y % n`: (1) It's in the
/// range `[0, n)` and it's equal to `(x - y) % n`. (2) It's in the
/// range `[-n, 0)` and it's equal to `(x + y) % n - n`.
pub open spec fn mod_auto_minus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        }
}

/// This function expresses that multiplication is commutative,
/// distributes over addition, and distributes over subtraction
pub open spec fn mul_auto() -> bool {
    &&& forall|x: int, y: int| #[trigger] (x * y) == (y * x)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z)
}

/// Proof of basic properties of the division given the divisor `n`:
///
/// 1) Adding the denominator to the numerator increases the quotient
/// by 1 and doesn't change the remainder.
///
/// 2) Subtracting the denominator from the numerator decreases the
/// quotient by 1 and doesn't change the remainder.
///
/// 3) The numerator is the same as the result if and only if the
/// numerator is in the half-open range `[0, n)`.
pub proof fn lemma_mod_basics(n: int)
    requires
        n > 0,
    ensures
        forall|x: int| #[trigger] ((x + n) % n) == x % n,
        forall|x: int| #[trigger] ((x - n) % n) == x % n,
        forall|x: int| #[trigger] ((x + n) / n) == x / n + 1,
        forall|x: int| #[trigger] ((x - n) / n) == x / n - 1,
        forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x,
{
    assert forall|x: int| #[trigger] ((x + n) % n) == x % n by {
        lemma_mod_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) % n) == x % n by {
        lemma_mod_sub_denominator(n, x);
        assert((x - n) % n == x % n);
    };
    assert forall|x: int| #[trigger] ((x + n) / n) == x / n + 1 by {
        lemma_div_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) / n) == x / n - 1 by {
        lemma_div_sub_denominator(n, x);
    };
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        lemma_mod_below_denominator(n, x);
    };
}

/// Proof that if `x == q * r + n` and `0 <= r < n`, then `q == x / n`
/// and `r == x % n`. Essentially, this is the converse of the
/// fundamental theorem of division and modulo.
pub proof fn lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires
        n > 0,
        0 <= r < n,
        x == q * n + r,
    ensures
        q == x / n,
        r == x % n,
    decreases
            (if q > 0 {
                q
            } else {
                -q
            }),
{
    lemma_mod_basics(n);
    if q > 0 {
        lemma_mul_is_distributive_add_nonlinear(n, q - 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q - 1) * n + n + r);
        lemma_quotient_and_remainder(x - n, q - 1, r, n);
    } else if q < 0 {
        lemma_mul_is_distributive_sub(n, q + 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q + 1) * n - n + r);
        lemma_quotient_and_remainder(x + n, q + 1, r, n);
    } else {
        lemma_small_div_nonlinear();
        assert(r / n == 0);
    }
}

/// Proof that multiplication is always commutative
proof fn lemma_mul_commutes()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
{
}

/// Proof that multiplication distributes over addition and over
/// subtraction
#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z),
        forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();
    assert forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z) by {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall|i: int| i >= 0 && #[trigger] f1(i) implies #[trigger] f1(add1(i, 1)) by {
            assert((x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f1(i) implies #[trigger] f1(sub1(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));
    }
    assert forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall|i: int| i >= 0 && #[trigger] f2(i) implies #[trigger] f2(add1(i, 1)) by {
            assert((x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f2(i) implies #[trigger] f2(sub1(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };
        lemma_mul_induction(f2);
        assert(f2(y));
    }
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of nonnegative
/// values of `x`.
proof fn lemma_induction_helper_pos(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x >= 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases x,
{
    if (x >= n) {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert(f(add1(x - n, n)));
        assert(f((x - n) + n));
    }
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of negative
/// values of `x`.
proof fn lemma_induction_helper_neg(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x < 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases -x,
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    } else {
        lemma_induction_helper_neg(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    }
}


/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `0 <= i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// is thus simply `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, n))`.
/// `add1(i, n)` is just `i + n`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i < n`, `f(i) ==> f(sub1(i, n))`.
/// `sub1(i, n)` is just `i - n`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_induction_helper(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    } else {
        lemma_induction_helper_neg(n, f, x);
    }
}

/// Proof that when dividing, adding the denominator to the numerator
/// doesn't change the remainder. Specifically, for the given `n` and
/// `x`, `(x + n) % n == x % n`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(n * zp == n * ((x + n) / n - x / n) - n) by {
        assert(n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
            lemma_mul_is_distributive_auto();
        };
    };
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    }
    if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    }
}

/// Proof that when dividing, subtracting the denominator from the
/// numerator doesn't change the remainder. Specifically, for the
/// given `n` and `x`, `(x - n) % n == x % n`.
pub proof fn lemma_mod_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    lemma_mul_is_distributive_auto();  // OBSERVE
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}

/// Proof that when dividing, adding the denominator to the numerator
/// increases the result by 1. Specifically, for the given `n` and `x`,
/// `(x + n) / n == x / n + 1`.
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) / n == x / n + 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by { lemma_mul_auto() };
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    }
    if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    }
}


/// Proof that when dividing, subtracting the denominator from the numerator
/// decreases the result by 1. Specifically, for the given `n` and `x`,
/// `(x - n) / n == x / n - 1`.
pub proof fn lemma_div_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) / n == x / n - 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}


/// Proof that for the given `n` and `x`, `x % n == x` if and only if
/// `0 <= x < n`.
pub proof fn lemma_mod_below_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        0 <= x < n <==> x % n == x,
{
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        if (0 <= x < n) {
            lemma_small_mod(x as nat, n as nat);
        }
        lemma_mod_range_nonlinear(x, n);
    }
}


/// Proof that multiplication is commutative
pub proof fn lemma_mul_is_commutative_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == (y * x),
{
}


/// Proof that multiplication distributes over subtraction, specifically that
/// `x * (y - z) == x * y - x * z`
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures
        x * (y - z) == x * y - x * z,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over addition by 1 and
/// over subtraction by 1
proof fn lemma_mul_successor()
    ensures
        forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y by {
        lemma_mul_is_distributive_add_nonlinear(y, x, 1);
    }
    assert forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y by {
        assert((x - 1) * y == y * (x - 1));
        lemma_mul_is_distributive_add_nonlinear(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}

/// Proof that multiplication distributes over addition and
/// subtraction, whether the addition or subtraction happens in the
/// first or the second argument to the multiplication
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
}

/// Proof that, since `x <= y` and `z >= 0`, `x * z <= y * z`
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires
        x <= y,
        z >= 0,
    ensures
        x * z <= y * z,
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// Proof that multiplication distributes over addition
pub proof fn lemma_mul_is_distributive_add_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z by {
        lemma_mul_is_distributive_add_nonlinear(x, y, z);
    }
}

/// Proof that multiplication distributes over subtraction
pub proof fn lemma_mul_is_distributive_sub_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z by {
        lemma_mul_is_distributive_sub(x, y, z);
    }
}


/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate `f`, proves
/// the predicate holds in the base case of 0, and proves correctness
/// of inductive steps both upward and downward from the base case.
/// This lemma invokes induction to establish that the predicate holds
/// for the given integer `x`.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i`, `is_le(0, i)` implies `f(i) ==>
/// f(i + 1)`.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i`, `is_le(i, 0)` implies `f(i) ==>
/// f(i - 1)`.
pub proof fn lemma_mul_induction_auto(x: int, f: spec_fn(int) -> bool)
    requires
        mul_auto() ==> {
            &&& f(0)
            &&& (forall|i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
            &&& (forall|i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))
        },
    ensures
        mul_auto(),
        f(x),
{
    lemma_mul_auto();
    assert(forall|i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert(forall|i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

/// Proof that when integer `x` is divided by positive integer `m`,
/// the remainder is nonegative and less than `m`.
pub proof fn lemma_mod_bound(x: int, m: int)
    requires
        0 < m,
    ensures
        0 <= x % m < m,
{
    lemma_mod_range_nonlinear(x, m);
}


}
