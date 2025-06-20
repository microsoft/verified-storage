#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

    pub proof fn lemma_mod_auto_basics(n: int, x: int)
        requires
            n > 0
        ensures
            (x + n) % n == x % n,
            (x - n) % n == x % n,
            (x + n) / n == x / n + 1,
            (x - n) / n == x / n - 1,
            0 <= x < n <==> x % n == x,
    {
        lemma_fundamental_div_mod(x, n);
        lemma_fundamental_div_mod(x + n, n);
        lemma_fundamental_div_mod(x - n, n);
        let zp = (x + n) / n - x / n - 1;
        let zm = (x - n) / n - x / n + 1;
        lemma_mul_is_distributive_sub(n, (x + n) / n, x / n + 1);
        lemma_mul_is_distributive_add(n, x / n, 1);
        assert (n * zp == n * ((x + n) / n) - n * (x / n) - n * 1);
        assert (0 == n * zp + ((x + n) % n) - (x % n));
        lemma_mul_is_distributive_sub(n, (x - n) / n, x / n - 1);
        lemma_mul_is_distributive_sub(n, x / n, 1);
        assert (n * zm == n * ((x - n) / n) - n * (x / n) + n * 1);
        assert (0 == n * zm + ((x - n) % n) - (x % n));
        if (zp > 0) { lemma_mul_inequality(1, zp, n); }
        if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
        if (zp == 0) { lemma_mul_by_zero_is_zero(n); }
        if (zm > 0) { lemma_mul_inequality(1, zm, n); }
        if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
        if 0 <= x < n {
            lemma_basic_div_specific_divisor(n);
        }
    }

    pub proof fn lemma_div_relation_when_mods_have_same_order(d: int, x: int, y: int)
        requires
            d > 0,
            x < y,
            y - x <= d,
            x % d < y % d
        ensures
            y / d == x / d
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);

        lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
        lemma_mul_is_commutative(y / d, d);
        lemma_mul_is_commutative(x / d, d);

        if (y / d) > (x / d) {
            lemma_mul_inequality(1, (y / d) - (x / d), d);
            assert (((y / d) - (x / d)) * d >= 1 * d);
            assert ((y / d) * d - (x / d) * d >= d);
            assert (false);
        }
        if (y / d) < (x / d) {
            lemma_mul_inequality((y / d) - (x / d), -1, d);
            assert (((y / d) - (x / d)) * d <= (-1) * d);
            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            assert (false);
        }
    }

    pub proof fn lemma_div_relation_when_mods_have_same_order_alt(d: int, x: int, y: int)
        requires
            d > 0,
            x <= y,
            y - x < d,
            x % d <= y % d
        ensures
            y / d == x / d
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);

        lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
        lemma_mul_is_commutative(y / d, d);
        lemma_mul_is_commutative(x / d, d);

        if (y / d) > (x / d) {
            lemma_mul_inequality(1, (y / d) - (x / d), d);
            assert (((y / d) - (x / d)) * d >= 1 * d);
            assert (false);
        }
        if (y / d) < (x / d) {
            lemma_mul_inequality((y / d) - (x / d), -1, d);
            assert (((y / d) - (x / d)) * d <= (-1) * d);
            assert (false);
        }
    }

    pub proof fn lemma_div_relation_when_mods_have_different_order(d: int, x: int, y: int)
        requires
            d > 0,
            x < y,
            y - x <= d,
            y % d <= x % d
        ensures
            y / d == x / d + 1
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);

        lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
        lemma_mul_is_commutative(y / d, d);
        lemma_mul_is_commutative(x / d, d);

        if (y / d) > (x / d) + 1 {
            lemma_mul_inequality(2, (y / d) - (x / d), d);
            assert (((y / d) - (x / d)) * d >= 2 * d);
            assert (false);
        }
        if (y / d) <= (x / d) {
            lemma_mul_inequality(0, (x / d) - (y / d), d);
            assert (0 * d <= ((x / d) - (y / d)) * d);
            lemma_mul_is_commutative((x / d) - (y / d), d);
            lemma_mul_is_distributive_sub(d, x / d, y / d);
            assert (d * ((x / d) - (y / d)) == d * (x / d) - d * (y / d));
            assert (0 * d <= x - y - x % d + y % d);
            assert (false);
        }
    }

    pub proof fn lemma_div_relation_when_mods_have_different_order_alt(d: int, x: int, y: int)
        requires
            d > 0,
            x <= y,
            y - x < d,
            y % d < x % d
        ensures
            y / d == x / d + 1
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);

        lemma_mul_is_commutative(y / d, d);
        lemma_mul_is_commutative(x / d, d);

        if (y / d) > (x / d) + 1 {
            lemma_mul_inequality(2, (y / d) - (x / d), d);
            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            assert (((y / d) - (x / d)) * d >= 2 * d);
            assert (false);
        }
        if (y / d) <= (x / d) {
            lemma_mul_inequality(0, (x / d) - (y / d), d);
            assert (0 * d <= ((x / d) - (y / d)) * d);
            lemma_mul_is_commutative((x / d) - (y / d), d);
            lemma_mul_is_distributive_sub(d, x / d, y / d);
            assert (d * ((x / d) - (y / d)) == d * (x / d) - d * (y / d));
            assert (0 * d <= x - y - x % d + y % d);
            assert (false);
        }
    }

    pub proof fn lemma_mod_between(d: int, x: int, y: int, z: int)
        requires
            d > 0,
            x % d < y % d,
            y - x <= d,
            x <= z <= y
        ensures
            x % d <= z % d <= y % d
    {
        if y - x == d {
            lemma_mod_auto_basics(d, x);
            assert (y % d == x % d);
            assert (false);
        }
        else {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_fundamental_div_mod(z, d);
            assert (d * (y / d) - d * (x / d) + y % d - x % d < d);
            assert (d * (y / d) - d * (x / d) < d);
            lemma_mul_is_distributive_sub(d, (y / d), (x / d));
            assert (d * ((y / d) - (x / d)) < d);

            lemma_div_relation_when_mods_have_same_order(d, x, y);

            let z_mod_d = x % d + (z - x);
            assert (z == (x / d) * d + z_mod_d) by {
                assert (z == d * (x / d) + z_mod_d);
                lemma_mul_is_commutative(d, (x / d));
            }
            lemma_fundamental_div_mod_converse(z, d, (x / d), z_mod_d);
        }
    }

    pub proof fn lemma_mod_not_between(d: int, x: int, y: int, z: int)
        requires
            d > 0,
            y % d < x % d,
            y - x <= d,
            x <= z <= y
        ensures
            z % d <= y % d || z % d >= x % d
    {
        if y - x == d {
            lemma_mod_auto_basics(d, x);
            assert (y % d == x % d);
            assert (false);
        }
        else {
            lemma_fundamental_div_mod(x, d);
            lemma_fundamental_div_mod(y, d);
            lemma_fundamental_div_mod(z, d);
            assert (d * (y / d) - d * (x / d) + y % d - x % d >= 0);
            assert (d * (y / d) - d * (x / d) >= 0);
            lemma_mul_is_distributive_sub(d, (y / d), (x / d));
            assert (d * ((y / d) - (x / d)) >= 0);

            lemma_div_relation_when_mods_have_different_order(d, x, y);

            if y % d < z % d < x % d {
                lemma_div_relation_when_mods_have_different_order(d, z, y);
                lemma_div_relation_when_mods_have_same_order(d, z, x);
                assert (false);
            }
        }
    }

    pub proof fn lemma_mod_addition_when_bounded(x: int, y: int, d: int)
        requires
            d > 0,
            y >= 0,
            (x % d) + y < d,
        ensures
            (x + y) % d == (x % d) + y
    {
        lemma_fundamental_div_mod(x, d);
        lemma_mul_is_commutative(x / d, d);
        lemma_fundamental_div_mod_converse(x + y, d, x / d, x % d + y);
    }

    pub proof fn lemma_mod_difference_equal(x: int, y: int, d: int)
        requires
            d > 0,
            x <= y,
            x % d <= y % d,
            y - x < d
        ensures
            y % d - x % d == y - x
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);

        assert (d * (y / d) - d * (x / d) + y % d - x % d == y - x);
        lemma_mul_is_distributive_sub(d, y / d, x / d);
        assert (d * (y / d - x / d) + y % d - x % d == y - x);
        assert (0 <= d * (y / d - x / d) + y % d - x % d < d);
        lemma_div_relation_when_mods_have_same_order_alt(d, x, y);
        assert (y / d == x / d);
    }

    pub proof fn lemma_mod_wrapped_len(x: int, y: int, d: int)
        requires
            d > 0,
            x <= y,
            x % d > y % d,
            y - x < d
        ensures
            d - (x % d) + (y % d) == y - x
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);
        assert (d * (y / d) - d * (x / d) + y % d - x % d == y - x);
        lemma_mul_is_distributive_sub(d, y / d, x / d);
        assert (d * (y / d - x / d) + y % d - x % d == y - x);
        assert (0 <= d * (y / d - x / d) + y % d - x % d < d);
        lemma_div_relation_when_mods_have_different_order_alt(d, x, y);
        assert (y / d == x / d + 1);
        assert (y / d - x / d == 1 ==> d * (y / d - x / d) == d) by (nonlinear_arith);
    }

    pub proof fn lemma_mod_equal(x: int, y: int, d: int)
        requires
            d > 0,
            x <= y,
            x % d == y % d,
            y - x < d
        ensures
            x == y
    {
        lemma_mod_difference_equal(x, y, d);
    }

    pub proof fn lemma_mod_equal_converse(x: int, y: int, d: int)
        requires 
            d > 0,
            x == y,
        ensures 
            x % d == y % d
    {}

    pub proof fn lemma_mod_not_equal(x: int, y: int, d: int) 
        requires 
            d > 0,
            y - x < d,
            y - x >= 0,
            x != y,
        ensures 
            x % d != y % d
    {
        if x % d == y % d {
            if x < y {
                lemma_mod_equal(x, y, d);
                assert(false);
            } else {
                assert(y - x < 0);
                assert(false);
            }
        }

    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_div_equal(x: int, q: int, d: int)
        requires
            q * d <= x < (q + 1) * d
        ensures
            (x / d) == q
    {}

    pub proof fn lemma_mod_subtract(x: int, y: int, d: int)
        requires
            d > 0,
            (x % d) + y >= d,
            0 <= y < d
        ensures
            (x % d) + y - d == (x + y) % d
    {
        assert(d <= (x % d) + y < 2 * d);
        assert((x / d) * d + d <= (x / d) * d + (x % d) + y < (x / d) * d + 2 * d);
        lemma_fundamental_div_mod(x, d);
        lemma_mul_is_commutative(x / d, d);
        lemma_mul_is_distributive_add_other_way(d, x / d, 1);
        lemma_mul_is_distributive_add_other_way(d, x / d, 2);
        assert((x / d + 1) * d <= x + y < (x / d + 2) * d);
        lemma_mul_div_equal(x + y, (x / d + 1), d);
        assert(x / d + 1 == (x + y) / d);
        lemma_fundamental_div_mod(x + y, d);
        assert(x + y == d * ((x + y) / d) + (x + y) % d);
    }

}
