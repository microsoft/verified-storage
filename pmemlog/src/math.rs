#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    /*
      From Ironfleet's math library's mul_nonlinear.i.dfy
    */

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_strictly_positive(x: int, y: int)
        ensures
            (0 < x && 0 < y) ==> (0 < x*y)
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_nonzero(x: int, y: int)
        ensures
            x*y != 0 <==> x != 0 && y != 0
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
        ensures
            x * (y * z) == (x * y) * z
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
        ensures
            x*(y + z) == x*y + x*z
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_ordering(x: int, y: int)
        requires
            0 < x,
            0 < y,
            0 <= x*y
        ensures
            x <= x*y && y <= x*y
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
        requires
            x < y,
            z > 0
        ensures
            x*z < y*z
    {
    }

    pub proof fn lemma_mul_by_zero_is_zero(x: int)
        ensures
            0*x == 0,
            x*0 == 0
    {
    }

    /*
      From Ironfleet's math library's mul.i.dfy
    */

    #[verifier(opaque)]
    pub open spec fn mul_pos(x: int, y: int) -> int
        recommends
            x >= 0
        decreases
            x
    {
        if x <= 0 {
            0
        }
        else {
            y + mul_pos(x - 1, y)
        }
    }

    pub open spec fn mul_recursive(x: int, y: int) -> int
    {
        if x >= 0 {
            mul_pos(x, y)
        }
        else {
            -1 * mul_pos(-1 * x, y)
        }
    }

    pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
        requires
            x >= 0
        ensures
            x * y == mul_pos(x, y)
        decreases
            x
    {
        reveal(mul_pos);
        if x > 0 {
            lemma_mul_is_mul_pos(x - 1, y);
            lemma_mul_is_distributive_add_other_way(y, x - 1, 1);
            assert (x * y == (x - 1) * y + y);
        }
    }

    pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
        ensures
            x * y == mul_recursive(x, y)
    {
        if (x >= 0) {
            lemma_mul_is_mul_pos(x, y);
        }
        else if (x <= 0) {
            lemma_mul_is_mul_pos(-x, y);
            lemma_mul_is_associative(-1, -x, y);
        }
    }

    pub proof fn lemma_mul_basics(x: int)
        ensures
            0 * x == 0,
            x * 0 == 0,
            1 * x == x,
            x * 1 == x
    {
    }

    pub proof fn lemma_mul_is_commutative(x: int, y: int)
        ensures
            x * y == y * x
    {
    }

    pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
        requires
            x <= y,
            z >= 0,
        ensures
            x * z <= y * z
        decreases
            z
    {
        if z > 0 {
            lemma_mul_inequality(x, y, z - 1);
            lemma_mul_is_distributive_add(x, z - 1, 1);
            lemma_mul_basics(x);
            assert (x * z == x * (z - 1) + x);
            lemma_mul_is_distributive_add(y, z - 1, 1);
            lemma_mul_basics(y);
            assert (y * z == y * (z - 1) + y);
        }
    }

    pub proof fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
        requires
            x <= x_bound,
            y <= y_bound,
            0 <= x,
            0 <= y
        ensures
            x * y <= x_bound * y_bound
    {
        lemma_mul_inequality(x, x_bound, y);
        lemma_mul_inequality(y, y_bound, x_bound);
    }

    /// This lemma is less precise than the non-strict version, since
    /// it uses two < facts to achieve only one < result. Thus, use it with
    /// caution -- it may be throwing away precision you'll require later.
    #[verifier(nonlinear)]
    pub proof fn lemma_mul_strict_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
        requires
            x < x_bound,
            y < y_bound,
            0 <= x,
            0 <= y
        ensures
            x * y < x_bound * y_bound
        decreases
            y
    {
        lemma_mul_upper_bound(x, x_bound - 1, y, y_bound - 1);
        assert ((x_bound - 1) * (y_bound - 1) == x_bound * y_bound - y_bound - x_bound + 1);
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
        requires
            x > 0
        ensures
            y <= z ==> x * y <= x * z,
            y < z ==> x * y < x * z
        decreases
            x
    {
        if x > 1 {
            lemma_mul_left_inequality(x - 1, y, z);
            assert (x * y == (x - 1) * y + y);
            assert (x * z == (x - 1) * z + z);
        }
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
        requires
            x*z <= y*z,
            z > 0
        ensures
            x <= y
        decreases
            z
    {
        if z > 1 {
            if (x * (z - 1) <= y * (z - 1)) {
                lemma_mul_inequality_converse(x, y, z - 1);
            }
            else {
                lemma_mul_inequality_converse(y, x, z - 1);
                assert (false);
            }
        }
    }

    pub proof fn lemma_mul_equality_converse(x: int, y: int, z: int)
        requires
            x*z == y*z,
            0<z
        ensures
            x==y
    {
        lemma_mul_inequality_converse(x, y, z);
        lemma_mul_inequality_converse(y, x, z);
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
        ensures
            (y + z)*x == y*x + z*x
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
        ensures
            x*(y - z) == x*y - x*z
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_distributive_sub_other_way(x: int, y: int, z: int)
        ensures
            (y - z)*x == y*x - z*x
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
        ensures
            x*(y + z) == x*y + x*z,
            x*(y - z) == x*y - x*z,
            (y + z)*x == y*x + z*x,
            (y - z)*x == y*x - z*x,
            x*(y + z) == (y + z)*x,
            x*(y - z) == (y - z)*x,
            x*y == y*x,
            x*z == z*x
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_strictly_increases(x: int, y: int)
        requires
            1 < x,
            0 < y
        ensures
            y < x*y
    {
        assert (x * y == (x - 1) * y + y);
        lemma_mul_strictly_positive(x - 1, y);
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_increases(x: int, y: int)
        requires
            0<x,
            0<y
        ensures
            y <= x*y
        decreases
            x
    {
        if x > 1 {
            lemma_mul_increases(x - 1, y);
            assert (x * y == (x - 1) * y + y);
        }
    }

    pub proof fn lemma_mul_nonnegative(x: int, y: int)
        requires
            0 <= x,
            0 <= y
        ensures
            0 <= x*y
    {
        if x != 0 && y != 0 {
            lemma_mul_strictly_positive(x, y);
        }
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_unary_negation(x: int, y: int)
        ensures
            (-x)*y == -(x*y),
            -(x*y) == x*(-y)
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_mul_one_to_one(m: int, x: int, y: int)
        requires
            m!=0,
            m*x == m*y
        ensures
            x == y
    {
        if m > 0 {
            if x < y {
                lemma_mul_strict_inequality(x, y, m);
            }
            if x > y {
                lemma_mul_strict_inequality(y, x, m);
            }
        }
        else {
            assert (x * m == -(x * -m));
            assert (y * m == -(y * -m));
            if x < y {
                lemma_mul_strict_inequality(x, y, -m);
            }
            if x > y {
                lemma_mul_strict_inequality(y, x, -m);
            }
        }
    }

    /*
      From Ironfleet's math library's div_nonlinear.i.dfy
    */

    pub proof fn lemma_div_of_0(d: int)
        requires
            d != 0
        ensures
            0int / d == 0
    {
    }

    pub proof fn lemma_div_by_self(d: int)
        requires
              d != 0
        ensures
            d / d == 1
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_small_div(x: int, d: int)
        requires
            0 <= x < d,
            d > 0
        ensures
            x / d == 0
    {
    }

    pub proof fn lemma_mod_of_zero_is_zero(m: int)
        requires
            0 < m
        ensures
            0int % m == 0
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_fundamental_div_mod(x: int, d: int)
        requires
            d != 0
        ensures
            x == d * (x/d) + (x%d)
    {
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_small_mod(x: int, m: int)
        requires
            0 <= x < m,
            0 < m
        ensures
            x % m == x
    {
    }

    pub proof fn lemma_mod_range(x: int, m: int)
        requires
            m > 0
        ensures
            0 <= x % m < m
    {
    }

    /*
      From Ironfleet's math library's mod_auto_proofs.i.dfy
    */

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
        lemma_mod_range(x, n);
        lemma_fundamental_div_mod(x, n);
        lemma_fundamental_div_mod(x + n, n);
        lemma_fundamental_div_mod(x - n, n);
        lemma_mod_range(x, n);
        lemma_mod_range(x + n, n);
        lemma_mod_range(x - n, n);
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
            lemma_small_div(x, n);
        }
    }

    /*
      From Ironfleet's div.i.dfy
    */

    proof fn lemma_fundamental_div_mod_converse_helper_1(u: int, d: int, r: int)
        requires
            d != 0,
            0 <= r < d
        ensures
            u == (u * d + r) / d
        decreases
            if u >= 0 { u } else { -u }
    {
        if u < 0 {
            lemma_fundamental_div_mod_converse_helper_1(u + 1, d, r);
            lemma_mod_auto_basics(d, u * d + r);
            lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
            assert (u * d + r == (u + 1) * d + r - d);
            assert (u == (u * d + r) / d);
        }
        else if u == 0 {
            lemma_small_div(r, d);
            assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
            assert (u == (u * d + r) / d);
        }
        else {
            lemma_fundamental_div_mod_converse_helper_1(u - 1, d, r);
            lemma_mod_auto_basics(d, (u - 1) * d + r);
            lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
            assert (u * d + r == (u - 1) * d + r + d);
            assert (u == (u * d + r) / d);
        }
    }

    proof fn lemma_fundamental_div_mod_converse_helper_2(u: int, d: int, r: int)
        requires
            d != 0,
            0 <= r < d
        ensures
            r == (u * d + r) % d
        decreases
            if u >= 0 { u } else { -u }
    {
        if u < 0 {
            lemma_fundamental_div_mod_converse_helper_2(u + 1, d, r);
            lemma_mod_auto_basics(d, u * d + r);
            lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
            assert (u * d == (u + 1) * d + (-1) * d);
            assert (u * d + r == (u + 1) * d + r - d);
            assert (r == (u * d + r) % d);
        }
        else if u == 0 {
            assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
            if d > 0 {
                lemma_small_mod(r, d);
            }
            else {
                lemma_small_mod(r, -d);
            }
            assert (r == (u * d + r) % d);
        }
        else {
            lemma_fundamental_div_mod_converse_helper_2(u - 1, d, r);
            lemma_mod_auto_basics(d, (u - 1) * d + r);
            lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
            assert (u * d + r == (u - 1) * d + r + d);
            assert (r == (u * d + r) % d);
        }
    }

    pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
        requires
            d != 0,
            0 <= r < d,
            x == q * d + r
        ensures
            q == x / d,
            r == x % d
    {
        lemma_fundamental_div_mod_converse_helper_1(q, d, r);
        assert (q == (q * d + r) / d);
        lemma_fundamental_div_mod_converse_helper_2(q, d, r);
    }

    /*
      Lemmas we need for this project
    */

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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);

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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);

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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);

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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);

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
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);
            lemma_mod_range(z, d);
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
            lemma_mod_range(x, d);
            lemma_mod_range(y, d);
            lemma_mod_range(z, d);
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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);

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
        lemma_mod_range(x, d);
        lemma_mod_range(y, d);
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
