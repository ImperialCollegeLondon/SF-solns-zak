import tactic.ring


-- intermediate lemmas, many of which probably already existed
-- always made inputs of type k explicit for clarity
-- naming very random

theorem mul_eq_implies_mul_mul {k : Type} [field k] (a b c : k):
a=b → a*c = b*c := begin
intro H, rw H
end

theorem add_eq_implies_add_add {k : Type} [field k] (a b c : k):
a=b → a+c = b+c := begin
intro H, rw H
end

theorem move_sides {k : Type} [field k] (a b : k) :
a + b = 0 → a = - b :=
begin
intro H,
have H₁ := @eq_of_add_eq_add_left k _ b a (-b),
rw H₁, simp, exact H
end

theorem eq_implies_sq_eq {k : Type} [field k] (a b : k) :
a = b ∨ a = -b → a^2 = b^2 := begin

intro H,
unfold pow monoid.pow, simp,
cases H;rw H,
simp

end

theorem factorise_a_sq_minus_b_sq {k : Type} [field k] (a b : k) :
a^2 - b^2 = (a-b) * (a+b) := begin
ring
end

theorem add_neg_eq_sub {k : Type} [field k] (a b : k) :
a + - (b) = a - b := begin
refl
end

theorem sq_eq_implies_eq_or_neg_eq {k : Type} [field k] (a b : k) :
a^2 = b^2 → a = b ∨ a = -b := begin

intro H,
have rearrange_H := @add_eq_of_eq_add_neg k _ (a*a) (-(b*b)) 0,
simp at rearrange_H,

rw ←pow_two at rearrange_H, rw ←pow_two at rearrange_H,

rw add_neg_eq_sub (a^2) (b^2) at rearrange_H,
rw factorise_a_sq_minus_b_sq at rearrange_H,

rw H at rearrange_H, simp at rearrange_H,

have H_zero := @mul_eq_zero k _ (a +- b) (a + b),
rw rearrange_H at H_zero, simp at H_zero,
cases H_zero,
{
    rw add_neg_eq_zero at H_zero,
    exact or.inl H_zero,
},
{
    rw add_comm at H_zero,
    rw add_eq_zero_iff_neg_eq at H_zero,
    right,
    exact H_zero.symm
}

end

theorem multiply_out_divide {k : Type} [field k] (a b c: k) (H_neq : c ≠ 0) :
a * c = b → a = b / c := begin
intro H,
have H₁ :=  @eq_of_mul_eq_mul_left k _ c a (b/c) H_neq,
rw H₁,
--rw mul_comm c (b/c),
rw mul_div_cancel' b H_neq,
rw ←H,
exact mul_comm c a

end



theorem quad (k : Type) [field k] (a b c x S : k)
(HS : S*S = b*b - 4*a*c) (char_not_2 : (2:k) ≠ 0) (a_not_0 : a ≠ 0) :
a * x*x + b * x + c = 0 ↔ 
(x = (-b + S ) / (2*a) ∨ 
 x = (-b - S ) / (2*a)) := begin

have H₁  := @eq_zero_or_eq_zero_of_mul_eq_zero _ _ 2 a,
have H₂  : 2 * a ≠ 0,
{
    intro H₃,
    cases H₁ H₃,
    {
        revert h,
        exact char_not_2
    },
    {
        revert h, exact a_not_0
    }
},

clear H₁, clear a_not_0,

split,
-- ax^2 + bx + c = 0 → x=...
{
    intro H_main,

    have H_equate_squares : (2*a*x + b)^2 = S^2,
    {
        rw pow_two,
        rw pow_two,

        rw HS,
        repeat {rw mul_add},
        repeat {rw add_mul},

        simp,
        have H_mul_comm : b * (2 * a * x) = 2 * a * x * b,{rw mul_comm},
        rw H_mul_comm,
        rw ←add_assoc,
        rw ←mul_two (2*a*x*b),
        ring,
        have H_neg_mul_comm : -(4 * c * a) = -(4 * c) * a,{ring},
        rw H_neg_mul_comm, clear H_neg_mul_comm,

        have H_cancel_a :=
        mul_eq_implies_mul_mul (4 * x ^ 2 * a + 4 * x * b) (-(4 * c)) a,
        
        apply H_cancel_a, clear H_cancel_a,
        
        rw ←mul_neg_eq_neg_mul_symm 4 c,
        rw mul_assoc 4 x b,
        rw mul_assoc 4 (x^2) a,
        rw ←mul_add 4 (x^2*a) (x*b),
        congr,
        unfold pow monoid.pow, simp,

        have H_move_sides :=
        move_sides (x * b + x * x * a) c,
        rw H_move_sides, clear H_move_sides,

        --lots of shuffling about to get the goal to look like H_main
        
        rw add_comm,
        rw ←pow_two,
        rw mul_comm,
        rw mul_comm (x^2) a,
        
        simp at H_main,

        rw pow_two,

        rw mul_assoc a x x at H_main,
        exact H_main
    },

    have H_sq_eq := sq_eq_implies_eq_or_neg_eq (2 * a * x + b) S,
    rw H_equate_squares at H_sq_eq, simp at H_sq_eq,
    rw add_comm at H_sq_eq,

    cases H_sq_eq,
    {
        left,
        have H_mul_out_1 := multiply_out_divide x (-b + S) (2*a) H₂,
        rw H_mul_out_1, clear H_mul_out_1,
        rw mul_comm,

        suffices H_add_b : 2*a*x + b = S,
        {
            rw ←H_add_b,simp
        },

        exact H_sq_eq
    },
    {
        right,
        have H_mul_out_2 := multiply_out_divide x (-b - S) (2*a) H₂,
        rw H_mul_out_2, clear H_mul_out_2,
        rw mul_comm,

        suffices H_add_b : 2*a*x + b = -S,
        {
            rw ←add_neg_eq_sub,
            rw ←H_add_b,simp
        },

        exact H_sq_eq
    }

},
-- x=... → ax^2 + bx + c
{
    intro H,
    cases H,

    repeat --works for both cases -b - S and - b + S
    {
        subst H,
        
        
        apply eq_of_mul_eq_mul_right H₂,
        simp [add_mul],

        repeat {rw ←mul_div_assoc},
        repeat {rw div_mul_cancel _ H₂},
        
        apply eq_of_mul_eq_mul_right H₂,
        simp [add_mul],

        rw ←add_assoc,

        rw div_mul_eq_mul_div,

        rw div_mul_cancel _ H₂,
        ring,
        rw pow_two S,
        rw HS,
        ring
    },
    
}

end
