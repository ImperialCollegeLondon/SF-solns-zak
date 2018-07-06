--import tactic.ring

theorem m (a b c:ℕ) : (a+b) * c = a * c + b * c := begin
induction c with c H,
{
    refl
},
{
    have H2 := nat.mul_succ,
    rw H2, clear H2,
    have H2 := nat.mul_succ a c,
    rw H2, clear H2,
    have H2 := nat.mul_succ b c,
    rw H2, rw H, simp
}
end

theorem m2 (a b c:ℕ) : c * (a+b) = a * c + b * c := begin
have H := m a b c,
rw ←H, 
apply nat.mul_comm
end

theorem m3 (n:ℕ) : 2*n = n+n :=begin

induction n,{refl},
{
    rw nat.mul_succ 2 n_n,
    rw n_ih,
    have H : nat.succ n_n = n_n + 1, {refl},
    rw H,simp
}

end


theorem a (n:ℕ) : n^2 = n*n := begin
unfold pow nat.pow, simp
end

theorem b (a b:ℕ) : (a+b)^2 = a^2 + b^2 + 2*a*b := 
begin
unfold pow nat.pow,
simp,

have H₁ := m  a b (a+b), rw H₁, clear H₁,
have H₁ := m2 a b a,     rw H₁, clear H₁,
have H₁ := m2 a b b,     rw H₁, clear H₁, simp,

have H₂ : a * b = b * a,
{
    exact nat.mul_comm a b
},

rw ←H₂,

have H₃ : 2 * a * b = a * b + a * b,
{
    have H₄ := m3 (a*b),
    have H₅ : 2 * (a * b) = 2 * a * b,
    {
        rw nat.mul_assoc 2 a b
    },
    {
        rw H₅ at H₄, clear H₅,
        rw H₄
    }
},

rw H₃,
simp
end


theorem c (a n:ℕ) : n^2 + 2*a*n = (n+a)^2 - a^2 := begin

have H := b n a,
rw H,
simp,
have H₂ := nat.add_sub_cancel (n ^ 2 + 2 * n * a) (a^2),
have H₃ : 
a^2 + (n ^ 2 + 2 * n * a) - a^2 = (n ^ 2 + 2 * n * a) + a^2 - a^2,{simp},
rw H₃,
rw H₂,
have H₄ :  2*a*n = 2*n*a,
{
    have H₅ := m3 (a*n),
    clear H H₂ H₃,
    have H₆ : 2*a*n = 2*(a*n),
    {
        exact nat.mul_assoc 2 a n 
    },
    rw H₆, rw H₅,

    have H₅ := m3 (n*a),
    have H₆ : 2*n*a = 2*(n*a),
    {
        exact nat.mul_assoc 2 n a 
    },
    rw H₆, rw H₅,
    
    rw nat.mul_comm a n
},
rw H₄

end




-- ax^2 + bx + c = 0
-- x^2 + bx/a + c/a = 0
-- x^2 + bx/a = - c/a
-- (x + b/2a)^2 - b^2/4a^2 = -c/a
-- (x + b/2a)^2 = b^2/4a^2 - c/a
--              = b^2 - 4ac / 4a^2
-- x + b/2a     =  S ∨ -S
-- x            = -b/2a + S ∨ -b/2a - S 



theorem quad (k : Type) [field k] (a b c x S : k)
(HS : S*S = b*b - 4*a*c) (char_not_2 : (2:k) ≠ 0) :
a * x*x + b * x + c = 0 ↔ 
(x = (-b + S ) / 2*a ∨ 
 x = (-b - S ) / 2*a ) := begin

split,
{
    intro H₁,
}

end
