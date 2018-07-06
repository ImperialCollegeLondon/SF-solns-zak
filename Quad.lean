-- ax^2 + bx + c = 0
-- x^2 + bx/a + c/a = 0
-- x^2 + bx/a = - c/a
-- (x + b/2a)^2 - b^2/4a^2 = -c/a
-- (x + b/2a)^2 = b^2/4a^2 - c/a
--              = b^2 - 4ac / 4a^2
-- x + b/2a     =  S / 2a ∨ -S / 2a
-- x            = -b/2a + S ∨ -b/2a - S 

import tactic.ring
import tactic.find 

#check id 
#find _ / _ * _ = _ * _ / _ 



theorem quad (k : Type) [field k] (a b c x S : k)
(HS : S*S = b*b - 4*a*c) (char_not_2 : (2:k) ≠ 0) (a_not_0 : a ≠ 0) :
a * x*x + b * x + c = 0 ↔ 
(x = (-b + S ) / (2*a) ∨ 
 x = (-b - S ) / (2*a)) := begin

split,{sorry},
{
    intro H,
    cases H,
    {
        subst H,
        
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

        apply eq_of_mul_eq_mul_right H₂,
        simp [add_mul],

        rw ←mul_div_assoc b (S + - b) (2 * a),
        rw ←mul_div_assoc,
        rw ←mul_div_assoc,

        rw div_mul_cancel _ H₂,
        rw div_mul_cancel _ H₂,
        
        apply eq_of_mul_eq_mul_right H₂,
        simp [add_mul],

        rw ←add_assoc,

        rw div_mul_eq_mul_div,
rw div_mul_cancel _ H₂,
ring,
rw pow_two S,
rw HS,
ring
        -- a * (b/c) = (a*b)/c


    },{sorry}
}

end
