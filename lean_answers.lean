-- 1
def nandb : bool → bool → bool
| tt tt := ff
| a b := tt

def is_correct : (bool → bool → bool) → bool := 
λ a, (a (ff) (ff) = tt) && (a (ff) (tt) = tt) && (a (tt) (ff) = tt) &&(a (tt) (tt) = ff)

inductive naat: Type
| zro : naat
| suc : naat → naat

def is_even : naat → bool
| naat.zro := tt
| (naat.suc naat.zro) := ff
| (naat.suc (naat.suc n)) := is_even n

def nat_add : naat → naat → naat
| naat.zro x := x
| (naat.suc a) b := naat.suc (nat_add a b)

def nat_double : naat → naat
| naat.zro := naat.zro
| (naat.suc n) := nat_add (naat.suc (naat.suc naat.zro)) (nat_double n)

theorem easy : ∀ n : nat, 2 * (1 + n) = 2 + 2 * n :=
begin
intro n,
rewrite mul_add,
rewrite mul_one,
end 


def nat_eq : naat → naat → bool
| naat.zro naat.zro := tt
| (naat.suc a) (naat.suc b) := nat_eq a b
| _ _ := ff

def a_bigger_than_b : naat → naat → bool
| naat.zro naat.zro := ff
| naat.zro a := ff
| a naat.zro := tt
| (naat.suc a) (naat.suc b) := a_bigger_than_b a b

def factorial : ℕ → ℕ
| 0 := 1
| (nat.succ n) := nat.succ n * factorial n
