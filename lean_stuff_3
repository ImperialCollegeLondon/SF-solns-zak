--#check list.reverse
--#check list
namespace z

inductive nt: Type
| zero : nt
| succ : nt → nt

definition add_n : nt → nt → nt
| nt.zero x := x
| (nt.succ x) y := nt.succ (add_n x y)

definition product_n : nt → nt → nt
| x (nt.succ nt.zero) := x
| _ nt.zero := nt.zero
| x (nt.succ y) := add_n x (product_n x y)

definition eq_n : nt → nt → bool
| nt.zero nt.zero := tt
| (nt.succ a) (nt.succ b) := eq_n a b
| _ _ := ff




inductive nat_pair : Type 
| p : nat → nat → nat_pair

open nat_pair
notation a ; b := p a b

#check p 5 5 

def fst : nat_pair → nat
| (p x _) := x

def snd : nat_pair → nat
| (p _ x) := x

def first_or_second : nat_pair → bool → nat
| (p x _) ff := x
| (p _ x) tt := x

def swap : nat_pair → nat_pair
| (x;y)  := y;x



theorem surjective_pairing : ∀ (n m : nat), (n;m) = 
((first_or_second (n;m) ff) ; (first_or_second (n;m) tt)) := begin

intros n m,

have H₁ : ∀ n m : ℕ, first_or_second (n;m) ff = n,
{
    unfold first_or_second,
    intro h,
    intro g,
    refl
},
{
    rw H₁,
    have H₂ : ∀ n m : ℕ, first_or_second (n;m) tt = m,
    {
        unfold first_or_second,
        intro h, intro g, refl
    },
    rw H₂
}

end


theorem snd_fst_is_swap : ∀ (p : nat_pair),
  (snd p ; fst p) = swap p := begin

  intro p,
  cases p with x y,
  refl

  end

theorem fst_swap_is_snd : ∀ (p : nat_pair),
  fst (swap p) = snd p := begin

  intro p,
  cases p,
  refl

  end


inductive natlist : Type 
| emp : natlist
| ap : nat → natlist → natlist

open natlist
notation {} := emp
notation x :: y := ap x y


def repeat : ℕ → ℕ → natlist
|  0 _ := {}
| (n+1) x := ap x (repeat n x)

def len : natlist → ℕ 
| {} := 0
| (ap _ x) := 1 + len x

def append : natlist → natlist → natlist 
| {} x := x
| (ap n L) x := ap n (append L x)

def ap_r : natlist → nat → natlist := λ L n,
append L (ap n {})

def reverse : natlist → natlist
| {} := {}
| (ap n L) := append (reverse L) (n::{})
--ap_r changed to append
--n changed to (n::{})

def first_element : natlist → ℕ
| {} := 0
| (n::L) := n

def last_element : natlist → ℕ
| {} := 0
| (a::{}) := a
| (a::b) := last_element b

def up_to_last : natlist → natlist
| {} := {}
| (a::{}) := {}
| (a::L) := a::(up_to_last L)

def is_odd : ℕ → bool
| 1 := tt
| 0 := ff
| (n+2) := is_odd n

def append_if_odd : ℕ → bool → natlist → natlist
| x tt L := ap x L
| x ff L := L 

def oddmembers : natlist → natlist
| {} := {}
| (ap n L) := append_if_odd n (is_odd n) (oddmembers L)

def count_odd_members : natlist → ℕ
| {} := 0
| L := len (oddmembers L)

def list_zip : natlist → natlist → natlist
| {} {} := {}
-- at least one not empty
| {} L := L
| L {} := L
-- neither empty
| (ap n₁ L₁) (ap n₂ L₂) := ap n₁ (ap n₂ (list_zip L₁ L₂))

def one_if_equal_else_zero : ℕ → ℕ → ℕ
| x y := if x=y then 1 else 0

def count : natlist → ℕ → ℕ
| {} _ := 0
| (ap n L) x := one_if_equal_else_zero x n + (count L x)

def sum_of_list : natlist → ℕ
| {} := 0
| (ap n L) := n + sum_of_list L

def sum := append
def add := ap

def member : natlist → ℕ → bool
| {} _ := false
| (ap n L) x := if n=x then tt else member L x

def remove_one : natlist → ℕ → natlist
| {} _ := {}
| (ap n L) x := if n=x then L else ap n (remove_one L x)

def remove_all : natlist → ℕ → natlist
| {} _ := {}
| (ap n L) x := if n=x then remove_all L x else ap n (remove_all L x)

def to_set : natlist → natlist
| {} := {}
| (ap n L) := if count L n = 0 then ap n (to_set L) else to_set L

def is_a_subset_of_b : natlist → natlist → bool
| {} _ := tt
| (a::L) x := if count L a < count x a then is_a_subset_of_b L x else ff

-- ascending order
definition sort_into_list : natlist → ℕ → natlist
| {} x := x::{}
| (n::L) x := if n>=x then (x::n::L) else append (n::{}) (sort_into_list L x)

-- sort             a   into  b={}
definition SORT : natlist → natlist → natlist
| {} x := x
| (n::L) x := SORT L (sort_into_list x n)

definition sort_list : natlist → natlist := λ n, SORT n {}

-- only equal if same values in same places
definition list_equality : natlist → natlist → bool
| {} {} := tt
| (ap a L1) (ap b L2) := if a=b then list_equality L1 L2 else ff
| _ _ := ff

definition same_values : natlist → natlist → bool := 
λ a b, list_equality (sort_list a) (sort_list b)


@[derive decidable_eq] inductive nat_error : Type
| Some : nat → nat_error
| None : nat_error
open nat_error

definition nth_in_list : natlist → ℕ → nat_error
| {} _ := None
| (x::L) 0 := Some x
| (x::L) (nat.succ n) := nth_in_list L n

theorem a : ∀ n y:ℕ, count (repeat n y) y = n := begin intros n y,
induction n with d Hd,
{
    refl
},
{
    unfold repeat,
    unfold count,
    unfold one_if_equal_else_zero,
    rw Hd,
    simp
} end

theorem b : ∀ a b : ℕ, sum_of_list (repeat a b) = a*b := begin intros a b,
induction a with d Hd,
{
    simp,
    cases b;refl
},
{
    unfold repeat,
    unfold sum_of_list,
    rw Hd,
    simp,

    rw mul_add b d 1, simp
} end

@[simp] theorem count_append (a L : natlist) (n : ℕ) : 
count (append a L) n = count a n + count L n :=begin induction a with new L₂ Hd,
{
    unfold count append,
    simp
},
{
    unfold append count one_if_equal_else_zero ,
    by_cases (n=new),
    {
        simp [h],
        --clear h,
        congr,
        rw h at Hd,
        rw Hd,
        simp
    },
    {
        simp [h],
        rw Hd,
        simp
    }
} end

@[simp] theorem c : ∀ L : natlist, ∀ n:ℕ, count (reverse L) n = count L n := begin
intros L n,
induction L with new L₂ H₁, {refl},
{
    by_cases (n=new),
    {
        unfold reverse ap_r count one_if_equal_else_zero,
        subst h, simp,
        unfold count one_if_equal_else_zero,
        simp, congr,
        rw H₁
    },
    {
        unfold reverse count ap_r one_if_equal_else_zero,
        simp [h],
        unfold reverse count ap_r one_if_equal_else_zero,
        simp [h],
        rw H₁
    }
}
end

@[simp] theorem append_unchanged : ∀ a : natlist, append a {} = a := begin
intro a,
induction a,{refl},
{
    unfold append,
    rw ih_1
} end


@[simp] theorem append_ass : ∀ a b c : natlist, 
append (append a b) c = append a (append b c) := begin
intros a b c,
induction a,
{
    refl
},
{
    unfold append,
    rw ih_1
} end 


@[simp]theorem d: ∀ L₁ L₂ : natlist,
  reverse (append L₁ L₂) = append (reverse L₂) (reverse L₁) := begin
  intros L₁ L₂,
  induction L₁ with new L H,
  {
      unfold reverse,
      unfold append,
      simp
  },
  {
      unfold append reverse ap_r,
      rw H,
      exact append_ass (reverse L₂) (reverse L)(new :: {})
  } end


-- [1,2,3] [4,5,6]
-- [3,2,1] [6,5,4]
-- [3,2,1,6,5,4]
-- [4,5,6,1,2,3]

theorem e : ∀ L : natlist, reverse (reverse L) = L := begin
intro L,
induction L with new L_shorter H,{refl},
{
    unfold reverse,
    simp,
    rw H, refl
}
end

@[simp]theorem same_eq : ∀ x : natlist, list_equality x x = tt := begin
intro x,
induction x,{refl},
{
    unfold list_equality,
    simp, rw ih_1
}
end

@[simp]theorem same_eq2 : ∀ x : natlist, same_values x x = tt := begin
intro x, unfold same_values, simp
end

theorem g (L : natlist) (n : ℕ) : same_values (append (n::{}) L) (append L (n::{})) := sorry


theorem t : 1=1 := begin

by_cases (Some 5 = None),
{
    admit
},
{
    admit
}

end



theorem f : ∀ L : natlist, same_values L (reverse L) = tt := begin

intro L,
induction L with new L_shorter H,{refl},
{
    unfold reverse,
    
    -- new + L == L_r + new
    --unfold same_values sort_into_list
    --list_equality sort_into_list,
    --unfold same_values sort_into_list
    --list_equality sort_into_list at H,

    admit

}

end 

end z
