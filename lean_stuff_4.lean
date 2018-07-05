
namespace z3

inductive List (α : Type) 
| emp {} : List
| ap     : α → List → List

open List
notation {} := emp
notation x :: y := ap x y

definition append : Π {α:Type}, List α → List α → List α 
| α emp L := L
| α (x::L₁) L₂ := x::(append L₁ L₂)

definition repeat : Π {α:Type}, α → ℕ → List α
| α _ 0 := emp
| α x (nat.succ n) := append (x::{}) (repeat x (n))

definition len : Π {α:Type}, List α → ℕ 
| α emp := 0
| α (_::L) := len L + 1

--todo : {} for append

theorem list_app_eq : ∀ α : Type, ∀ L₁ L₂ : List α,
len (append L₁ L₂) = len L₁ + len L₂ := begin
intro α,
intros L₁ L₂,
induction L₁ with new L_shorter H,{unfold append, unfold len, simp},
{
    unfold append,
    unfold len,
    rw H,
    simp
}end

-------------- products -----------------

inductive prodd (α β : Type)
| pair : α → β → prodd
open prodd

def fst : Π {α β : Type}, prodd α β → α
| _ _ (pair x y) := x

def snd : Π {α β : Type}, prodd α β → β
| _ _ (pair x y) := y


def zip : Π {α β : Type}, List α → List β → List (prodd α β)
| α β {} {} := {}
| α β (A::L₁) (B::L₂) := ap (pair A B) (zip L₁ L₂)
-- if different lengths, give up
| _ _ _ _ := {}

def unzip : Π {α β : Type}, List (prodd α β) → prodd (List α) (List β)
| α β {} := pair {} {}
| α β (x::L) := pair (ap (fst x) (fst (unzip L)) ) (ap (snd x) (snd (unzip L)) )

theorem A : ∀ α β:Type, ∀ L₁ L₂:List α, len L₁ = len L₁ → pair L₁ L₂ = unzip (zip L₁ L₂) := begin

intros α β,
intros L₁ L₂,
intro H,
admit

end

inductive option (α : Type)
| None : option
| Some : α → option

def get_nth {α : Type}: List α → ℕ → option α
| {} _ := option.None α
| (x::_) 0 := option.Some x
| (_::y) (nat.succ n) := get_nth y n

def filter : Π {α : Type}, List α → (α → bool) → List α
| α {} _ := {}
| α (x::L) F := if F x = tt then ap x (filter L F) else filter L F

def nat_even : ℕ → bool
| 0 := tt
| 1 := ff
| (nat.succ (nat.succ n)) := nat_even n

def bool_and : bool → bool → bool
| tt tt := tt
| _ _ := ff

def bool_inv : bool → bool
| tt := ff
| _ := tt

def gt (a b : ℕ) : bool := if a > b then tt else ff
def task (L₁ : List ℕ) : List ℕ := filter L₁ (λ n, bool_and (nat_even n) (gt n 7)  ) 

def inverse_func : Π {α : Type}, (α → bool) → (α → bool) := 
--λ α F, λ b, bool_inv (F b)
λ α F, bool_inv ∘ F

-- f ∘ g = λ b, f (g b)

def partition : Π {α : Type}, (α → bool) → List α → prodd (List α) (List α) :=
λ α F L, pair (filter L F) (filter L (inverse_func F))

def fold {α β : Type} : (α → β → β) → List α → β → β
| _ {} st := st
| F (a::L) st := F a (fold F L st)

def map : Π {α β : Type}, (α → β) → List α → List β
| α β _ {} := {}
| α β F (a::L) := ap (F a) (map F L)

definition fold_map : Π{α β:Type}, (α → β) → List α → List β := 
λ α β F L, fold (λ a b, ap (F a) b) L {}

-- ∀ n : (α → β), ∀ L : List α, fold_map n L = map n L

def reverse : Π {α : Type}, List α → List α
| α {} := {}
| α (ap n L) := append (reverse L) (n::{})

def flatten_list : Π {α : Type}, List (List α) → List α
| α {} := {}
| α (a::L) := append a (flatten_list L)

def flat_map : Π {α β : Type}, (α → List β) → List α → List β := λ α β F L, flatten_list (map F L)

definition fold_length : Π {α : Type}, List α → ℕ :=
  λ α L, fold (λ _ n, nat.succ n) L 0


definition prod_curry {X Y Z : Type} (f : prodd X Y → Z) (x : X) (y : Y) : Z :=
f (pair x y)

definition prod_uncurry {X Y Z : Type} : (X → Y → Z) → (prodd X Y) → Z
| f p := f (fst p) (snd p)

#check (λ a b, a+b) 5 6
#check prod_curry (prod_uncurry (λ a b, a+b) (pair 1 2))

#reduce prod_curry (λ pair (a:ℕ) (b:ℕ), a+1) 50 6 


@[simp]theorem map_app : Π {α β : Type}, ∀ F : α → β, ∀ L : List α, ∀ a : α,
  map F (append L (a::{})) = append (map F L) ((F a)::{}) := begin

intros α β F L a,
induction L with new L_sh H,{refl},
{
    unfold map,
    unfold append,

    rw ←H,
    unfold map
}

end

theorem map_rev : Π {α β : Type}, ∀ F : α → β, ∀ L : List α,
  map F (reverse L) = reverse (map F L) := begin

intros α β,
intro F,
intro L,

induction L with new L_sh H₁,
{
    unfold reverse,
    unfold map,
    refl
},
{
    unfold map reverse,
    simp,
    rw H₁
    --apply map_app F (reverse L_sh) new,
}

end

theorem fold_length_eq : Π {α : Type}, ∀ L : List α, fold_length L = len L := begin

intros α L,
induction L with new L_sh prev, {refl},
{
    unfold len,
    rw ←prev,
    unfold fold_length,
    refl
}

end

theorem curry {α β γ : Type} : ∀ F : (α → β → γ), 
F = prod_curry (prod_uncurry F) := begin
intro F,
apply funext,
intro a,
apply funext,
intro b,
unfold prod_curry,
unfold prod_uncurry,
refl
end

theorem a : ∀ X n L, len L = n → @get_nth X L n = option.None X :=begin

intros X n L,
revert n,
induction L with new Lh H₂,
{
    unfold get_nth,
    intros a b,
    refl
},
{
    unfold len get_nth,
    have H₃ := H₂ (len Lh) rfl,
    intro n,
    intro H₄,
    rw ←H₄,
    clear H₂,
    unfold get_nth,
    rw H₃
}

end

end z3
