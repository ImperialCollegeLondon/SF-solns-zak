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

end z

inductive bina:Type
| O : bina
| pls : bina → bina 
| dob : bina → bina


def inc_b : bina → bina
| bina.O := bina.pls bina.O
| (bina.dob x) := bina.pls (bina.dob x)
| (bina.pls (bina.dob x)) := bina.dob (inc_b x)
--else pls , O = 1
| _ := bina.dob (bina.pls bina.O)

def bin_to_un : bina → ℕ
| bina.O := 0
| (bina.pls x) := 1 + bin_to_un x
| (bina.dob x) := 2 * bin_to_un x


#eval bin_to_un (bina.dob (bina.pls (bina.dob (bina.dob (bina.dob (bina.pls bina.O))))))
#eval bina.pls(bina.dob (bina.pls (bina.O)))


def check1 : bina → bool 
| x := bin_to_un (inc_b x) = (bin_to_un x) + 1

--   1 + pls dob n = 1 + 1 + 2 * n
-- = 1 + 1 + 2 * n
-- = 2 + 2 * n
-- = 2 * (1 + n)
--- = dob pls n

theorem mult_0_r : ∀ n:nat,
  n * 0 = 0 := begin
  simp
  end

open nat
theorem ac (m n : ℕ) : m^(succ n) = m * m^n :=
begin

induction n,
{
    simp
},
{
    unfold nat.pow,
    rewrite mul_comm
}

end

theorem plus_n_Sm : ∀ n m : nat,
  nat.succ (n + m) = n + (nat.succ m) := sorry

theorem plus_comm : ∀ n m : nat,
  n + m = m + n := sorry

theorem plus_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p := sorry

--open nat

theorem minus_diag : ∀ (n : nat), n - n = 0 :=
begin
intro n,
induction n,

{
    refl
},
{
    simp,
    rewrite ih_1
}

end


def is_even : ℕ → bool
| 0 := tt
| 1 := ff
| (nat.succ (nat.succ x)) := is_even x

definition b_not : bool → bool
| ff := tt
| tt := ff

theorem x_plus_two_also_even : ∀ n : nat, is_even n = is_even (n + 2) := begin
intro n,
induction n,
{
    refl
},
{
    cases (is_even a);cases is_even (nat.succ a);refl
}
end

theorem evenb_S : ∀ n : nat, is_even (nat.succ n) = b_not (is_even n) := begin

intro n,
induction n with d Hd,

{
    refl
},

{
    cases is_even (nat.succ d),
    {
        cases is_even (nat.succ (nat.succ d)),
        {
            --change ff=tt at ih_1,
            revert Hd,
            exact dec_trivial
        },
        {
            refl
        }
    },
    {
        cases is_even (nat.succ (nat.succ d)),
        {
            refl
        },
        {
            --change tt=ff at ih_1,
            revert Hd,
            exact dec_trivial
        }
    }
}

end

theorem A : ∀ n : z.nt, z.eq_n n n = tt := begin

intro n,


end

----------------------------------------
--trashier
----------------------------------------


namespace Z

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


-- x * (y+1) = xy + x
theorem nec : ∀x y: ℕ, x*(y+1)=x*y+x :=
begin
intros x y,
refl,
end


end Z

theorem test2 : ∀ n m : ℕ, n = m → n+n = m+m :=
begin
intros n m,
intro hyp,
subst hyp,
end


theorem plus_id_exercise : ∀ n m o : ℕ , n = m → m = o → n + m = m + o := 
begin
intros n m o,
intro H,
subst H,
intro H2,
subst H2
end


theorem mult_S_1 : ∀ n m : ℕ, m = nat.succ n → m * (1 + n) = m * m :=
begin
intros n m,
intro H,
subst H,
simp,
end



definition b_and : bool → bool → bool
| tt tt := tt
| _ _ := ff

definition b_or : bool → bool → bool
| ff ff := ff
| _ _ := tt

definition b_not : bool → bool
| ff := tt
| tt := ff

-- AND (a b) = NOT OR (NOT A NOT B)

theorem t : ∀ a b : bool, b_and a b = b_not ( b_or (b_not a ) (b_not b) ):=
begin
intros a b,
cases a,
{
    cases b,
    {
        exact dec_trivial
    },
    {
        exact dec_trivial
    }
},
{
    cases b,
    {
        exact dec_trivial
    },
    {
        exact dec_trivial
    }
}
end

theorem yy: ∀ x : bool, ¬ x = ff → x = tt:=
begin
intro x,
intro H,
admit
end



theorem a_b_c (c : bool) : ¬ (c = tt) → c = ff :=
begin
  intro H,
  cases c,
  { -- goal is ff = ff
    refl
  },
  { -- goal is tt = ff
    -- but we have hypothesis H : ¬tt = tt
    -- and that hypothesis is false
    --cases (H rfl)
    have H₂ : tt = tt,
      refl, -- now we have P in our context
    have Q := H H₂,
    -- check out the type of Q!
  }
end


--set_option pp.notation false 
theorem andb_true_elim2_2 : ∀ b c : bool, b_and b c = true → c = true :=
begin

intros b c,
intro H₁,
by_cases b=tt,
{
    rename h H₂, 
    by_cases c=tt,
    {
        subst h,
        refl
    },
    {
        subst H₂,
        
    }
},
{
admit
}

end

theorem identity_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = x) →
  ∀ (b : bool), f (f b) = b := begin

  intro f,
  intro h,
  intro b,

  rewrite h,
  rewrite h,

end

theorem andb_eq_orb : ∀ (b c : bool), (b_and b c = b_or b c) → b = c:=
begin

intros b c,
--intro H,

cases b,
{
    cases c,
    {
        intro H,
        refl
    },
    {
        --change ff = b_or ff tt at H,
        --revert H,
        exact dec_trivial
    }
},
{
    cases c,
    {
        --change ff = tt at H,
        --revert H,
        exact dec_trivial   
    },
    {
        intro H,
        refl
    }
}

end



example : b_and ff tt = b_or ff tt -> false :=
begin
  intro H,
  -- H : b_and ff tt = b_or ff tt
  change ff = tt at H,
  revert H,
  exact dec_trivial,
end
