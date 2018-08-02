#print notation ::
#print notation [

-- = append (rev a) b
definition rev_append {α : Type} : list α → list α → list α
| [] a := a
| (x::L₁) L₂ := rev_append L₁ (x::L₂) 

definition tr_rev {α : Type} (l : list α) : list α :=
  rev_append l []

def rev {α : Type} : list α → list α
| [] := []
| (n::L) := append (rev L) [n]

--set_option pp.notation false

theorem ap {α : Type} (a : α) (A : list α) : 
a :: A = [a] ++ A := by refl

theorem b {α : Type} (A : list α) : ∀ B C : list α,
rev_append A (C++B) = (rev_append A C) ++ B :=
begin
induction A with mem A₂ H,
{
    intros B C,
    refl
},
{
    unfold rev_append,
    intros B C,
    have Hr := ap mem (C++B),
    --have Hr : mem :: (C ++ B) = [mem] ++ C ++ B,refl,
    rw Hr, clear Hr,
    have Hr₂ := ap mem C,
    rw Hr₂, clear Hr₂,

    rw H,

    rw H C [mem],
    
    exact (list.append_assoc (rev_append A₂ [mem]) C B).symm
}
end


theorem a {α : Type} ( L : list α ) : tr_rev L = rev L := begin
unfold tr_rev,
induction L with mem L₂ H,refl,
{
    unfold rev,
    rw ←H,
    unfold rev_append,
    clear H,

    exact (list.nil_append [mem]) ▸ b L₂ [mem] list.nil,
    --have H₂ := b L₂ [mem] list.nil,
    --rw list.nil_append [mem] at H₂,
    --exact H₂
}
end

-- rev_append L₂ [mem] = ()
-- list.append (rev_append L₂ list.nil) [mem]
#reduce rev_append [5,2,3] [10]
#reduce list.append (rev_append [5,2,3] list.nil) [10]
