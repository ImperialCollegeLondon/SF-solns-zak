
@[simp] lemma to_bool_true_eq_tt (h : decidable true) : @to_bool true h = tt :=
decidable.cases_on h (λ h, false.elim (iff.mp not_true h)) (λ _, rfl)

@[simp] lemma to_bool_false_eq_ff (h : decidable false) : @to_bool false h = ff :=
decidable.cases_on h (λ h, rfl) (λ h, false.elim h)
