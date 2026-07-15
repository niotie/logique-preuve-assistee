namespace LPA

variable {p q r : Prop}


-- La proposition False est fausse (duh)
theorem not_false : ¬ False := by
  sorry

-- De False on peut déduire ce qu'on veut
theorem false_elim : False → p := by
  sorry

-- De deux hypothèses contradictoires on peut déduire ce qu'on veut
theorem contradiction (hp : p) (hnp : ¬ p) : q := by
  sorry

-- entraînement : réessayer sans la tactique `contradiction`
-- (indice : essayer `exfalso`, `specialize`, `apply false_elim`, `have`...)
example (hp : p) (hnp : ¬ p) : q := by
  sorry

-- Introduction de la double négation
theorem not_not_intro (hp : p) : ¬¬p := by
  sorry

theorem not_not_elim (hnnp : ¬¬p) : p := by
  -- on ne sait pas comment avancer, donc on recourt à un
  -- raisonnement par cas (aussi appelé *tiers exclu*)
  by_cases h : p
  . sorry
  . sorry


section demorgan

-- Interactions entre négation, et, ou
-- *indication :* l'une de ces propriétés nécessite by_cases !

theorem not_or_not_of_not_and : ¬ (p ∧ q) → ¬ p ∨ ¬ q := by
  sorry

-- Lois de De Morgan (2/4)
theorem not_and_of_not_or_not : ¬ p ∨ ¬ q → ¬ (p ∧ q) := by
  sorry

-- Lois de De Morgan (3/4)
theorem not_and_not_of_not_or : ¬ (p ∨ q) → ¬ p ∧ ¬ q := by
  sorry

-- Lois de De Morgan (4/4)
theorem not_or_of_not_and_not : ¬ p ∧ ¬ q → ¬ (p ∨ q) := by
  sorry

end demorgan


section contrapose

-- Contraposée. L'une des directions nécessite `by_cases` ou `not_not_elim`

theorem contrapose_1 : (p → q) → (¬ q → ¬ p) := by
  sorry

theorem contrapose_2 : (¬ q → ¬ p) → (p → q) := by
  sorry

end contrapose


section imp_equiv

-- Implication

theorem imp_of_not_or (h : ¬ p ∨ q): p → q := by
  sorry

theorem not_or_of_imp_classical (h : p → q) : ¬ p ∨ q := by
  sorry

-- Négation d'une implication

theorem not_imp_of_and_not (h : p ∧ ¬ q): ¬ (p → q) := by
  sorry

theorem and_not_of_not_imp_classical (h : ¬ (p → q)) : p ∧ ¬ q := by
  sorry

-- Implication d'une négation

theorem not_and_of_imp_not (h : p → ¬q) : ¬(p ∧ q) := by
  sorry

theorem imp_not_of_not_and (h : ¬(p ∧ q)) : p → ¬q := by
  sorry

end imp_equiv
