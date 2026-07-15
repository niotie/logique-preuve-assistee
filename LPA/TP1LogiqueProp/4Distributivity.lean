namespace LPA

variable {p q r : Prop}

-- Distributivité entre et et ou (plein de variantes)

theorem or_and_distrib_left (h : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_and_distrib_right (h : (p ∧ q) ∨ r) : (p ∨ r) ∧ (q ∨ r) := by
  sorry

theorem and_or_distrib_left (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem and_or_distrib_right (h : (p ∨ q) ∧ r) : (p ∧ r) ∨ (q ∧ r) := by
  sorry

theorem and_or_fact_left (h : (p ∨ q) ∧ (p ∨ r) ) : p ∨ (q ∧ r) := by
  sorry

theorem and_or_fact_right (h : (p ∨ r) ∧ (q ∨ r) ) : (p ∧ q) ∨ r := by
  sorry

theorem or_and_fact_left (h : (p ∧ q) ∨ (p ∧ r) ) : p ∧ (q ∨ r) := by
  sorry

theorem or_and_fact_right (h : (p ∧ r) ∨ (q ∧ r) ) : (p ∨ q) ∧ r := by
  sorry
