import LPA.TP1LogiqueProp.«1HypothesesImplication»
import LPA.TP1LogiqueProp.«2Conjunction»
import LPA.TP1LogiqueProp.«3Disjunction»
import LPA.TP1LogiqueProp.«4Distributivity»
import LPA.TP1LogiqueProp.«5Negation»

namespace LPA

variable {p q r : Prop}


-- Démontrer un "si et seulement si"
theorem iff_intro (hpq : p → q) (hqp : q → p) : p ↔ q := by
  sorry

-- Utiliser un "si et seulement si" : sens direct
theorem iff_direct (h : p ↔ q) (hp : p) : q := by
  /- nombreuses variantes possibles :
     - utiliser `apply Iff.mp h`
     - utiliser `apply h.mp`
     - séparer `h` en deux avec `rcases`
     - utiliser `rewrite`, etc. -/
  sorry

-- Utiliser un "si et seulement si" : sens réciproque
theorem iff_recip (h : p ↔ q) (hq : q) : p := by
  sorry

-- Utiliser un "si et seulement si" : réécriture
theorem iff_rewrite_direct (hpq : p ↔ q) (h : q → r ∨ ¬ (q ∧ ¬r)) : p → r ∨ ¬ (p ∧ ¬r) := by
  -- utiliser `rewrite`
  sorry

theorem iff_rw_recip (hpq : p ↔ q) (h : p → r ∨ ¬ (p ∧ ¬r)) : q → r ∨ ¬ (q ∧ ¬r) := by
  -- utiliser `rewrite`
  sorry

-- Réflexivité
theorem iff_refl : p ↔ p := by
  sorry

-- Transitivité
theorem iff_trans (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by
  sorry


section iff_divers

theorem and_comm : p ∧ q ↔ q ∧ p := by
  sorry

theorem and_assoc : p ∧ q ∧ r ↔ (p ∧ q) ∧ r := by
  sorry

theorem and_imp : p ∧ q → r ↔ p → q → r := by
  sorry

theorem imp_and : p → q ∧ r ↔ (p → q) ∧ (p → r) := by
  sorry

theorem or_comm : p ∨ q ↔ q ∨ p := by
  sorry

theorem or_assoc : p ∨ q ∨ r ↔ (p ∨ q) ∨ r := by
  sorry

theorem or_imp : p ∨ q → r ↔ (p → r) ∧ (q → r) := by
  sorry

theorem imp_or : p → q ∨ r ↔ (p → q) ∨ (p → r) := by
  sorry

theorem or_and_left : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_and_right : (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
  sorry

theorem and_or_left : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem and_or_right : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) := by
  sorry

theorem not_not : ¬ ¬ p ↔ p := by
  sorry

theorem not_and : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := by
  sorry

theorem not_or : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by
  sorry

theorem contrapose : (p → q) ↔ (¬ q → ¬ p) := by
  sorry

theorem imp_iff : p → q ↔ ¬ p ∨ q := by
  sorry

theorem not_imp_iff : ¬ (p → q) ↔ p ∧ ¬ q := by
  sorry

theorem imp_not_iff : p → ¬q ↔ ¬(p ∧ q) := by
  sorry

end iff_divers
