import LPA.TP1LogiqueProp

namespace LPA

variable {α : Type}       -- un type d'éléments
variable {P : α → Prop}   -- un prédicat unaire


-- Trois de ces théorèmes nécessitent by_cases ou not_not_elim (une ou plusieurs fois !)

theorem not_exists : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  sorry

theorem not_exists_not : (¬ ∃ x, ¬ P x) ↔ (∀ x, P x) := by
  sorry

theorem not_forall : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  sorry

theorem not_forall_not : (¬ ∀ x, ¬ P x) ↔ (∃ x, P x) := by
  sorry
