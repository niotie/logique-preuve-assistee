import LPA.TP1LogiqueProp

namespace LPA

variable {α : Type}         -- un type d'éléments
variable {a b : α}          -- des constantes de ce type
variable {P Q : α → Prop}   -- des prédicats unaires
variable {r : Prop}         -- une proposition


theorem imp_forall_of_forall_imp (h : ∀ x, P x → Q x) :
    (∀ x, P x) → (∀ x, Q x) := by
  sorry

theorem imp_exists_of_forall_imp (h : ∀ x, P x → Q x) :
    (∃ x, P x) → (∃ x, Q x) := by
  sorry

theorem iff_forall_of_forall_iff (h : ∀ x, P x ↔ Q x) :
    (∀ x, P x) ↔ (∀ x, Q x) := by
  sorry

theorem iff_exists_of_forall_iff (h : ∀ x, P x ↔ Q x) :
    (∃ x, P x) ↔ (∃ x, Q x) := by
  sorry

theorem exists_imp : (∃ x, P x) → r ↔ ∀ x, P x → r := by
  sorry

-- -- Attention au parenthésage ! La version suivante est fausse
-- example : (∃ x, P x) → r ↔ (∀ x, P x) → r := by
--   fail
