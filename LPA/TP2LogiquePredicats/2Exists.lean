import LPA.TP1LogiqueProp

namespace LPA

variable {α : Type}         -- un type d'éléments
variable {a b : α}          -- des constantes de ce type
variable {P Q : α → Prop}   -- des prédicats unaires
variable {R : α → α → Prop} -- un prédicat binaire


-- Démontrer une propriété existentielle
example : P a ∨ P b → ∃ x, P x := by
  sorry

-- Utiliser une propriété existentielle
theorem exists_comm : (∃ x, ∃ y, R x y) → ∃ y, ∃ x, R x y := by
  sorry


theorem or_exists_of_exists_or :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

theorem exists_or_of_or_exists :
    (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
  sorry

theorem exists_or : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry


theorem and_exists_of_exists_and :
    -- Attention aux parenthèses !!
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry

-- La réciproque est fausse !
-- Essayer de la prouver, voir où cela échoue et chercher un contre-exemple
-- example : (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x) := by
--   fail


theorem forall_exists_of_exists_forall : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  sorry

-- La réciproque est fausse ! Expliquer pourquoi.
-- example : (∀ x, ∃ y, R x y) → ∃ y, ∀ x, R x y := by
--   fail
