import LPA.TP1LogiqueProp

namespace LPA

variable {α : Type}         -- un type d'éléments
variable {a b : α}          -- des constantes de ce type
variable {P Q : α → Prop}   -- des prédicats unaires
variable {R : α → α → Prop} -- un prédicat binaire


-- Démontrer une quantification universelle
theorem no_contradiction : ∀ x, ¬ (P x ∧ ¬ P x) := by
  sorry

-- Utiliser une quantification universelle
example : (∀ x, P x) → P a := by
  sorry

theorem forall_comm : (∀ x, ∀ y, R x y) → ∀ y, ∀ x, R x y := by
  sorry


theorem forall_imp_or : ∀ x, P x → P x ∨ Q x := by
  sorry

theorem forall_or_left : (∀ x, P x) → (∀ x, P x ∨ Q x) := by
  sorry

-- -- Attention à la portée ! L'énoncé suivant est faux.

-- example : ∀ x, P x → ∀ x, P x ∨ Q x := by
--   fail

theorem or_forall : (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
  sorry

-- -- Attention ! L'énoncé suivant est faux (donner un exemple)

-- example : (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x) := by
--   fail


-- Quantification universelle et conjonction

theorem forall_and_of_and_forall : (∀ x, P x) ∧ (∀ x, Q x) → ∀ y, P y ∧ Q y := by
  sorry

theorem and_forall_of_forall_and : (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

theorem and_forall : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

-- -- Attention à la portée ! Les énoncés suivants sont faux

-- example : ∀ x, P x ∧ ∀ x, Q x → ∀ x, P x ∧ Q x := by
--   fail

-- example : ∀ x, P x ∧ Q x → (∀ x, P x) ∧ (∀ x, Q x) := by
--   fail
