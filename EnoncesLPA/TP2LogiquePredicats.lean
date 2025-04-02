import EnoncesLPA.TP1LogiqueProp

namespace Local
set_option linter.unusedVariables false

variable {α : Type}         -- un type d'éléments
variable {a b : α}          -- des constantes de ce type
variable {P Q : α → Prop}   -- des prédicats unaires
variable {R : α → α → Prop} -- un prédicat binaire


section forall_base

-- Démontrer une quantification universelle
theorem no_contradiction : ∀ x, ¬ (P x ∧ ¬ P x) := by
  sorry

-- Utiliser une quantification universelle
example : (∀ x, P x) → P a := by
  sorry

theorem forall_comm : (∀ x, ∀ y, R x y) → ∀ y, ∀ x, R x y := by
  sorry

end forall_base


section forall_or

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

end forall_or


section forall_and

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

end forall_and


section exists_base

-- Démontrer une propriété existentielle
example : P a ∨ P b → ∃ x, P x := by
  sorry

-- Utiliser une propriété existentielle
theorem exists_comm : (∃ x, ∃ y, R x y) → ∃ y, ∃ x, R x y := by
  sorry

end exists_base


section exists_or

theorem or_exists_of_exists_or :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

theorem exists_or_of_or_exists :
    (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
  sorry

theorem exists_or : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

end exists_or


section exists_and

theorem and_exists_of_exists_and :
    -- Attention aux parenthèses !!
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry

-- La réciproque est fausse !
-- Essayer de la prouver, voir où cela échoue et chercher un contre-exemple
-- example : (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x) := by
--   fail

end exists_and


section quantif_imp

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

end quantif_imp


section swap_quantif

theorem forall_exists_of_exists_forall : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  sorry

-- La réciproque est fausse ! Expliquer pourquoi.
-- example : (∀ x, ∃ y, R x y) → ∃ y, ∀ x, R x y := by
--   fail

end swap_quantif


section not_quantif

-- Trois de ces théorèmes nécessitent by_cases ou not_not_elim (une ou plusieurs fois !)

theorem not_exists : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  sorry

theorem not_exists_not : (¬ ∃ x, ¬ P x) ↔ (∀ x, P x) := by
  sorry

theorem not_forall : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  sorry

theorem not_forall_not : (¬ ∀ x, ¬ P x) ↔ (∃ x, P x) := by
  sorry

section not_quantif


section buveur

theorem buveur {dans_le_bar boit : α → Prop}
    (h : ∃ x, dans_le_bar x):
    ∃ x, dans_le_bar x ∧ boit x → ∀ y, dans_le_bar y → boit y := by
  sorry

end buveur
