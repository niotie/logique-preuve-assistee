import LPA.TP4EntiersNaturels.«7StrongInduction»
import LPA.TP4EntiersNaturels.«8Subtraction»

section division

namespace LPA.Nat

-- Définition de la division euclidienne
set_option linter.unusedVariables false in
def div (a b : Nat) : Nat :=
  if hb: b = 0 then 0
  else if hab: a < b then 0
  else div (a - b) b
  termination_by a
  decreasing_by
    apply sub_lt_of_not_lt_of_pos
    · exact hab
    · rw [← ne_zero_iff_zero_lt]; exact hb

instance : Div Nat where
  div a b := div a b

instance : Dvd Nat where
  dvd a b := ∃ c, b = a * c

def dvd_def := ∀ (a b : Nat), (a ∣ b) = ∃ c, b = a * c
