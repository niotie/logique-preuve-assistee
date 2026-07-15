namespace LPA

variable {p q r : Prop}

section hypotheses

-- Utiliser une hypothèse du contexte
example (h : p) : p := by
  sorry

-- Une instance particulière de l'exemple précédent
example {x : Nat} (h : x ≤ 10) : x ≤ 10 := by
  sorry

-- Choisir la bonne hypothèse !
set_option linter.unusedVariables false in
example (h1 : p) (h2 : q) (h3 : r) : q := by
  sorry

-- Une instance particulière de l'exemple précédent
set_option linter.unusedVariables false in
example {x y : Nat} (h1 : x ≤ 10) (h2 : x ≠ 0) (h3 : x ≠ y) : x ≠ 0 := by
  sorry

end hypotheses


section implication

-- Démontrer une implication
theorem imp_refl : p → p := by
  sorry

-- Utiliser une application (modus ponens)
theorem modus_ponens (h1 : p → q) (h2 : p) : q := by
  sorry

-- On combine les deux
theorem imp_trans (hpq : p → q) (hqr : q → r) : p → r := by
  sorry

-- Pour s'exercer : si q est vraie alors n'importe quoi implique q
example (hq : q) : p → q := by
  sorry

end implication
