namespace LPA

variable {p q r : Prop}

-- Démontrer une conjonction
theorem and_intro (hp : p) (hq : q) : p ∧ q := by
  sorry

-- entraînement
example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  sorry

-- entraînement
example (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ r := by
  sorry

-- Utiliser une conjonction (version gauche)
theorem and_elim_left (h : p ∧ q) : p := by
  sorry

-- Utiliser une conjonction (version droite)
theorem and_elim_right (h : p ∧ q) : q := by
  sorry

-- Commutativité de la conjonction
theorem and_comm_1 (h : p ∧ q) : q ∧ p := by
  sorry

-- Associativité de la conjonction (début)
theorem and_assoc_1 (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  sorry

-- Associativité de la conjonction (suite)
theorem and_assoc_2 (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) := by
  sorry

-- entraînement (utiliser des théorèmes précédents !)
example (h : p ∧ q ∧ r) : (r ∧ p) ∧ q := by
  sorry

-- Conjonction et implication (sens 1)
theorem and_imp_1 (h : p ∧ q → r) : p → q → r := by
  sorry

-- Conjonction et implication (sens 2)
theorem and_imp_2 (h : p → q → r) : p ∧ q → r := by
  sorry

-- Implication et conjonction (sens 1)
theorem imp_and_1 (h1: p → q) (h2 :p → r) : p → q ∧ r := by
  sorry

-- Implication et conjonction (sens 2, gauche)
theorem imp_and_2_left (h: p → q ∧ r) : p → q := by
  sorry

-- Implication et conjonction (sens 2, droit)
theorem imp_and_2_right (h: p → q ∧ r) : p → r := by
  sorry
