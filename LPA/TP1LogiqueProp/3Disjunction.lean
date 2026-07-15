namespace LPA

variable {p q r : Prop}

-- Démontrer une disjonction : preuve du membre gauche
theorem or_intro_left (hp : p) : p ∨ q := by
  sorry

-- Démontrer une disjonction : preuve du membre droit
theorem or_intro_right (hq : q) : p ∨ q := by
  sorry

-- Utiliser une disjonction
theorem or_elim (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r := by
  sorry

-- Commutativité de la disjonction
theorem or_comm_1 (h : p ∨ q) : q ∨ p := by
  sorry

-- Associativité de la disjonction (sens 1)
theorem or_assoc_1 (h : p ∨ q ∨ r) : (p ∨ q) ∨ r := by
  sorry

-- Associativité de la disjonction (sens 2)
theorem or_assoc_2 (h : (p ∨ q) ∨ r) : p ∨ q ∨ r := by
  sorry

-- Appliquer une implication à un membre d'une disjonction (gauche)
theorem imp_across_or_left (h : p ∨ q) (h' : p → r) : r ∨ q := by
  sorry

-- Appliquer une implication à un membre d'une disjonction (droite)
theorem imp_across_or_right (h : p ∨ q) (h' : q → r) : p ∨ r := by
  sorry

theorem or_imp_of_imp_and_imp (hpr : p → r) (hqr : q → r) : p ∨ q → r := by
  sorry

theorem imp_of_or_imp_left (h : p ∨ q → r) : p → r := by
  sorry

theorem imp_of_or_imp_right (h : p ∨ q → r) : q → r := by
  sorry

theorem imp_or_of_imp_or_imp (h : (p → q) ∨ (p → r)) : p → q ∨ r := by
  sorry

theorem imp_or_imp_of_imp_or (h : p → q ∨ r) : (p → q) ∨ (p → r) := by
  -- nécessite by_cases (*tiers exclu*) !
  sorry
