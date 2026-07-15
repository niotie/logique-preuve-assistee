import LPA.TP4EntiersNaturels.«3Addition»

namespace LPA.Nat

-- ## Multiplication : définition et propriétés

variable (m n k : Nat)

-- Définition de la multiplication
@[reducible]
def mul : Nat → Nat → Nat
  | zero, _ => zero
  | succ m, n => n + m.mul n

instance : Mul Nat where
  mul := mul

#eval two * two

-- Théorèmes reflétant la définition
@[simp]
theorem zero_mul : zero * m = zero := by
  rfl

@[simp]
theorem succ_mul : m.succ * n = n + m * n := by
  rfl

-- Élément absorbant
-- on a déjà zero_mul, on montre l'absorption à droite
@[simp]
theorem mul_zero : m * zero = zero := by
  sorry

-- Comportement vis-à-vis de succ
-- on a déjà succ_mul, on montre la variante à droite
@[simp]
theorem mul_succ : m * n.succ = m + m * n := by
  sorry

-- Élément neutre
@[simp]
theorem one_mul : one * m = m := by
  sorry

@[simp]
theorem mul_one : m * one = m := by
  sorry

-- Commutativité
theorem mul_comm : m * n = n * m := by
  sorry

-- Distributivité de la multiplication sur l'addition
-- à gauche
theorem mul_add_left : m * (n + k) = m * n + m * k := by
  sorry

-- à droite
theorem mul_add_right : (m + n) * k = m * k + n * k := by
  sorry

-- Associativité
theorem mul_assoc : m * n * k = m * (n * k) := by
  sorry
