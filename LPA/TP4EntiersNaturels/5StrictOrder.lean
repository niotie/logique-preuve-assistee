import LPA.TP4EntiersNaturels.«4Multiplication»

namespace LPA.Nat

/-! # Définition -/

-- Définition inductive de lt
inductive lt : Nat → Nat → Prop
  | succ {n : Nat} : lt n n.succ
  | step {m n : Nat} (h : lt m n) : lt m n.succ

-- Incantation pour utiliser le symbole <
instance : LT Nat where
  lt := lt


/-! # Théorèmes reflétant la définition -/

theorem lt_succ_self {m : Nat} : m < m.succ := by
  exact lt.succ

theorem lt_succ_of_lt {m n : Nat} : m < n → m < n.succ := by
  exact lt.step


/-! # Propriétés de lt relatives à 0 -/

-- Aucun nombre n'est strictement inférieur à zéro
theorem not_lt_zero {n : Nat} : ¬ n < zero := by
  sorry

-- Zéro est strictement inférieur à tout successeur
theorem zero_lt_succ {n : Nat} : zero < n.succ := by
  sorry


/-! # Propriétés de lt relatives à la fonction succ -/

theorem lt_of_succ_lt {m n : Nat} : m.succ < n → m < n := by
  sorry

theorem lt_of_succ_lt_succ {m n : Nat} : m.succ < n.succ → m < n := by
  sorry

theorem succ_lt_succ_of_lt {m n : Nat} : m < n → m.succ < n.succ := by
  sorry

@[simp]
theorem succ_lt_succ_iff {m n : Nat} : m.succ < n.succ ↔ m < n := by
  sorry


/-! # Décidabilité -/

instance decidableLt (m n : Nat) : Decidable (m < n) := by
  match m, n with
  | _, 0 => exact isFalse not_lt_zero
  | 0, succ _ => exact isTrue zero_lt_succ
  | succ _, succ _ => rw [succ_lt_succ_iff]; apply decidableLt


/-! # lt est une relation d'ordre strict -/

-- Irreflexivité de lt
theorem lt_irrefl {m : Nat} : ¬ m < m := by
    sorry

-- Asymétrie de lt
theorem lt_asymm {m n : Nat} : m < n → ¬ n < m := by
    sorry

-- Antisymétrie (conséquence de l'asymétrie)
theorem lt_antisymm {m n : Nat} : m < n → n < m → m = n := by
  sorry

-- Transitivité de lt
theorem lt_trans {m n k : Nat} : m < n → n < k → m < k := by
  sorry


/-! # Trichotomie (implique aussi que l'ordre est total) -/

theorem lt_trichotomy {m n : Nat} : m < n ∨ m = n ∨ n < m := by
  sorry


/-! # Compatibilité avec + et * -/

theorem add_lt_add_right {m n k : Nat} (h : m < n) : m + k < n + k := by
  sorry

theorem add_lt_add_left {m n k : Nat} (h : m < n) : k + m < k + n := by
  sorry

theorem mul_lt_mul_right {m n k : Nat} (hk : zero < k) (hmn : m < n) : m * k < n * k := by
  sorry

theorem mul_lt_mul_left {m n k : Nat} (hk : zero < k) (hmn : m < n) : k * m < k * n := by
  sorry
