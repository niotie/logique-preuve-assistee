import LPA.TP1LogiqueProp
import LPA.TP4EntiersNaturels.«5StrictOrder»

namespace LPA.Nat

-- ## Définition de l'ordre large

inductive le : Nat → Nat → Prop
  | refl {n : Nat} : le n n
  | step {m n : Nat} (h : le m n) : le m n.succ

instance : LE Nat where
  le := le

/-! # Théorèmes reflétant la définition -/

@[refl, simp]
theorem le_refl {m : Nat} : m ≤ m := by
  exact le.refl

theorem le_succ_of_le {m n : Nat} : m ≤ n → m ≤ n.succ := by
  exact le.step


-- ## Équivalences avec l'ordre strict

theorem le_iff_lt_or_eq (m n : Nat) : m ≤ n ↔ m < n ∨ m = n := by
  sorry

theorem lt_iff_le_and_ne (m n : Nat) : m < n ↔ m ≤ n ∧ m ≠ n := by
  sorry

theorem lt_succ_iff {m n : Nat} : m < n.succ ↔ m ≤ n := by
  sorry

theorem not_lt {m n : Nat} : ¬ n < m ↔ m ≤ n  := by
  sorry

theorem not_le {m n : Nat} : ¬ n ≤ m ↔ m < n := by
  sorry

theorem succ_le {m n : Nat} : m.succ ≤ n ↔ m < n := by
  sorry


-- ## Propriétés relatives à zero

theorem zero_le {m : Nat} : zero ≤ m := by
  sorry

theorem le_zero (m : Nat) : m ≤ zero ↔ m = zero := by
  sorry

theorem ne_zero_iff_zero_lt : m ≠ zero ↔ zero < m := by
  sorry


-- ## Propriétés relatives à succ

theorem le_of_succ_le {m n : Nat} : m.succ ≤ n → m ≤ n := by
  sorry

theorem le_of_succ_le_succ {m n : Nat} : m.succ ≤ n.succ → m ≤ n := by
  sorry

theorem succ_le_succ_of_le {m n : Nat} : m ≤ n → m.succ ≤ n.succ := by
  sorry

theorem succ_le_succ_iff {m n : Nat} : m.succ ≤ n.succ ↔ m ≤ n :=
  sorry

theorem not_succ_le_self {n : Nat} : ¬ n.succ ≤ n := by
  sorry

theorem not_succ_le_zero {n : Nat} : ¬ n.succ ≤ 0 := by
  sorry


/-! # Décidabilité -/

instance decidableLe (m n : Nat) : Decidable (m ≤ n) := by
  match m, n with
  | 0, _ => exact isTrue zero_le
  | succ _, 0 => exact isFalse not_succ_le_zero
  | succ _, succ _ => rw [succ_le_succ_iff]; apply decidableLe


-- ## Propriétés relatives à pred

theorem pred_lt {n : Nat} : n ≠ zero → n.pred < n := by
  sorry

theorem pred_eq_self_iff : n = n.pred ↔ n = zero := by
  sorry


-- ## ≤ est un ordre (large)

-- Réflexivité
#check le_refl

-- Antisymétrie
theorem le_antisymm' {m n : Nat} : m ≤ n → n ≤ m → m = n := by
  sorry

-- Transitivité
theorem le_trans {m n k : Nat} : m ≤ n → n ≤ k → m ≤ k := by
  sorry

-- Variante de la transitivité
theorem lt_of_lt_of_le {m n k : Nat} : m < n → n ≤ k → m < k := by
  sorry


-- ## Compatibilité avec + et *

theorem le_add_right {m n : Nat} : m ≤ m + n := by
  sorry


-- ## Introduction et élimination de ≤

theorem le.dest {m n : Nat} (h : m ≤ n) : ∃ k, m + k = n := by
  sorry

theorem le.intro {m n k : Nat} (h : m + k = n) : m ≤ n := by
  sorry
