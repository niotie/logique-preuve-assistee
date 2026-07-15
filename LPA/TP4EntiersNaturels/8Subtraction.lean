import LPA.TP4EntiersNaturels.«6NonStrictOrder»

namespace LPA.Nat

-- # Soustraction : définition et propriétés

def sub : Nat → Nat → Nat
| m, zero => m
| m, succ n => pred (sub m n)

-- Incantation pour pouvoir utiliser la syntaxe '-'
instance instSubNat : Sub Nat where
  sub := sub

#eval two - three
#eval three - three
#eval three - two


-- Théorèmes reflétant la définition
@[simp]
theorem sub_eq : sub x y = x - y := by
  rfl

@[simp]
theorem sub_succ (m n : Nat): m - n.succ = (m - n).pred := by
  rfl


-- Élement neutre à droite
@[simp]
theorem sub_zero (n : Nat): n - zero = n := by
  sorry


-- Interaction avec succ
@[simp]
theorem succ_sub (m n : Nat): (m.succ - n).pred = m - n := by
  sorry

@[simp]
theorem succ_sub_succ {m n : Nat}: m.succ - n.succ = m - n := by
  sorry


-- Soustraction par le même nombre
@[simp]
theorem sub_self {m : Nat} : m - m = zero := by
  sorry


-- Soustraction par un entier plus grand
theorem sub_eq_zero_of_le {m n : Nat} : m ≤ n → m - n = zero := by
  sorry

theorem le_of_sub_eq_zero {m n : Nat} : m - n = zero → m ≤ n := by
  sorry

theorem sub_eq_zero_iff_le {m n : Nat} : m - n = zero ↔ m ≤ n :=
  sorry

@[simp]
theorem zero_sub {n : Nat} : zero - n = zero :=
  sorry


-- Interactions avec add
theorem sub_sub {m n k : Nat} : m - n - k = m - (n + k) := by
  sorry

theorem add_sub_add_right {n k m : Nat} : (n + k) - (m + k) = n - m := by
  sorry

theorem add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  sorry

@[simp]
theorem add_sub_cancel (n m : Nat) : n + m - m = n := by
  sorry

@[simp]
theorem add_sub_cancel_left (n m : Nat) : n + m - n = m :=
  sorry

theorem add_sub_assoc {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 sorry


-- Comportement de mul vis-à-vis de pred
theorem mul_pred {m n : Nat} : m * n.pred = m * n - m := by
  sorry

theorem pred_mul {m n : Nat} : m.pred * n = m * n - n := by
  sorry


-- Distributivité de la multiplication sur la soustraction
-- à gauche
theorem mul_sub_left_distrib {m n k : Nat} : m * (n - k) = m * n - m * k := by
  sorry

-- à droite
theorem mul_sub_right_distrib {m n k : Nat} : (m - n) * k = m * k - n * k := by
  sorry


-- Propriétés de lt relatives à la soustraction
theorem sub_eq_zero_iff_not_lt (m n : Nat) : m - n = zero ↔ ¬ n < m := by
  sorry

theorem sub_lt_of_not_lt_of_pos {a b : Nat} (h : ¬ a < b) (h' : zero < b) : a - b < a := by
  sorry
