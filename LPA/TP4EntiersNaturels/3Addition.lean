import LPA.TP4EntiersNaturels.«2Predecessor»

namespace LPA.Nat

-- # Addition : définition et propriétés

variable (m n k : Nat)

-- Définition inductive de l'addition
@[reducible]
def add : Nat → Nat → Nat
| zero, n => n
| succ m, n => (add m n).succ

#eval two.add two


-- Incantation pour pouvoir utiliser la syntaxe '+'
instance : Add Nat where
  add := add

#eval two + two


-- Un premier théorème !! Youpi !
theorem one_plus_one : one + one = two := by
  sorry

-- Théorèmes reflétant la définition
@[simp]
theorem zero_add : zero + n = n := by
  sorry

@[simp]
theorem succ_add : m.succ + n = (m + n).succ := by
  sorry


-- Élément neutre à droite
example : n + zero = n := by
  cases n with
  | zero => sorry
  | succ n' => sorry

-- Nouvel essai
@[simp]
theorem add_zero : n + zero = n := by
  induction n with
  | zero => sorry
  | succ m' ih => sorry


-- Commutativité
example : m + n = n + m := by
  induction m with
  | zero =>
      rewrite [add_zero, zero_add]
      rfl
  | succ m' ih =>
      rewrite [succ_add, ih]
      -- coincé !
      sorry

-- Nouvel essai : avec un nouveau lemme
@[simp]
theorem add_succ : m + n.succ = (m + n).succ := by
  sorry

theorem add_comm : m + n = n + m := by
  sorry

-- Associativité de l'addition
theorem add_assoc : m + n + k = m + (n + k) := by
  sorry

-- Divers
theorem one_add : m.succ = one + m := by
  sorry

theorem add_one : m.succ = m + one := by
  sorry
