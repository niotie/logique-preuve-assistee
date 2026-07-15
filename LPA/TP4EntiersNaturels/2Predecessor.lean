import LPA.TP4EntiersNaturels.«1Definition»

namespace LPA.Nat

-- ## Fonction "prédécesseur"

-- Fonction "prédécesseur"
@[reducible]
def pred : Nat → Nat
  | zero => zero
  | succ n => n

@[simp]
theorem pred_succ {m : Nat} : m.succ.pred = m := by
  rewrite [pred]
  sorry

@[simp]
theorem succ_pred {m : Nat} (h : m ≠ 0): m.pred.succ = m := by
  -- rewrite [pred]  -- ne fonctionne pas !
  cases m with
  | zero => sorry
  | succ m' => sorry

theorem pred_eq_of_eq_succ {m n : Nat} (h : m = n.succ) : m.pred = n := by
  sorry
