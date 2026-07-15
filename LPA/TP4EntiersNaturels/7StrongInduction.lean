import LPA.TP2LogiquePredicats
import LPA.TP3EnsemblesFonctions
import LPA.TP4EntiersNaturels.«6NonStrictOrder»

namespace LPA.Nat

-- ## Induction forte

theorem strongInduction
    {phi : Set Nat}
    (ind : ∀ n, (∀ m, m < n → phi m) → phi n) :
    ∀ k, phi k := by
  intro k
  apply ind
  induction k with
  | zero => sorry
  | succ k' ih => sorry

-- Principe du bon ordre :
-- tout ensemble d'entiers possède un minimum
def non_empty (A : Set Nat) := ∃ (n : Nat), A n
def minimum (m : Nat) (A : Set Nat) := A m ∧ ∀ (n : Nat), A n → m ≤ n
def has_minimum (A : Set Nat) := ∃ (m : Nat), minimum m A

theorem minimal_element_property (A : Set Nat) (h : non_empty A) : has_minimum A := by
  obtain ⟨n, hn⟩ := h
  induction n using strongInduction with
  | ind n ih =>
    by_cases h : ∃ m, m < n ∧ A m
    . sorry
    . sorry

-- La propriété du minimum permet de démontrer la propriété d'induction
example :
    (∀ (A : Set Nat), (∃ n, A n) → ∃ m, A m ∧ ∀ (n : Nat), A n → m ≤ n) →
    (∀ (A : Set Nat), A zero → (∀ n, A n → A n.succ) → ∀ n, A n) :=  by
  sorry

-- L'ordre lt est bien fondé
instance lt_wfRel : WellFoundedRelation Nat where
  rel := (. < .)
  wf := by
    apply WellFounded.intro
    intro n
    induction n using strongInduction with
    | ind n ih =>
        constructor
        intro m h
        apply ih
        exact h
