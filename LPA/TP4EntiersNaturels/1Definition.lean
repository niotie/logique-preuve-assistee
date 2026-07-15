namespace LPA

-- Définition inductive des entiers de Peano
inductive Nat
| zero : Nat
| succ (n : Nat) : Nat


namespace Nat

-- Exemples d'entiers
@[reducible] def one := zero.succ
@[reducible] def two := one.succ
@[reducible] def three := two.succ

#reduce three

-- Incantation pour pouvoir utiliser des littéraux comme 1, 2, 45...
instance : OfNat Nat n where
  ofNat := aux n
    where aux
    | 0 => Nat.zero
    | n+1 => Nat.succ (aux n)

-- Incantation pour pouvoir utiliser #eval
def repr_nat (n : Nat) (prio : _root_.Nat) : Std.Format := match n with
  | zero => "zero"
  | succ n' => n'.repr_nat prio ++ ".succ"

instance : Repr Nat where
  reprPrec := repr_nat

-- Incantation pour rendre l'égalité entre Nat calculable
instance decidableEqNat (m n : Nat) : Decidable (m = n) := by
  revert n
  match m with
  | zero =>
    intro n
    cases n with
    | zero => exact isTrue rfl
    | succ n' => exact isFalse Nat.noConfusion
  | succ m' =>
    intro n
    cases n with
    | zero => exact isFalse Nat.noConfusion
    | succ n' =>
      rw [Nat.succ.injEq]
      apply decidableEqNat


#eval (3 : Nat) -- zero.succ.succ.succ


/-
Tout ce qui suit est construit automatiquement par Lean d'après la définition
inductive ci-dessus.
-/

section predefini  -- # Fonctions et théorèmes automatiquement engendrés par Lean

variable (C : Nat → Prop)

-- Injectivité de `succ`
#check Nat.succ.inj
#check Nat.succ.injEq

-- Distinction entre entiers différents
#check Nat.noConfusion
#check Nat.noConfusionType

-- Principe de récursion
#check Nat.casesOn
#check Nat.recOn

-- Récursion "complète"
#check Nat.below
#check Nat.brecOn

end predefini


section peano -- ## Axiomes de Peano

-- zero est un nombre entier
#check (zero : Nat)

-- axiomes de l'égalité
#check (@Eq.refl Nat)   -- l'égalité est réflexive
#check (@Eq.symm Nat)   -- l'égalité est symétrique
#check (@Eq.trans Nat)  -- l'égalité est transitive
#check (@Eq Nat)        -- en Lean, l'égalité n'a de sens qu'entre valeurs du même type

-- axiomes de succ
#check (succ : Nat → Nat)  -- succ est une fonction des naturels dans les naturels
#check (@succ.inj : ∀ (m n : Nat), m.succ = n.succ → m = n)  -- succ est injective
example : ∀ (m : Nat), m.succ ≠ zero := by
  intro m h
  exact Nat.noConfusion h

#check (∀ (m : Nat), (h : m.succ = zero) → Nat.noConfusion h)
#check @Nat.noConfusionType Prop

-- axiome d'induction
#check (@Nat.rec :
  -- Étant donné un prédicat phi...
  (phi : Nat → Prop) →
  -- ... une preuve que (phi 0) ...
  (init : phi zero) →
  -- ... et une preuve que phi est héréditaire ...
  (heredite : ∀ n, phi n → phi n.succ) →
  -- ... on peut prouver que (phi n) pour tout n :
  ∀ t, phi t)

end peano
