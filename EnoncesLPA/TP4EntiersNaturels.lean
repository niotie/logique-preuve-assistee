import EnoncesLPA.TP3EnsemblesFonctions

namespace Local

-- Définition inductive des entiers de Peano
inductive Nat
| zero : Nat
| succ (n : Nat) : Nat


namespace Nat

-- Exemples d'entiers
def one := zero.succ
def two := one.succ
def three := two.succ

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


#eval (3 : Nat) -- zero.succ.succ.succ

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

-- Récurrence "complète"
#check Nat.ibelow
#check Nat.binductionOn

end predefini


section peano -- ## Axiomes de Peano
/-
Tout ce qui suit est construit automatiquement par Lean d'après la définition
inductive ci-dessus.
-/

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


section pred  -- ## Fonction "prédécesseur"

-- Fonction "prédécesseur"
def pred : Nat → Nat
  | zero => zero
  | succ n => n

theorem pred_succ {m : Nat} : m.succ.pred = m := by
  rewrite [pred]
  sorry

theorem succ_pred (h : m ≠ 0): m.pred.succ = m := by
  -- rewrite [pred]  -- ne fonctionne pas !
  cases m with
  | zero => sorry
  | succ m' => sorry

end pred


section addition  -- # Addition : définition et propriétés

variable (m n k : Nat)

-- Définition inductive de l'addition
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
theorem zero_add : zero + n = n := by
  sorry
theorem succ_add : m.succ + n = (m + n).succ := by
  sorry


-- Élément neutre à droite
example : n + zero = n := by
  cases n with
  | zero => sorry
  | succ m' => sorry

-- Nouvel essai
theorem add_zero : n + zero = n := by
  induction n with
  | zero => sorry
  | succ m' ih => sorry

-- Commutativité
example : m + n = n + m := by
  induction m with
  | zero =>
      rw [add_zero, zero_add]
  | succ m' ih =>
      rw [succ_add, ih]
      -- coincé !
      sorry

-- Nouvel essai : avec un nouveau lemme
theorem add_succ : m + n.succ = (m + n).succ := by
  sorry

theorem add_comm : m + n = n + m := by
  sorry


-- Associativité de l'addition
theorem add_assoc : m + n + k = m + (n + k) := by
  sorry


-- Divers
theorem add_one : m.succ = m + one := by
  sorry

end addition


section multiplication  -- ## Multiplication : définition et propriétés

variable (m n k : Nat)

-- Définition de la multiplication
def mul : Nat → Nat → Nat
  | zero, _ => zero
  | succ m, n => n + m.mul n

instance : Mul Nat where
  mul := mul

#eval two * two


-- Théorèmes reflétant la définition
theorem zero_mul : zero * m = zero := by rfl
theorem succ_mul : m.succ * n = n + m * n := by rfl


-- Élément absorbant
-- on a déjà zero_mul, on montre l'absorption à droite
theorem mul_zero : m * zero = zero := by
  sorry


-- Commutativité
theorem mul_succ : m * n.succ = m + m * n := by
  sorry

theorem mul_comm : m * n = n * m := by
  sorry


-- Élément neutre
theorem mul_one : m * one = m := by
  sorry


-- Distributivité
theorem mul_add_left : m * (n + k) = m * n + m * k := by
  sorry

-- Associativité
theorem mul_assoc : m * n * k = m * (n * k) := by
  sorry

end multiplication


section ordre  -- # Définition et propriétés de l'ordre sur Nat


-- ## Ordre strict lt

-- Définition inductive de lt
inductive lt : Nat → Nat → Prop
  | succ {n : Nat} : lt n n.succ
  | step {m n : Nat} (h : lt m n) : lt m n.succ

-- Incantation pour utiliser le symbole <
instance : LT Nat where
  lt := lt


-- ## Propriétés de lt relatives à 0

-- Aucun nombre n'est strictement inférieur à zéro
theorem not_lt_zero {n : Nat} : ¬ n < zero := by
  sorry

-- Zéro est strictement inférieur à tout successeur
theorem zero_lt_succ {n : Nat} : zero < n.succ := by
  sorry


-- ## Propriétés de lt relatives à la fonction succ

theorem lt_of_succ_lt {m n : Nat} : m.succ < n → m < n := by
  sorry

theorem lt_of_succ_lt_succ {m n : Nat} : m.succ < n.succ → m < n := by
  sorry

theorem succ_lt_succ_of_lt {m n : Nat} : m < n → m.succ < n.succ := by
  sorry

theorem succ_lt_succ_iff {m n : Nat} : m.succ < n.succ ↔ m < n := by
  sorry


-- ## lt est une relation d'ordre strict

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


-- ## Trichotomie (implique aussi que l'ordre est total)

theorem lt_trichotomy {m n : Nat} : m < n ∨ m = n ∨ n < m := by
  sorry


-- ## Définition de l'ordre large

inductive le : Nat → Nat → Prop
  | refl {n : Nat} : le n n
  | step {m n : Nat} (h : le m n) : le m n.succ

instance : LE Nat where
  le := le


-- ## Équivalences

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

theorem not_succ_le_self {n : Nat} : ¬ n.succ ≤ n := by
  sorry


-- ## Propriétés relatives à pred

theorem pred_lt {n : Nat} : n ≠ zero → n.pred < n := by
  sorry

theorem pred_eq_self_iff : n = n.pred ↔ n = zero := by
  sorry


-- ## ≤ est un ordre (large)

-- Réfléxivité
theorem le_refl {m : Nat} : m ≤ m := by
  sorry

-- Antisymétrie
theorem le_antisymm' {m n : Nat} : m ≤ n → n ≤ m → m = n := by
  sorry

-- Transitivité
theorem le_trans {m n k : Nat} : m ≤ n → n ≤ k → m ≤ k := by
  sorry

-- Variantes de la transitivité
theorem lt_of_lt_of_le {m n k : Nat} : m < n → n ≤ k → m < k := by
  sorry


-- ## Compatibilité avec + et *


theorem add_lt_add_right {m n k : Nat} (h : m < n) : m + k < n + k := by
  sorry

theorem add_lt_add_left {m n k : Nat} (h : m < n) : k + m < k + n := by
  sorry

theorem le_add_right {m n : Nat} : m ≤ m + n := by
  sorry


theorem mul_lt_mul_right {m n k : Nat} (hk : zero < k) (hmn : m < n) : m * k < n * k := by
  sorry

theorem mul_lt_mul_left {m n k : Nat} (hk : zero < k) (hmn : m < n) : k * m < k * n := by
  sorry


-- ## Introduction et élimination de ≤

theorem le.dest {m n : Nat} (h : m ≤ n) : ∃ k, m + k = n := by
  sorry


theorem le.intro {m n k : Nat} (h : m + k = n) : m ≤ n := by
  sorry


end ordre


section induction

-- ## Induction forte

theorem strongInduction
    {phi : Nat → Prop}
    (ind : ∀ n, (∀ m, m < n → phi m) → phi n) :
    ∀ k, phi k := by
  intro k
  have h : ∀m, m ≤ k → phi m := by
    sorry
  apply h
  exact le_refl

-- Propriété de l'ordre bien fondé
theorem lt_wfRel (A : Nat → Prop) (h : ∃ (n : Nat), A n) :
    (∃ (m : Nat), A m ∧ ∀ (n : Nat), A n → m ≤ n) := by
  obtain ⟨n, hn⟩ := h
  induction n using strongInduction with
  | ind n ih =>
      sorry


-- La propriété de l'élément minimal permet de démontrer la propriété d'induction
example :
    (∀ (A : Nat → Prop), (∃ n, A n) → ∃ m, A m ∧ ∀ (n : Nat), A n → m ≤ n) →
    (∀ (A : Nat → Prop), A zero → (∀ n, A n → A n.succ) → ∀ n, A n) :=  by
  sorry

end induction
