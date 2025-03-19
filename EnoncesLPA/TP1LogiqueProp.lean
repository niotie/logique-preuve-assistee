namespace Local
set_option linter.unusedVariables false

variable {p q r : Prop}


section hypotheses

-- Utiliser une hypothèse du contexte
example (h : p) : p := by
  sorry

-- Une instance particulière de l'exemple précédent
example {x : Nat} (h : x ≤ 10) : x ≤ 10 := by
  sorry

-- Choisir la bonne hypothèse !
example (h1 : p) (h2 : q) (h3 : r) : q := by
  sorry

-- Une instance particulière de l'exemple précédent
example (h1 : x ≤ 10) (h2 : x ≠ 0) (h3 : x ≠ y) : x ≠ 0 := by
  sorry

end hypotheses


section implication

-- Démontrer une implication
theorem imp_refl : p → p := by
  sorry

-- Utiliser une application (modus ponens)
theorem modus_ponens (h1 : p → q) (h2 : p) : q := by
  sorry

-- On combine les deux
theorem imp_trans (hpq : p → q) (hqr : q → r) : p → r := by
  sorry

-- Pour s'exercer : si q est vraie alors n'importe quoi implique q
example (hq : q) : p → q := by
  sorry

end implication


section conjunction

-- Démontrer une conjonction
theorem and_intro (hp : p) (hq : q) : p ∧ q := by
  sorry

-- entraînement
example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  sorry

-- entraînement
example (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ r := by
  sorry

-- Utiliser une conjonction (version gauche)
theorem and_elim_left (h : p ∧ q) : p := by
  sorry

-- Utiliser une conjonction (version droite)
theorem and_elim_right (h : p ∧ q) : q := by
  sorry

-- Commutativité de la conjonction
theorem and_comm_1 (h : p ∧ q) : q ∧ p := by
  sorry

-- Associativité de la conjonction (début)
theorem and_assoc_1 (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  sorry

-- Associativité de la conjonction (suite)
theorem and_assoc_2 (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) := by
  sorry

-- entraînement (utiliser des théorèmes précédents !)
example (h : p ∧ q ∧ r) : (r ∧ p) ∧ q := by
  sorry

-- Conjonction et implication (sens 1)
theorem and_imp_1 (h : p ∧ q → r) : p → q → r := by
  sorry

-- Conjonction et implication (sens 2)
theorem and_imp_2 (h : p → q → r) : p ∧ q → r := by
  sorry

-- Implication et conjonction (sens 1)
theorem imp_and_1 (h1: p → q) (h2 :p → r) : p → q ∧ r := by
  sorry

-- Implication et conjonction (sens 2, gauche)
theorem imp_and_2_left (h: p → q ∧ r) : p → q := by
  sorry

-- Implication et conjonction (sens 2, droit)
theorem imp_and_2_right (h: p → q ∧ r) : p → r := by
  sorry

end conjunction


section disjunction

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
  -- nécessite by_cases !
  sorry

end disjunction


section distrib

-- Distributivité entre et et ou (plein de variantes)

theorem or_and_distrib_left (h : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_and_distrib_right (h : (p ∧ q) ∨ r) : (p ∨ r) ∧ (q ∨ r) := by
  sorry

theorem and_or_distrib_left (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem and_or_distrib_right (h : (p ∨ q) ∧ r) : (p ∧ r) ∨ (q ∧ r) := by
  sorry

theorem and_or_fact_left (h : (p ∨ q) ∧ (p ∨ r) ) : p ∨ (q ∧ r) := by
  sorry

theorem and_or_fact_right (h : (p ∨ r) ∧ (q ∨ r) ) : (p ∧ q) ∨ r := by
  sorry

theorem or_and_fact_left (h : (p ∧ q) ∨ (p ∧ r) ) : p ∧ (q ∨ r) := by
  sorry

theorem or_and_fact_right (h : (p ∧ r) ∨ (q ∧ r) ) : (p ∨ q) ∧ r := by
  sorry

end distrib


section negation

-- La proposition False est fausse (duh)
theorem not_false : ¬ False := by
  sorry

-- De False on peut déduire ce qu'on veut
theorem false_elim : False → p := by
  sorry

-- De deux hypothèses contradictoires on peut déduire ce qu'on veut
theorem contradiction (hp : p) (hnp : ¬ p) : q := by
  sorry

-- entraînement : réessayer sans la tactique `contradiction`
-- (indice : essayer `specialize`, `apply false_elim`, `have`...)
example (hp : p) (hnp : ¬ p) : q := by
  sorry

-- Introduction de la double négation
theorem not_not_intro (hp : p) : ¬¬p := by
  sorry

theorem not_not_elim (hnnp : ¬¬p) : p := by
  -- on ne sait pas comment avancer, donc on recourt à un
  -- raisonnement par cas (aussi appelé *tiers exclu*)
  by_cases h : p
  . sorry
  . sorry

end negation


section demorgan

-- Interactions entre négation, et, ou
-- *indication :* l'une de ces propriétés nécessite by_cases !

theorem not_or_not_of_not_and : ¬ (p ∧ q) → ¬ p ∨ ¬ q := by
  sorry

-- Lois de De Morgan (2/4)
theorem not_and_of_not_or_not : ¬ p ∨ ¬ q → ¬ (p ∧ q) := by
  sorry

-- Lois de De Morgan (3/4)
theorem not_and_not_of_not_or : ¬ (p ∨ q) → ¬ p ∧ ¬ q := by
  sorry

-- Lois de De Morgan (4/4)
theorem not_or_of_not_and_not : ¬ p ∧ ¬ q → ¬ (p ∨ q) := by
  sorry

end demorgan


section contrapose

-- Contraposée. L'une des directions nécessite `by_cases` ou `not_not_elim`

theorem contrapose_1 : (p → q) → (¬ q → ¬ p) := by
  sorry

theorem contrapose_2 : (¬ q → ¬ p) → (p → q) := by
  sorry

end contrapose


section imp_equiv

-- Implication

theorem imp_of_not_or (h : ¬ p ∨ q): p → q := by
  sorry

theorem not_or_of_imp_classical (h : p → q) : ¬ p ∨ q := by
  sorry

-- Négation d'une implication

theorem not_imp_of_and_not (h : p ∧ ¬ q): ¬ (p → q) := by
  sorry

theorem and_not_of_not_imp_classical (h : ¬ (p → q)) : p ∧ ¬ q := by
  sorry

-- Implication d'une négation

theorem not_and_of_imp_not (h : p → ¬q) : ¬(p ∧ q) := by
  sorry

theorem imp_not_of_not_and (h : ¬(p ∧ q)) : p → ¬q := by
  sorry


end imp_equiv


section iff

-- Démontrer un "si et seulement si"
theorem iff_intro (hpq : p → q) (hqp : q → p) : p ↔ q := by
  sorry

-- Utiliser un "si et seulement si" : sens direct
theorem iff_direct (h : p ↔ q) (hp : p) : q := by
  /- nombreuses variantes possibles :
     - utiliser `apply Iff.mp h`
     - utiliser `apply h.mp`
     - séparer `h` en deux avec `rcases`
     - utiliser `rewrite`, etc. -/
  sorry

-- Utiliser un "si et seulement si" : sens réciproque
theorem iff_recip (h : p ↔ q) (hp : q) : p := by
  sorry

-- Utiliser un "si et seulement si" : réécriture
theorem iff_rewrite_direct (hpq : p ↔ q) (h : q → r ∨ ¬ (q ∧ ¬r)) : p → r ∨ ¬ (p ∧ ¬r) := by
  -- utiliser `rewrite`
  sorry

theorem iff_rw_recip (hpq : p ↔ q) (h : p → r ∨ ¬ (p ∧ ¬r)) : q → r ∨ ¬ (q ∧ ¬r) := by
  -- utiliser `rewrite`
  sorry

end iff


section iff_divers

theorem and_comm : p ∧ q ↔ q ∧ p := by
  sorry

theorem and_assoc : p ∧ q ∧ r ↔ (p ∧ q) ∧ r := by
  sorry

theorem and_imp : p ∧ q → r ↔ p → q → r := by
  sorry

theorem imp_and : p → q ∧ r ↔ (p → q) ∧ (p → r) := by
  sorry

theorem or_comm : p ∨ q ↔ q ∨ p := by
  sorry

theorem or_assoc : p ∨ q ∨ r ↔ (p ∨ q) ∨ r := by
  sorry

theorem or_imp : p ∨ q → r ↔ (p → r) ∧ (q → r) := by
  sorry

theorem imp_or : p → q ∨ r ↔ (p → q) ∨ (p → r) := by
  sorry

theorem or_and_left : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_and_right : (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
  sorry

theorem and_or_left : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem and_or_right : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) := by
  sorry

theorem not_not : ¬ ¬ p ↔ p := by
  sorry

theorem not_and : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := by
  sorry

theorem not_or : ¬ (p ∨ q) → ¬ p ∧ ¬ q := by
  sorry

theorem contrapose : (p → q) ↔ (¬ q → ¬ p) := by
  sorry

theorem imp_iff : p → q ↔ ¬ p ∨ q := by
  sorry

theorem not_imp_iff : ¬ (p → q) ↔ p ∧ ¬ q := by
  sorry

theorem imp_not_iff : p → ¬q ↔ ¬(p ∧ q) := by
  sorry

end iff_divers
