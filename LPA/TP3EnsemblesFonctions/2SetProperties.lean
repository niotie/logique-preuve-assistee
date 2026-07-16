import LPA.TP3EnsemblesFonctions.«1SetDefinitions»

namespace LPA
-- set_option linter.unusedVariables false

universe u
variable {α : Type u}
variable {r s t : Set α}
variable {x x' : α}

open Set

/-! # Propriétés relatives aux ensembles -/


section subset  -- ## Propriétés liées à la relation ⊆

@[refl]
theorem subset_refl : s ⊆ s := by
  sorry

theorem subset_antisymm {s t : Set α} (h : s ⊆ t) (h' : t ⊆ s) : s = t := by
  sorry

theorem subset_trans (hrs : r ⊆ s) (hst : s ⊆ t) : r ⊆ t := by
  sorry

end subset


section singleton  -- ## Propriétés des singletons

@[simp,refl]
theorem mem_singleton_iff : x ∈ ({x'} : Set α) ↔ x = x' := by
  sorry

@[simp]
theorem sub_singleton_iff : {x} ⊆ ({x'} : Set α) ↔ x = x' := by
  sorry

@[simp]
theorem eq_singleton_iff : {x} = ({x'} : Set α) ↔ x = x' := by
  sorry

end singleton


section union    -- ## Propriétés de l'union

theorem union_empty (s : Set α) : s ∪ ∅ = s := by
  sorry

theorem union_univ (s : Set α) : s ∪ univ = univ := by
  sorry

theorem union_comm : s ∪ t = t ∪ s := by
  sorry

theorem union_assoc : r ∪ s ∪ t = r ∪ (s ∪ t) := by
  sorry

theorem sub_union : s ⊆ s ∪ t := by
  sorry

theorem sub_of_union_eq (h : s = s ∪ t) : t ⊆ s := by
  sorry

theorem union_eq_of_sub (h : t ⊆ s) : s = s ∪ t := by
  sorry

theorem union_eq_iff : s = s ∪ t ↔ t ⊆ s := by
  sorry


end union


section inter    -- ## Propriétés de l'intersection

theorem inter_vide : s ∩ ∅ = ∅ := by
  sorry

theorem inter_self : s ∩ s = s := by
  sorry

theorem inter_comm : s ∩ t = t ∩ s := by
  sorry

theorem inter_assoc : r ∩ s ∩ t = r ∩ (s ∩ t) := by
  sorry

theorem inter_sub : r ∩ s ⊆ r := by
  sorry

theorem inter_eq_of_sub (h : r ⊆ s) : r = r ∩ s := by
  sorry

theorem sub_of_inter_eq (h : r = r ∩ s) : r ⊆ s := by
  sorry

theorem inter_eq_iff : s = s ∩ t ↔ s ⊆ t := by
  sorry

theorem subset_inter (hca: t ⊆ r) (hcb: t ⊆ s) : t ⊆ r ∩ s := by
  sorry

end inter


section distrib  -- ## Distributivité

theorem union_inter_left : r ∪ (s ∩ t) = (r ∪ s) ∩ (r ∪ t) := by
  sorry

theorem inter_union_left : r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t) := by
  sorry

theorem union_inter_self_left : s ∪ (s ∩ t) = s := by
  sorry

theorem inter_union_self_left : s ∩ (s ∪ t) = s := by
  sorry

end distrib


section compl  -- ## Propriétés du complémentaire

theorem compl_compl : sᶜᶜ = s := by
  sorry

end compl


section diff     -- ## Propriétés de la différence

theorem moins_vide_eq (s : Set α) : s \ ∅ = s := by
  sorry

theorem moins_univ_eq_vide (s : Set α) : s \ univ = ∅ := by
  sorry

theorem moins_eq_inter_compl (s t : Set α) : s \ t = s ∩ tᶜ := by
  sorry

end diff


section exercice  -- Trouver l'intrus !

-- L'une de ces propriétés est fausse. Trouvez un contre-exemple pour cette
-- propriété, et démontrez les autres.

-- theorem sub_union_of_sub_or_sub (h : r ⊆ s ∨ r ⊆ t) : r ⊆ s ∪ t := by
--   fail

-- theorem sub_sub_of_sub_union (h : r ⊆ s ∪ t) : r ⊆ s ∨ r ⊆ t := by
--   fail

-- theorem sub_inter_of_sub_and_sub (h : r ⊆ s ∧ r ⊆ t) : r ⊆ s ∩ t := by
--   fail

-- theorem sub_of_sub_inter_left (h : r ⊆ s ∩ t) : r ⊆ s := by
--   fail

-- theorem sub_of_sub_inter_right (h : r ⊆ s ∩ t) : r ⊆ t := by
--   fail

end exercice


section exercice

example (h: r ⊆ r ∩ s) : r ∪ s = s := by
  sorry

end exercice
