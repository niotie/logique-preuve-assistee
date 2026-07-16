import LPA.TP3EnsemblesFonctions.«4FunctionProperties»

namespace LPA
-- set_option linter.unusedVariables false

universe u
variable {α β γ : Type u}
variable {s s' : Set α} {t t' : Set β} {r r' : Set γ}
variable {f : α → β} {g : β → γ}

-- # Propositions relatives aux fonctions injectives et surjectives

open Set

section inj_comp  -- ## Injectivité, surjectivité et composition

theorem inj_comp (h1 : injective f) (h2 : injective g) : injective (g ∘ f) := by
  sorry

theorem surj_comp (h1 : surjective f) (h2 : surjective g) : surjective (g ∘ f) := by
  sorry

-- Seuls deux des quatres thèorèmes suivants sont vrais.
-- Les démontrer, et trouver un contre-exemple pour chacun des deux autres.

-- example (h : injective (g ∘ f)) : injective g := by
--   fail

-- theorem inj_right_of_inj_comp (h : injective (g ∘ f)) : injective f := by
--   fail

-- theorem surj_left_of_surj_comp (h : surjective (g ∘ f)) : surjective g := by
--   fail

-- theorem surj_right_of_surj_comp (h : surjective (g ∘ f)) : surjective f := by
--   fail

end inj_comp


section inter   -- ## Retour sur l'intersection des images

-- Seul l'un des deux thèorèmes suivants est vrai.
-- Le démontrer, et trouver un contre-exemple pour l'autre.

-- theorem inter_image_sub_image_inter_of_inj (h : injective f) :
--     f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by
--   fail

-- theorem inter_image_sub_image_inter_of_surj (h : surjective f) :
--     f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by
--   fail


end inter


section preimage_image  -- ## Retour sur image et préimage

-- Seuls deux des quatres thèorèmes suivants sont vrais.
-- Les démontrer, et trouver un contre-exemple pour chacun des deux autres.

-- theorem preimage_image_sub_of_inj (h : injective f) : f ⁻¹' (f '' s) ⊆ s := by
--   fail

-- theorem preimage_image_sub_of_surj (h : surjective f) : f ⁻¹' (f '' s) ⊆ s := by
--   fail

-- theorem sub_image_preimage_of_inj (h : injective f) : t ⊆ f '' (f ⁻¹' t) := by
--   fail

-- theorem sub_image_preimage_of_surj (h : surjective f) : t ⊆ f '' (f ⁻¹' t) := by
--   fail

end preimage_image


section carac_inj  -- ## Caractérisations de l'injectivité

section carac_inj_1

theorem inj_of_eq_preimage_image (h: ∀ s, f ⁻¹' (f '' s) ⊆ s) : injective f := by
  sorry

theorem inj_iff_eq_preimage_image : injective f ↔ ∀ s, f ⁻¹' (f '' s) ⊆ s := by
  sorry

end carac_inj_1


section carac_inj_2

theorem inj_of_sub_of_sub_image (h: ∀ s s', f '' s ⊆ f '' s' → s ⊆ s') : injective f := by
  sorry

theorem sub_of_sub_image_of_inj (h : injective f) (h' : f '' s ⊆ f '' s') : s ⊆ s' := by
  sorry

theorem inj_iff_sub_of_sub_image : injective f ↔ ∀ s s', f '' s ⊆ f '' s' → s ⊆ s' := by
  sorry

end carac_inj_2


section carac_inj_3

theorem inj_of_inter_image_sub_image_inter
    (h: ∀ s s', f '' s ∩ f '' s' ⊆ f '' (s ∩ s')) : injective f := by
  sorry

theorem inj_iff_inter_image_sub_image_inter :
    injective f ↔ ∀ s s', f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by
  sorry

end carac_inj_3


section carac_inj_4

theorem image_compl_sub_compl_image_of_inj :
    injective f → ∀ s, f '' sᶜ ⊆ (f '' s)ᶜ := by
  sorry

theorem inj_of_image_compl_sub_compl_image :
    (∀ s, f '' sᶜ ⊆ (f '' s)ᶜ) → injective f := by
  sorry

theorem inj_iff_image_compl_sub_compl_image :
    injective f ↔ ∀ s, f '' sᶜ ⊆ (f '' s)ᶜ := by
  sorry

end carac_inj_4

end carac_inj


section carac_surj  -- ## Caractérisations de la surjectivité

section carac_surj_1

theorem surj_of_sub_image_preimage (h : ∀ t, t ⊆ f '' (f ⁻¹' t)) : surjective f := by
  sorry

theorem surj_iff_sub_image_preimage :
    surjective f ↔ ∀ s, s ⊆ f '' (f ⁻¹' s) := by
  sorry

end carac_surj_1


section carac_surj_2

theorem surj_iff_univ_sub_image_preimage_univ :
    surjective f ↔ univ ⊆ f '' (f ⁻¹' univ) := by
  sorry

end carac_surj_2


section carac_surj_3

theorem surj_of_sub_of_sub_preimage (h : ∀ t t', f ⁻¹' t ⊆ f ⁻¹' t' → t ⊆ t') : surjective f := by
  sorry

theorem sub_of_sub_preimage_of_surj (h : surjective f) (h' : f ⁻¹' t ⊆ f ⁻¹' t') : t ⊆ t' := by
  sorry

theorem surj_iff_sub_of_sub_preimage : surjective f ↔ ∀ t t', f ⁻¹' t ⊆ f ⁻¹' t' → t ⊆ t' := by
  sorry

end carac_surj_3


section carac_surj_4

theorem image_compl_sub_compl_image_of_surj :
    surjective f → ∀ s, (f '' s)ᶜ ⊆ f '' sᶜ := by
  sorry

theorem surj_of_image_compl_sub_compl_image :
    (∀ s, (f '' s)ᶜ ⊆ f '' sᶜ) → surjective f := by
  sorry

theorem surj_iff_image_compl_sub_compl_image :
    surjective f ↔ ∀ s, (f '' s)ᶜ ⊆ f '' sᶜ := by
  sorry

end carac_surj_4


section carac_surj_5

theorem surj_iff_exists_right_inverse :
    surjective f ↔ ∃ f', f ∘ f' = id := by
  -- L'une des directions utilise `Classical.choose` et `Classical.choose_spec`
  sorry

end carac_surj_5

end carac_surj


section divers  -- ## Propriétés diverses

section inj_surj

theorem inj_of_comp_inj_surj (hi : injective (g ∘ f)) (hs : surjective f) : injective g := by
  sorry

end inj_surj


section categ  -- Injectivité et surjectivité "catégorielles"

theorem categorical_injectivity {f1 : α → β} {f2 : α → β}
    (h : injective g) (h' : g ∘ f1 = g ∘ f2) : f1 = f2 := by
  sorry

theorem categorical_surjectivity {g1: β → γ} {g2: β → γ}
    (h : surjective f) (h' : g1 ∘ f = g2 ∘ f) : g1 = g2 := by
  sorry

end categ

end divers
