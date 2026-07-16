import LPA.TP3EnsemblesFonctions.«3FunctionsDefinitions»

namespace LPA

universe u
variable {α β γ : Type u}
variable {s s' : Set α} {t t' : Set β} {r r' : Set γ}
variable {f : α → β} {g : β → γ}

open Set

section singleton  -- ## Image d'un singleton

theorem image_singleton {x : α} : f '' {x} = {f x} := by
  sorry

end singleton


section comp  -- ## Image et préimage d'une composition de fonctions

theorem comp_preimage : g ∘ f ⁻¹' r = f ⁻¹' (g ⁻¹'  r) := by
  sorry

theorem comp_image : g ∘ f '' s = g '' (f '' s) := by
  sorry

end comp


section preimage_image -- ## Pré-image de l'image d'un ensemble

-- Seul l'un de ces deux thèorèmes est vrai.
-- Le démontrer, et trouver un contre-exemple pour l'autre.

-- theorem sub_preimage_image : s ⊆ f ⁻¹' (f '' s) := by
--   fail

-- theorem preimage_image_sub : f ⁻¹' (f '' s) ⊆ s := by
--   fail

end preimage_image


section image_preimage  -- ## Image de la pré-image d'un ensemble

-- Seul l'un de ces deux thèorèmes est vrai.
-- Le démontrer, et trouver un contre-exemple pour l'autre.

-- theorem sub_image_preimage : t ⊆ f '' (f ⁻¹' t) := by
--   fail

-- theorem image_preimage_sub : f '' (f ⁻¹' (t)) ⊆ t := by
--   fail

end image_preimage


section inclusions  -- ## Inclusion des images ou des préimages

theorem image_sub_of_sub (h : s ⊆ s') : f '' s ⊆ f '' s' := by
  sorry

theorem preimage_sub_of_sub (h : t ⊆ t') : f ⁻¹' t ⊆ f ⁻¹' t' := by
  sorry

end inclusions


section union  -- ## Image et pré-image d'une union

theorem image_union : f '' (s ∪ s') = f '' s ∪ f '' s' := by
  sorry

theorem preimage_union : f ⁻¹' ( t ∪ t') = f ⁻¹' t ∪ f ⁻¹' t' := by
  sorry

end union


section inter  -- ## Image et pré-image d'une intersection

theorem preimage_inter : f ⁻¹' ( t ∩ t') = f ⁻¹' t ∩ f ⁻¹' t' := by
  sorry

-- Seul l'un des deux thèorèmes suivants est vrai.
-- Le démontrer, et trouver un contre-exemple pour l'autre.

-- theorem image_inter_sub_inter_image : f '' (s ∩ s') ⊆ f '' s ∩ f '' s' := by
--   fail

-- theorem inter_image_sub_image_inter : f '' s ∩ f '' s' ⊆ f '' (s ∩ s') := by
--   fail

end inter
