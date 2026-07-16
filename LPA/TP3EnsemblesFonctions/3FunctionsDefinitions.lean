import LPA.TP3EnsemblesFonctions.«2SetProperties»

namespace LPA
-- set_option linter.unusedVariables false

universe u
variable {α β γ : Type u}

open Set


section defs_fonctions  -- # Définitions relatives aux fonctions

variable  {α β γ : Type u}

section image    -- ## Image d'un ensemble

-- Image d'un ensemble par une fonction
def image (f : α → β) (s : Set α) : Set β :=
  fun b ↦ ∃ a, a ∈ s ∧ f a = b

infixl:80 " '' " => image

#check (id '' _ : Set _)

-- Théorèmes utilitaires
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y := by
  rfl

theorem mem_image_of_mem {f : α → β} {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

end image


section preim    -- ## Image réciproque (pré-image) d'un ensemble

-- Image réciproque d'un ensemble par une fonction
def preimage (f : α → β) (s : Set β) : Set α :=
  fun x => f x ∈ s

-- Incantation pour utiliser ⁻¹ (taper \preim)
infixl:80 " ⁻¹' " => preimage

-- Théorème utilitaire
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s := by
  rfl

end preim


section divers   -- ## Autres définitions sur les fonctions

-- Composition de fonctions
#check Function.comp
#check Function.comp_def
#check Function.comp_apply
#check Function.comp_const

-- Extensionnalité
#check funext
#check funext_iff

end divers


section inj_surj -- ## Injectivité, surjectivité, bijectivité

-- Injectivité
def injective (f : α → β) : Prop := ∀ x y, f x = f y → x = y

-- Surjectivité
def surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y

-- Bijectivité
def bijective (f : α → β) : Prop := injective f ∧ surjective f

end inj_surj


end defs_fonctions
