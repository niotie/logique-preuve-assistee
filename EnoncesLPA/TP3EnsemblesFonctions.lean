import EnoncesLPA.TP2LogiquePredicats

namespace Local
set_option linter.unusedVariables false

universe u
variable {α β γ : Type u}

section definitions  -- # Définition des ensembles et des opérations courantes

-- Définition du type Set
-- Un ensemble est vu comme sa fonction caractéristique
def Set (α : Type u) := α → Prop

namespace Set

section appartenance  -- ## Relation d'appartenance

-- Relation d'appartenance
def Mem (s : Set α) (a : α) : Prop :=
  s a

-- Incantation pour pouvoir utiliser ∈ (saisir \in)
instance : Membership α (Set α) where
  mem := Set.Mem

-- Théorème utilitaire
theorem mem_def {x : α} {s : Set α} : x ∈ s ↔ s x := by
  rfl

end appartenance


section inclusion  -- ## Relation d'inclusion

-- Relation d'inclusion
def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

-- Incantation pour pouvoir utiliser ⊆ (saisir \sub)
instance instSubsetHasSubset : HasSubset (Set α) where
  Subset := Set.Subset

-- Théorème utilitaire
theorem subset_def {s₁ s₂ : Set α} :
    s₁ ⊆ s₂ ↔ ∀ x, x ∈ s₁ → x ∈ s₂ := by
  rfl

end inclusion


section egalite  -- ## Égalité entre ensembles

-- Magie noire ! Pas si facile de définir l'égalité d'ensembles
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b := by
  -- les deux ensembles sont représentés par la même fonction
  funext x
  -- deux propriétés équivalentes sont considérées comme égales
  apply propext
  exact h x

theorem ext_iff {a b : Set α} : (∀ (x : α), x ∈ a ↔ x ∈ b) ↔ a = b := by
  constructor
  . exact ext
  . intro hab x
    rewrite [hab]
    exact iff_refl

end egalite


section vide_univ  -- ## Ensembles particuliers

-- Incantation pour pouvoir utiliser ∅ (saisir \empty)
instance : EmptyCollection (Set α) :=
  ⟨fun _ ↦ False⟩

#check (∅ : Set α)

-- Ensemble "univers" (tous les éléments du domaine)
def univ : Set α := fun (_ : α) ↦ True

#check (univ : Set α)

end vide_univ


section union  -- ## Union

-- Opération d'union (et théorème compagnon)
def union (s₁ s₂ : Set α) : Set α :=
  fun a ↦ a ∈ s₁ ∨ a ∈ s₂

-- Invocation pour utiliser ∪ (saisir \union ou \cup)
instance : Union (Set α) :=
  ⟨union⟩

-- Théorème utilitaire
theorem union_def {s₁ s₂ : Set α} {x : α} :
    x ∈ s₁ ∪ s₂ ↔ x ∈ s₁ ∨ x ∈ s₂ := by
  rfl

end union


section intersection  -- ## Intersection

-- Opération d'intersection (et théorème compagnon)
def inter (s₁ s₂ : Set α) : Set α :=
  fun a ↦ a ∈ s₁ ∧ a ∈ s₂

-- Invocation pour utiliser ∩ (saisir \inter ou \cap)
instance : Inter (Set α) :=
  ⟨Set.inter⟩

-- Théorème utilitaire
theorem inter_def {s₁ s₂ : Set α} {x : α} :
    x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂ := by
  rfl

end intersection


section complement  -- ## Complémentaire

-- Opération de complément
def compl (s : Set α) : Set α :=
  fun a ↦ a ∉ s

-- Invocation pour utiliser ᶜ (saisir \compl)
postfix:1024 "ᶜ" => compl

-- Théorème utilitaire
theorem compl_def {s : Set α} {x : α} : x ∈ sᶜ ↔ x ∉ s := by
  rfl

end complement


section difference  -- ## Différence ensembliste

-- Opération de différence ensembliste
def diff (s t : Set α) : Set α :=
  fun a ↦ a ∈ s ∧ a ∉ t

-- Invocation pour utiliser \ (attention, saisir \\ ou \setminus !)
instance : SDiff (Set α) := ⟨Set.diff⟩

-- Théorème utilitaire
theorem diff_def {s₁ s₂ : Set α} {x : α} :
    x ∈ s₁ \ s₂ ↔ x ∈ s₁ ∧ x ∉ s₂ := by
  rfl

end difference


section parties  -- ## Ensemble des parties (powerset)

-- Ensemble des parties
def powerset (s : Set α) : Set (Set α) :=
  fun t ↦ t ⊆ s

-- Invocation pour utiliser 𝒫 (saisir \powerset)
prefix:1000 "𝒫" => powerset

-- Théorème utilitaire
theorem powerset_def {s t : Set α} : t ∈ 𝒫 s ↔ t ⊆ s := by
  rfl

end parties


section extension  -- ## Notations en extension

-- Ensemble à un élément (singleton)
@[reducible] def singleton (a : α) : Set α :=
  fun b ↦ b = a

-- Incantation pour utiliser la syntaxe {a}
instance : Singleton α (Set α) where
  singleton := singleton

#check ({1} : Set Nat)

-- Insertion dans un ensemble
def insert (a : α) (s : Set α) : Set α :=
  fun b ↦ b = a ∨ b ∈ s

-- Incantation pour utiliser la syntaxe {a, b, c}
instance : Insert α (Set α) where
  insert := insert

#check ({1, 2, 3} : Set Nat)

end extension

end Set

end definitions


open Set

section prop_ensembles  -- # Propriétés relatives aux ensembles

variable  {r s t : Set α}

section subset  -- ## Propriétés liées à la relation ⊆

@[refl]
theorem subset_refl : s ⊆ s := by
  -- rewrite [subset_def]
  intro a
  exact imp_refl
  -- ou :
  -- intro h
  -- exact h

theorem subset_antisymm {s t : Set α} (h : s ⊆ t) (h' : t ⊆ s) : s = t := by
  apply ext
  intro a
  constructor
  . intro hs
    apply h
    exact hs
    -- ou :
    -- have ht : a ∈ t := h hs
    -- exact ht
    -- ou :
    -- exact h hs
  . sorry

theorem subset_trans (hrs : r ⊆ s) (hst : s ⊆ t) : r ⊆ t := by
  intro x hxr
  -- raisonnement "en arrière"
  apply hst
  apply hrs
  exact hxr

example (hrs : r ⊆ s) (hst : s ⊆ t) : r ⊆ t := by
  intro x hxr
  -- raisonnement "en avant"
  specialize hrs hxr
  specialize hst hrs
  exact hst

example (hrs : r ⊆ s) (hst : s ⊆ t) : r ⊆ t := by
  intro x hxr
  -- raisonnement "en avant" (autre forme)
  have hxs : x ∈ s := by
    apply hrs
    exact hxr
  have hxt : x ∈ t := by
    apply hst
    exact hxs
  exact hxt



end subset


section singleton  -- ## Propriétés des singletons

theorem mem_singleton_iff {x x' : α} : x ∈ ({x'} : Set α) ↔ x = x' := by
  rfl

theorem eq_singleton_iff {x x' : α} : {x} = ({x'} : Set α) ↔ x = x' := by
  constructor
  . intro h
    rewrite [← ext_iff] at h
    specialize h x
    rewrite [← mem_singleton_iff]
    rewrite [← h]
    rfl
  . intro h
    rewrite [h]
    rfl



theorem sub_singleton_iff {x x' : α} : {x} ⊆ ({x'} : Set α) ↔ x = x' := by
  sorry

end singleton


section union    -- ## Propriétés de l'union

theorem union_empty (s : Set α) : s ∪ ∅ = s := by
  apply subset_antisymm
  . intro x h
    rcases h with (h | h)
    . exact h
    . contradiction
  . intro x h
    left
    exact h

theorem union_univ (s : Set α) : s ∪ univ = univ := by
  apply subset_antisymm
  . intro x h
    trivial
  . intro x _
    right
    trivial

theorem union_comm : s ∪ t = t ∪ s := by
  apply ext
  intro x
  rewrite [union_def, or_comm]
  rfl

theorem union_assoc {r s t : Set α} : r ∪ s ∪ t = r ∪ (s ∪ t) := by
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

theorem union_inter_left {r s t : Set α} : r ∪ (s ∩ t) = (r ∪ s) ∩ (r ∪ t) := by
  sorry

theorem inter_union_left {r s t : Set α} : r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t) := by
  sorry

theorem union_inter_self_left : s ∪ (s ∩ t) = s := by
  sorry

theorem inter_union_self_left : s ∩ (s ∪ t) = s := by
  sorry

end distrib


section diff     -- ## Propriétés de la différence

theorem moins_vide_eq (s : Set α) : s \ ∅ = s := by
  sorry

theorem moins_univ_eq_vide (s : Set α) : s \ univ = ∅ := by
  sorry

theorem moins_eq_inter_compl (s t : Set α) : s \ t = s ∩ tᶜ := by
  sorry

end diff


section exercice  -- Trouver l'intrus !

-- L'une de ces propriétés est fausse. Démontrez les autres.

-- theorem sub_union_of_sub_or_sub {r s t : Set α} (h : r ⊆ s ∨ r ⊆ t) : r ⊆ s ∪ t := by

-- theorem sub_sub_of_sub_union {r s t : Set α} (h : r ⊆ s ∪ t) : r ⊆ s ∨ r ⊆ t := by

-- theorem sub_inter_of_sub_and_sub {r s t : Set α} (h : r ⊆ s ∧ r ⊆ t) : r ⊆ s ∩ t := by

-- theorem sub_of_sub_inter_left {r s t : Set α} (h : r ⊆ s ∩ t) : r ⊆ s := by

-- theorem sub_of_sub_inter_right {r s t : Set α} (h : r ⊆ s ∩ t) : r ⊆ t := by

end exercice


section exercice

example (h: r ⊆ r ∩ s) : r ∪ s = s := by
  sorry

end exercice

end prop_ensembles


section defs_fonctions  -- # Définitions relatives aux fonctions

variable  {α β γ : Type u}

section image    -- ## Image d'un ensemble

-- Image d'un ensemble par une fonction
def image (f : α → β) (s : Set α) : Set β :=
  fun b ↦ ∃ a, a ∈ s ∧ f a = b

infixl:80 " '' " => image

#check (id '' _ : Set _)

-- Théorèmes utilitaires
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

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
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl

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


section prop_fonctions  -- # Propriétés sur les fonctions

variable {s s' : Set α} {t t' : Set β} {r r' : Set γ}
variable {f : α → β} {g : β → γ}


section singleton  -- ## Image d'un singleton

theorem image_singleton : f '' {x} = {f x} := by
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

theorem sub_preimage_image : s ⊆ f ⁻¹' (f '' s) := by
  intro x
  intro h
  rewrite [mem_preimage]
  rewrite [mem_image]
  exists x

-- theorem preimage_image_sub : f ⁻¹' (f '' s) ⊆ s := by
--   intro x h
--   rewrite [mem_preimage] at h
--   rcases h with ⟨x', h, h'⟩
--   sorry

end preimage_image


section image_preimage  -- ## Image de la pré-image d'un ensemble

-- Seul l'un de ces deux thèorèmes est vrai.
-- Le démontrer, et trouver un contre-exemple pour l'autre.

-- theorem sub_image_preimage : t ⊆ f '' (f ⁻¹' t) := by
--   intro x h
--   rewrite [mem_image]
--   exists y
--   rewrite [mem_preimage]
--   sorry

theorem image_preimage_sub : f '' (f ⁻¹' (t)) ⊆ t := by
  intro x h
  rcases h with ⟨y, hy, hy'⟩
  rewrite [← hy']
  exact hy

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

end prop_fonctions


section prop_inj_surj  -- # Propositions relatives aux fonctions injectives et surjectives

variable {s s' : Set α} {t t' : Set β} {r r' : Set γ}
variable {f : α → β} {g : β → γ}

open Set

section inj_comp  -- ## Injectivité, surjectivité et composition

theorem inj_comp (h1 : injective f) (h2 : injective g) : injective (g ∘ f) := by
  sorry

theorem surj_comp (h1 : surjective f) (h2 : surjective g) : surjective (g ∘ f) := by
  sorry

-- Seuls deux des quatres thèorèmes suivants sont vrais.
-- Les démontrer, et trouver un contre-exemple pour chacun des deux autres.

-- theorem inj_left_of_inj_comp (h : injective (g ∘ f)) : injective g := by
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

theorem preimage_image_sub_of_inj (h : injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h'
  rewrite [mem_preimage] at h'
  rcases h' with ⟨x', hx'1, hx'2⟩
  specialize h x' x hx'2
  subst h
  exact hx'1

-- theorem preimage_image_sub_of_surj (h : surjective f) : f ⁻¹' (f '' s) ⊆ s := by
--   fail

-- theorem sub_image_preimage_of_inj (h : injective f) : t ⊆ f '' (f ⁻¹' t) := by
--   fail

theorem sub_image_preimage_of_surj (h : surjective f) : t ⊆ f '' (f ⁻¹' t) := by
  intro y h'
  specialize h y
  rcases h with ⟨a, ha⟩
  exists a
  constructor
  . subst ha
    exact h'
  . exact ha

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


end prop_inj_surj
