import LPA.TP2LogiquePredicats

namespace LPA
-- set_option linter.unusedVariables false

universe u
variable {α : Type u}
variable {x : α}


-- Définition du type Set
-- Un ensemble est vu comme sa fonction caractéristique
def Set (α : Type u) := α → Prop

namespace Set

section appartenance  -- ## Relation d'appartenance

-- Relation d'appartenance
def Mem (s : Set α) (a : α) : Prop :=
  s a

-- Incantation pour pouvoir utiliser ∈
instance : Membership α (Set α) where
  mem := Set.Mem

-- Théorème utilitaire
theorem mem_def {s : Set α} : x ∈ s ↔ s x := by
  rfl

end appartenance


section inclusion  -- ## Relation d'inclusion

-- Relation d'inclusion
def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

-- Incantation pour pouvoir utiliser ⊆
instance instSubsetHasSubset : HasSubset (Set α) where
  Subset := Set.Subset

-- Théorème utilitaire
theorem subset_def {s₁ s₂ : Set α} :
    s₁ ⊆ s₂ ↔ ∀ x, x ∈ s₁ → x ∈ s₂ := by
  rfl

end inclusion


section egalite  -- ## Égalité entre ensembles

-- Magie noire ! Pas si facile de définir l'égalité d'ensembles
@[ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b := by
  -- les deux ensembles sont représentés par la même fonction
  funext x
  -- deux propriétés équivalentes sont considérées comme égales
  apply propext
  exact h x

#check Set.ext_iff  -- défini automatiquement grâce à @[ext]

end egalite


section vide_univ  -- ## Ensembles particuliers

-- Incantation pour pouvoir utiliser ∅
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

-- Invocation pour utiliser ∪
instance : Union (Set α) :=
  ⟨union⟩

-- Théorème utilitaire
theorem union_def {s₁ s₂ : Set α} :
    x ∈ s₁ ∪ s₂ ↔ x ∈ s₁ ∨ x ∈ s₂ := by
  rfl

end union


section intersection  -- ## Intersection

-- Opération d'intersection (et théorème compagnon)
def inter (s₁ s₂ : Set α) : Set α :=
  fun a ↦ a ∈ s₁ ∧ a ∈ s₂

-- Invocation pour utiliser ∩
instance : Inter (Set α) :=
  ⟨Set.inter⟩

-- Théorème utilitaire
theorem inter_def {s₁ s₂ : Set α} :
    x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂ := by
  rfl

end intersection


section complement  -- ## Complémentaire

-- Opération de complément
def compl (s : Set α) : Set α :=
  fun a ↦ a ∉ s

-- Invocation pour utiliser ᶜ
postfix:1024 "ᶜ" => compl

-- Théorème utilitaire
theorem compl_def {s : Set α} : x ∈ sᶜ ↔ x ∉ s := by
  rfl

end complement


section difference  -- ## Différence ensembliste

-- Opération de différence ensembliste
def diff (s t : Set α) : Set α :=
  fun a ↦ a ∈ s ∧ a ∉ t

-- Invocation pour utiliser \ (attention, saisir \\ !)
instance : SDiff (Set α) := ⟨Set.diff⟩

-- Théorème utilitaire
theorem diff_def {s₁ s₂ : Set α} :
    x ∈ s₁ \ s₂ ↔ x ∈ s₁ ∧ x ∉ s₂ := by
  rfl

end difference


section parties  -- ## Ensemble des parties (powerset)

-- Ensemble des parties
def powerset (s : Set α) : Set (Set α) :=
  fun t ↦ t ⊆ s

-- Invocation pour utiliser 𝒫
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
