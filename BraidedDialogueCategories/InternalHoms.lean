module

public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C]

/-!
  Individual internal homs
-/

/--
`[A, B]ₗ` exists if the functor `X ↦ X ⊗ A`
has a representing object for morphisms into `B`. Equivalently, there is an object `H` such that
`Hom(X ⊗ A, B) ≃ Hom(X, H)` naturally in `X`.
-/
class HasLeftIhom (A B : C) where
  internalHomₗ : C
  homEquiv : ∀ X : C, (A ⊗ X ⟶ B) ≃ (X ⟶ internalHomₗ)
  homEquivNaturalityₗ :
    ∀ {X Y : C} (f : X ⟶ Y) (g : A ⊗ Y ⟶ B),
      homEquiv X ((𝟙 A ⊗ₘ f) ≫ g) =
        f ≫ homEquiv Y g

/--
The left internal hom `[A, B]ₗ`.
-/
abbrev leftIhom (A B : C) [ihom : HasLeftIhom A B] : C :=
  HasLeftIhom.internalHomₗ A B

namespace HasLeftIhom

variable {A B : C} [HasLeftIhom A B]

/-- The universal evaluation map for left internal homs. -/
def leftEval : A ⊗ internalHomₗ A B ⟶ B :=
  (homEquiv (internalHomₗ A B)).symm (𝟙 (internalHomₗ A B))

/-- Pins down `(homEquiv X).symm` purely in terms of `eval`. -/
lemma symm_apply_eq {X : C} (k : X ⟶ internalHomₗ A B) :
    (homEquiv X).symm k = (𝟙 A ⊗ₘ k) ≫ leftEval := by
  apply (homEquiv X).injective
  rw [Equiv.apply_symm_apply, homEquivNaturalityₗ]
  simp [leftEval]

variable {A₁ A₂ : C} [HasLeftIhom A₁ B] [HasLeftIhom A₂ B]

/-- The left internal hom contramap. -/
def contramap (g : A₁ ⟶ A₂) : internalHomₗ A₂ B ⟶ internalHomₗ A₁ B :=
  homEquiv (A := A₁) (internalHomₗ A₂ B) ((g ⊗ₘ 𝟙 _) ≫ leftEval)

/-- The naturality square `hleft` was reconstructing by hand. -/
lemma homEquiv_naturality_left {X : C} (g : A₁ ⟶ A₂) (f : A₂ ⊗ X ⟶ B) :
    homEquiv (A := A₁) X ((g ⊗ₘ 𝟙 X) ≫ f) =
      homEquiv (A := A₂) X f ≫ contramap g := by
  set φ := homEquiv (A := A₂) X f with hφ
  have hf : f = (𝟙 A₂ ⊗ₘ φ) ≫ leftEval := by
    have h1 : (homEquiv (A := A₂) X).symm φ = (𝟙 A₂ ⊗ₘ φ) ≫ leftEval := symm_apply_eq φ
    have h2 : (homEquiv (A := A₂) X).symm φ = f := by
      rw [hφ]; exact Equiv.symm_apply_apply _ f
    rw [← h2]; exact h1
  rw [hf, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [show g ⊗ₘ φ = (𝟙 A₁ ⊗ₘ φ) ≫ (g ⊗ₘ 𝟙 (internalHomₗ A₂ B)) from by
      rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]]
  rw [Category.assoc, homEquivNaturalityₗ]
  rfl

lemma symm_naturality_left {X : C} (g : A₁ ⟶ A₂) (ψ : X ⟶ internalHomₗ A₂ B) :
    (g ⊗ₘ 𝟙 X) ≫ (homEquiv (A := A₂) X).symm ψ =
      (homEquiv (A := A₁) X).symm (ψ ≫ contramap g) := by
  apply (homEquiv (A := A₁) X).injective
  rw [Equiv.apply_symm_apply]
  rw [homEquiv_naturality_left]
  rw [Equiv.apply_symm_apply]

/-- Naturality of `(homEquiv _).symm` in the representing object (postcomposition). -/
lemma symm_comp {X Y : C} (m : X ⟶ Y) (k : Y ⟶ internalHomₗ A B) :
    (homEquiv X).symm (m ≫ k) = (𝟙 A ⊗ₘ m) ≫ (homEquiv Y).symm k := by
  apply (homEquiv X).injective
  rw [Equiv.apply_symm_apply, homEquivNaturalityₗ, Equiv.apply_symm_apply]

/-- Uncurry∘curry cancels back to the original map. -/
lemma uncurry_curry {X : C} (φ : A ⊗ X ⟶ B) :
    (𝟙 A ⊗ₘ homEquiv X φ) ≫ leftEval = φ := by
  rw [← symm_apply_eq, Equiv.symm_apply_apply]
end HasLeftIhom

/--
`[A, B]ᵣ` exists if there is an object `H` such that `Hom(A ⊗ X, B) ≃ Hom(X, H)` naturally in `X`.
-/
class HasRightIhom (A B : C) where
  internalHomᵣ : C
  homEquiv : ∀ X : C, (X ⊗ A ⟶ B) ≃ (X ⟶ internalHomᵣ)
  homEquivNaturalityᵣ :
    ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⊗ A ⟶ B),
      homEquiv X ((f ⊗ₘ 𝟙 A) ≫ g) = f ≫ homEquiv Y g


/--
The right internal hom `[A, B]ᵣ`.
-/
def rightIhom (A B : C) [HasRightIhom A B] : C :=
  HasRightIhom.internalHomᵣ A B

namespace HasRightIhom

variable {A B : C} [HasRightIhom A B]

def evalRight : internalHomᵣ A B ⊗ A ⟶ B :=
  (homEquiv (internalHomᵣ A B)).symm (𝟙 (internalHomᵣ A B))

lemma symm_apply_eq {X : C} (k : X ⟶ internalHomᵣ A B) :
    (homEquiv X).symm k = (k ⊗ₘ 𝟙 A) ≫ evalRight := by
  apply (homEquiv X).injective
  rw [Equiv.apply_symm_apply, homEquivNaturalityᵣ]
  simp [evalRight]

variable {A₁ A₂ : C} [HasRightIhom A₁ B] [HasRightIhom A₂ B]

def contramap (g : A₁ ⟶ A₂) : internalHomᵣ A₂ B ⟶ internalHomᵣ A₁ B :=
  homEquiv (A := A₁) (internalHomᵣ A₂ B) ((𝟙 _ ⊗ₘ g) ≫ evalRight)

lemma homEquiv_naturality_left {X : C} (g : A₁ ⟶ A₂) (f : X ⊗ A₂ ⟶ B) :
    homEquiv (A := A₁) X ((𝟙 X ⊗ₘ g) ≫ f) =
      homEquiv (A := A₂) X f ≫ contramap g := by
  set φ := homEquiv (A := A₂) X f with hφ
  have hf : f = (φ ⊗ₘ 𝟙 A₂) ≫ evalRight := by
    have h1 : (homEquiv (A := A₂) X).symm φ = (φ ⊗ₘ 𝟙 A₂) ≫ evalRight := symm_apply_eq φ
    have h2 : (homEquiv (A := A₂) X).symm φ = f := by
      rw [hφ]; exact Equiv.symm_apply_apply _ f
    rw [← h2]; exact h1
  rw [hf, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [show φ ⊗ₘ g = (φ ⊗ₘ 𝟙 A₁) ≫ (𝟙 (internalHomᵣ A₂ B) ⊗ₘ g) from by rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]]
  rw [Category.assoc, homEquivNaturalityᵣ]
  rfl

lemma symm_naturality_left {X : C} (g : A₁ ⟶ A₂) (ψ : X ⟶ internalHomᵣ A₂ B) :
    (𝟙 X ⊗ₘ g) ≫ (homEquiv (A := A₂) X).symm ψ =
      (homEquiv (A := A₁) X).symm (ψ ≫ contramap g) := by
  apply (homEquiv (A := A₁) X).injective
  rw [Equiv.apply_symm_apply]
  rw [homEquiv_naturality_left]
  rw [Equiv.apply_symm_apply]

lemma symm_comp {X Y : C} (m : X ⟶ Y) (k : Y ⟶ internalHomᵣ A B) :
    (homEquiv X).symm (m ≫ k) = (m ⊗ₘ 𝟙 A) ≫ (homEquiv Y).symm k := by
  apply (homEquiv X).injective
  rw [Equiv.apply_symm_apply, homEquivNaturalityᵣ, Equiv.apply_symm_apply]

lemma uncurry_curry {X : C} (φ : X ⊗ A ⟶ B) :
    (homEquiv X φ ⊗ₘ 𝟙 A) ≫ evalRight = φ := by
  rw [← symm_apply_eq, Equiv.symm_apply_apply]
end HasRightIhom

/--
`C` is left closed at `B` if `[A, B]ₗ` exists for every `A`.
-/
class LeftClosedAt (B : C) where
  hasLeftIhom : ∀ A : C, HasLeftIhom A B

instance (A B : C) [LeftClosedAt B] : HasLeftIhom A B :=
  LeftClosedAt.hasLeftIhom A

/--
`C` is right closed at `B` if `[A, B]ᵣ` exists for every `A`.
-/
class RightClosedAt (B : C) where
  hasRightIhom : ∀ A : C, HasRightIhom A B

instance (A B : C) [RightClosedAt B] : HasRightIhom A B :=
  RightClosedAt.hasRightIhom A
