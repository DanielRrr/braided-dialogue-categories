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
