module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import BraidedDialogueCategories.MonadicStrength
public import Mathlib.Logic.Equiv.Defs

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
def leftIhom (A B : C) [ihom : HasLeftIhom A B] : C :=
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

/--
A distinguished object `bot` for which both families `[A, bot]ₗ` and `[A, bot]ᵣ` exist for every `A`.
-/
class DialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C] where
  bot : C
  [leftClosed : LeftClosedAt bot]
  [rightClosed : RightClosedAt bot]

namespace DialogueCategory

variable [D : DialogueCategory C]

/-- `[A, bot]ₗ`. -/
abbrev leftDual (A : C) : C :=
  letI := D.leftClosed
  HasLeftIhom.internalHomₗ A D.bot

/-- The left evaluation arrow `A ⊗ [A, bot]ᵣ ⟶ bot`-/
def leval (A : C) : A ⊗ leftDual A ⟶ bot :=
  letI := D.leftClosed
  (HasLeftIhom.homEquiv (A := A) (B := DialogueCategory.bot) (leftDual A)).symm (𝟙 (leftDual A))

/-- `leftDual` is a contravariant functor. -/
def leftDualMap {A B : C} (f : A ⟶ B) : leftDual B ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv
      (A := A)
      (B := DialogueCategory.bot)
      (leftDual B)
      ((f ⊗ₘ 𝟙 (leftDual B)) ≫ leval B)

def leftDualFunctor : Cᵒᵖ ⥤ C where
  obj A := leftDual A.unop
  map := fun {X Y} f =>
    letI := D.leftClosed
    HasLeftIhom.homEquiv
      (A := Y.unop)
      (B := D.bot)
      (leftDual X.unop)
      ((f.unop ⊗ₘ 𝟙 (leftDual X.unop)) ≫ leval X.unop)
  map_id X := sorry
  map_comp f g := sorry

/-- `[A, bot]ᵣ`. -/
abbrev rightDual (A : C) : C :=
  letI := D.rightClosed
  HasRightIhom.internalHomᵣ A D.bot

/-- The right evaluation arrow `[A, bot]ᵣ ⊗ A ⟶ bot`-/
def reval (A : C) : rightDual A ⊗ A ⟶ bot :=
  letI := D.rightClosed
  (HasRightIhom.homEquiv (A := A) (B := DialogueCategory.bot) (rightDual A)).symm (𝟙 (rightDual A))

/-- `rightDual` is a contravariant functor. -/
def rightDualMap {A B : C} (f : A ⟶ B) : rightDual B ⟶ rightDual A :=
  letI := D.rightClosed
  HasRightIhom.homEquiv
    (A := A)
    (B := DialogueCategory.bot)
    (rightDual B)
    ((𝟙 (rightDual B) ⊗ₘ f) ≫ reval B)

def lev (B A : C) : B ⊗ leftDual (A ⊗ B) ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv
      (A := A)
      (B := DialogueCategory.bot)
      (B ⊗ leftDual (A ⊗ B))
      ((associator A B (leftDual (A ⊗ B))).inv ≫
        leval (A ⊗ B))

def rev (A B : C) : (rightDual (A ⊗ B)) ⊗ A ⟶ rightDual B :=
  letI := D.rightClosed
  HasRightIhom.homEquiv
    (A := B)
    (B := DialogueCategory.bot)
    (rightDual (A ⊗ B) ⊗ A)
    ((associator (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B))

def leftName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv
    (A := A)
    (B := D.bot)
    (𝟙_ C)
    ((rightUnitor A).hom ≫ f)

lemma leftName_uncurry (A : C) (f : A ⟶ bot) :
    ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A =
      (rightUnitor A).hom ≫ f := by
  letI := D.leftClosed
  let e₀ :=
    HasLeftIhom.homEquiv
      (A := A)
      (B := D.bot)
      (𝟙_ C)
  let e₁ :=
    HasLeftIhom.homEquiv
      (A := A)
      (B := D.bot)
      (leftDual A)
  apply e₀.injective
  rw [HasLeftIhom.homEquivNaturalityₗ
    (A := A)
    (B := D.bot)
    (f := leftName A f)
    (g := leval A)]
  change
    leftName A f ≫ e₁ (e₁.symm (𝟙 (leftDual A))) =
      e₀ ((rightUnitor A).hom ≫ f)
  rw [e₁.apply_symm_apply]
  simp [leftName, e₀]

def rightName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ rightDual A :=
  letI := D.rightClosed
  HasRightIhom.homEquiv
    (A := A)
    (B := D.bot)
    (𝟙_ C)
    ((leftUnitor A).hom ≫ f)

lemma leftNameFact (A : C) (f : A ⟶ bot) : f = (rightUnitor A).inv ≫ ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A := by
  rw [leftName_uncurry]
  simp

-- structure Turn (A : C) where
--  turn : leftDual A ≅ rightDual A
--  turnNaturality : ∀ {A B : C} (f : A ⟶ B),
--    leftDual.map f ≫ (turn B).hom =
--      (turn A).hom ≫ rightDual.map f

structure Wheel (A B : C) where
  wheel : (A ⊗ B ⟶ bot) ≃ (B ⊗ A ⟶ bot)
  wheelNatInA : sorry
  wheelNatInB : sorry


end DialogueCategory

open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category.{v} C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ leftDual (rightDual A)
  etaStar₂ : ∀ A : C, A ≅ rightDual (leftDual A)
