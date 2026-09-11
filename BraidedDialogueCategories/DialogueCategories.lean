module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

universe v

namespace CategoryTheory

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C]

class LeftClosed (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj₁ : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : MonoidalCategory.tensorLeft X ⊣ rightAdj

class RightClosed (X : C) where
  /-- a choice of a right adjoint for `tensorRight X` -/
  rightAdj₂ : C ⥤ C
  /-- `tensorRight X` is a left adjoint -/
  adj : MonoidalCategory.tensorRight X ⊣ rightAdj

variable (A : C)
variable [LeftClosed A]

variable (B : C)
variable [RightClosed B]

def leftIhom (A : C) [LeftClosed A] : C ⥤ C := LeftClosed.rightAdj₁ A
def rightIhom (B : C) [RightClosed B] : C ⥤ C := RightClosed.rightAdj₂ B

namespace ihoms

def adjunction₁ : MonoidalCategory.tensorLeft A ⊣ leftIhom A := LeftClosed.adj
def adjunction₂ : MonoidalCategory.tensorRight B ⊣ rightIhom B := RightClosed.adj

instance : (MonoidalCategory.tensorLeft A).IsLeftAdjoint := (ihoms.adjunction₁ A).isLeftAdjoint

instance : (leftIhom A).IsRightAdjoint := (ihoms.adjunction₁ A).isRightAdjoint

instance : (MonoidalCategory.tensorRight B).IsLeftAdjoint := (ihoms.adjunction₂ B).isLeftAdjoint

instance : (rightIhom B).IsRightAdjoint := (ihoms.adjunction₂ B).isRightAdjoint

/-- The evaluation natural transformation for the left internal hom. -/
def evLeft : leftIhom A ⋙ MonoidalCategory.tensorLeft A ⟶ 𝟭 C :=
  (ihoms.adjunction₁ A).counit

/-- The coevaluation natural transformation for the left internal hom. -/
def coevLeft : 𝟭 C ⟶ MonoidalCategory.tensorLeft A ⋙ leftIhom A :=
  (ihoms.adjunction₁ A).unit

/-- The evaluation natural transformation for the right internal hom. -/
def evRight : rightIhom B ⋙ MonoidalCategory.tensorRight B ⟶ 𝟭 C :=
  (ihoms.adjunction₂ B).counit

/-- The coevaluation natural transformation for the right internal hom. -/
def coevRight : 𝟭 C ⟶ MonoidalCategory.tensorRight B ⋙ rightIhom B :=
  (ihoms.adjunction₂ B).unit

class DialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] where
  bot : C
  ϕ : LeftClosed bot
  ψ : RightClosed bot

class StarAutonomousCategory (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [D : DialogueCategory C] where
  η₁ : letI := D.ϕ
       letI := D.ψ
       𝟭 C ≅ leftIhom D.bot ⋙ rightIhom D.bot

  η₂ : letI := D.ϕ
       letI := D.ψ
       𝟭 C ≅ rightIhom D.bot ⋙ leftIhom D.bot
