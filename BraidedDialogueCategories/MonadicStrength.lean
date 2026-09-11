module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Monad.Basic

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C]

class LeftStrength (T : Monad C) where
  leftStrength : (X Y : C) → (T.obj X) ⊗ Y ⟶ (T.obj) (X ⊗ Y)
  leftStrengthEq₁ : (X Y : C) → T.η.app (X ⊗ Y) = (T.η.app X ⊗ₘ 𝟙 Y) ≫ (leftStrength X Y)
  leftStrengthEq₂ : (X Y Z : C) →
    leftStrength X (Y ⊗ Z) =
    ((associator (T.obj X) Y Z).inv) ≫
      ((leftStrength X Y) ⊗ₘ (𝟙 Z))
      ≫ leftStrength (X ⊗ Y) Z
      ≫ T.map (associator X Y Z).hom
  leftStrengthNaturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    leftStrength X Y ≫ T.map (f ⊗ₘ g) =
      (T.map f ⊗ₘ g) ≫ leftStrength X' Y'

class RightStrength (T : Monad C) where
  rightStrength : (X Y : C) → X ⊗ T.obj Y ⟶ (T.obj) (X ⊗ Y)
  rightStrengthEq₁ : (X Y : C) → T.η.app (X ⊗ Y) = (𝟙 X ⊗ₘ T.η.app Y) ≫ (rightStrength X Y)
  rightStrengthEq₂ : (X Y Z : C) →
    (associator X Y (T.obj Z)).inv ≫ rightStrength (X ⊗ Y) Z =
      ((𝟙 X) ⊗ₘ rightStrength Y Z) ≫
      rightStrength X (Y ⊗ Z) ≫ T.map (associator X Y Z).inv
  rightStrengthNaturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    rightStrength X Y ≫ T.map (f ⊗ₘ g) =
      (f ⊗ₘ T.map g) ≫ rightStrength X' Y'
