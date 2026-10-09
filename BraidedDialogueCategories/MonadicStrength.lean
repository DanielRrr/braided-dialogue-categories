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
  leftStrength : (X Y : C) → X ⊗ T.obj Y ⟶ (T.obj) (X ⊗ Y)
  leftStrengthEq₁ : (X Y : C) → T.η.app (X ⊗ Y) = (𝟙 X ⊗ₘ T.η.app Y) ≫ (leftStrength X Y)
  leftStrengthEq₂ : (X Y Z : C) →
    (associator X Y (T.obj Z)).inv ≫ leftStrength (X ⊗ Y) Z =
      ((𝟙 X) ⊗ₘ leftStrength Y Z) ≫
      leftStrength X (Y ⊗ Z) ≫ T.map (associator X Y Z).inv
  leftStrengthAssoc :
    ∀ X Y Z : C,
      leftStrength (X ⊗ Y) Z ≫ T.map (associator X Y Z).hom =
        (associator X Y (T.obj Z)).hom ≫ (𝟙 X ⊗ₘ leftStrength Y Z) ≫leftStrength X (Y ⊗ Z)
  leftStrengthNaturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    leftStrength X Y ≫ T.map (f ⊗ₘ g) =
      (f ⊗ₘ T.map g) ≫ leftStrength X' Y'

class RightStrength (T : Monad C) where
  rightStrength : (X Y : C) → (T.obj X) ⊗ Y ⟶ (T.obj) (X ⊗ Y)
  rightStrengthEq₁ : (X Y : C) → T.η.app (X ⊗ Y) = (T.η.app X ⊗ₘ 𝟙 Y) ≫ (rightStrength X Y)
  rightStrengthEq₂ : (X Y Z : C) →
    rightStrength X (Y ⊗ Z) =
    ((associator (T.obj X) Y Z).inv) ≫
      ((rightStrength X Y) ⊗ₘ (𝟙 Z))
      ≫ rightStrength (X ⊗ Y) Z
      ≫ T.map (associator X Y Z).hom
  rightStrengthAssoc :
    ∀ X Y Z : C,
      rightStrength X (Y ⊗ Z) ≫ T.map (associator X Y Z).inv =
        (associator (T.obj X) Y Z).inv ≫ (rightStrength X Y ⊗ₘ 𝟙 Z) ≫ rightStrength (X ⊗ Y) Z
  rightStrengthNaturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    rightStrength X Y ≫ T.map (f ⊗ₘ g) =
      (T.map f ⊗ₘ g) ≫ rightStrength X' Y'
