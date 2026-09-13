module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory

/--
The twist `theta A` is depicted as the ribbon `A`-twisted positively in the trigonometric direction
with an angle `2π`, whereas its inverse `theta⁻¹ A` is depicted as the same ribbon `A` twisted this
time negatively with an angle `-2π`.
-/
class BalancedMonoidal (C : Type v)
  [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C] where
  theta : ∀ A : C, A ⟶ A
  thetaId : theta (𝟙_ C) = 𝟙 (𝟙_ C)
  thetaProd : ∀ A B : C, theta (A ⊗ B) = (β_ A B).hom ≫ (theta B ⊗ₘ theta A) ≫ (β_ B A).hom

variable (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C]

structure DualPair (A B : C) where
  eta : 𝟙_ C ⟶ A ⊗ B
  epsilon : B ⊗ A ⟶ 𝟙_ C
  eq₁ : 𝟙 A = (leftUnitor A).inv ≫ (eta ⊗ₘ 𝟙 A) ≫ (associator A B A).hom ≫ (𝟙 A ⊗ₘ epsilon) ≫ (rightUnitor A).hom
  eq₂ : 𝟙 B = (rightUnitor B).inv ≫ (𝟙 B ⊗ₘ eta) ≫ (associator B A B).inv ≫ (epsilon ⊗ₘ 𝟙 B) ≫ (leftUnitor B).hom

variable [BraidedCategory.{v} C]

class RibbonCategory [b : BalancedMonoidal.{v} C] where
  star : C → C
  dualPair : ∀ A : C, DualPair C A (star A)
  ribbonCoh : ∀ A : C, (b.theta (star A) ⊗ₘ 𝟙 A) ≫ (dualPair A).epsilon = (𝟙 (star A) ⊗ₘ (b.theta A)) ≫ (dualPair A).epsilon
