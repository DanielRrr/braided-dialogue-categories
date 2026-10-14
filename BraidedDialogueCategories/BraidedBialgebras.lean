module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Comon_

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory ComonObj MonObj BraidedCategory

variable (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

class Bialgebra (A : C) where
  [bialgebraMonoid : MonObj A]
  [bialgebraCoMonoid : ComonObj A]
  mul_co_mul :
    μ[A] ≫ Δ[A] = (Δ[A] ⊗ₘ Δ[A]) ≫ ((β_ A A).hom ⊗ₘ (β_ A A).hom) ≫ (μ[A] ⊗ₘ μ[A])
  unit_co_unit : η[A] ≫ ε[A] = 𝟙 (𝟙_ C)
  mul_counit : μ[A] ≫ ε[A] = (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ C)).hom
  unit_comult : η[A] ≫ Δ[A] = (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A])

instance (A : C) [B : Bialgebra C A] : MonObj A where
  one := B.bialgebraMonoid.one
  mul := B.bialgebraMonoid.mul

instance (A : C) [B : Bialgebra C A] : ComonObj A where
  counit := B.bialgebraCoMonoid.counit
  comul := B.bialgebraCoMonoid.comul
