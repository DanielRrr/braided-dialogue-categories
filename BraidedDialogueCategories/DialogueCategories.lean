module

public import Mathlib.CategoryTheory.Monoidal.Category
public import BraidedDialogueCategories.InternalHoms

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory
open HasLeftIhom
open HasRightIhom

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C]


/--
A distinguished object `bot` for which both families `[A, bot]ₗ` and `[A, bot]ᵣ` exist for every `A`.
-/
class DialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C] where
  bot : C
  [leftClosed : LeftClosedAt bot]
  [rightClosed : RightClosedAt bot]

instance [D : DialogueCategory C] : LeftClosedAt D.bot where
  hasLeftIhom := D.leftClosed.hasLeftIhom

instance [D : DialogueCategory C] : RightClosedAt D.bot where
  hasRightIhom := D.rightClosed.hasRightIhom

namespace DialogueCategory

variable [D : DialogueCategory C]

/-- `[A, bot]ₗ`. -/
abbrev leftDual (A : C) : C := HasLeftIhom.internalHomₗ A D.bot

/-- `[A, bot]ᵣ`. -/
abbrev rightDual (A : C) : C := HasRightIhom.internalHomᵣ A D.bot

/-- The left evaluation arrow `A ⊗ [A, bot]ₗ ⟶ bot`-/
abbrev leval (A : C) : A ⊗ leftDual A ⟶ bot :=
  HasLeftIhom.leftEval (A := A) (B := DialogueCategory.bot)

lemma leval_eq_eval (A : C) :
  leval A = HasLeftIhom.leftEval (A := A) (B := D.bot) := rfl

def leftDualMap {A B : C} (f : A ⟶ B) : leftDual B ⟶ leftDual A :=
  HasLeftIhom.contramap (B := D.bot) f

def rightDualMap {A B : C} (f : A ⟶ B) : rightDual B ⟶ rightDual A :=
  HasRightIhom.contramap (B := D.bot) f

/-- The right evaluation arrow `[A, bot]ᵣ ⊗ A ⟶ bot`-/
def reval (A : C) : rightDual A ⊗ A ⟶ bot :=
  HasRightIhom.evalRight (A := A) (B := DialogueCategory.bot)

/-- The useful tautological equality for `reval` explicitly identifying `reval`
with `HasRightIhom.evalRight` with `B` instantiated with `D.bot`. -/
lemma reval_eq_eval (A : C) :
  reval A = HasRightIhom.evalRight (A := A) (B := D.bot) := rfl

def lev (B A : C) : B ⊗ leftDual (A ⊗ B) ⟶ leftDual A :=
  HasLeftIhom.homEquiv (B ⊗ leftDual (A ⊗ B))
      ((α_ A B (leftDual (A ⊗ B))).inv ≫ leval (A ⊗ B))

lemma contramapEval' {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    (𝟙 A₁ ⊗ₘ leftDualMap f) ≫ HasLeftIhom.leftEval = (f ⊗ₘ 𝟙 (leftDual A₂)) ≫ HasLeftIhom.leftEval := by
  rw [leftDualMap]
  exact HasLeftIhom.uncurry_curry _

lemma levUncurry (B A : C) :
    (𝟙 A ⊗ₘ lev B A) ≫ leval A =
      (associator A B (leftDual (A ⊗ B))).inv ≫ leval (A ⊗ B) := by
  rw [lev]
  exact HasLeftIhom.uncurry_curry _

/-- The useful combinator obtained from the right evaluation. -/
def rev (A B : C) : (rightDual (A ⊗ B)) ⊗ A ⟶ rightDual B :=
  HasRightIhom.homEquiv (rightDual (A ⊗ B) ⊗ A)
    ((α_ (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B))

lemma revUncurry (A B : C) :
    (rev A B ⊗ₘ 𝟙 B) ≫ reval B = (α_ (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B) := by
  rw [rev]
  exact HasRightIhom.uncurry_curry _

/-- The whiskered version of `contramapEval'`. -/
@[reassoc]
lemma leftDualMap_leval {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    A₁ ◁ leftDualMap f ≫ leval A₁ = f ▷ leftDual A₂ ≫ leval A₂ := by
  rw [← id_tensorHom, ← tensorHom_id]
  exact contramapEval' f

/-- The right-handed counterpart of `leftDualMap_leval`. -/
@[reassoc]
lemma rightDualMap_reval {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    rightDualMap f ▷ A₁ ≫ reval A₁ = rightDual A₂ ◁ f ≫ reval A₂ := by
  rw [← id_tensorHom, ← tensorHom_id]
  exact HasRightIhom.uncurry_curry _

/-- The whiskered version of `levUncurry`. -/
@[reassoc]
lemma lev_leval (B A : C) :
    A ◁ lev B A ≫ leval A = (α_ A B (leftDual (A ⊗ B))).inv ≫ leval (A ⊗ B) := by
  rw [← id_tensorHom]
  exact levUncurry B A

/-- The whiskered version of `revUncurry`. -/
@[reassoc]
lemma rev_reval (A B : C) :
    rev A B ▷ B ≫ reval B = (α_ (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B) := by
  rw [← tensorHom_id]
  exact revUncurry A B

/-- The currification of the left negation. -/
def leftName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ leftDual A :=
  HasLeftIhom.homEquiv (𝟙_ C) ((rightUnitor A).hom ≫ f)

/-- The exponentiation property for `leftName`. -/
lemma leftNameUncurry (A : C) (f : A ⟶ bot) :
    ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A = (rightUnitor A).hom ≫ f := by
  -- We have a (A ⊗ 𝟙_ C ⟶ bot) ≃ (𝟙_ C ⟶ internalHomₗ A bot)
  let e₀ := HasLeftIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  -- We also have a bijection (A ⊗ leftDual A ⟶ bot) ≃ (leftDual A ⟶ internalHomₗ A bot)
  let e₁ := HasLeftIhom.homEquiv (A := A) (B := D.bot) (leftDual A)
  -- e₀ is injective, so we must show `e₀ ((𝟙 A ⊗ₘ leftName A f) ≫ leval A) = e₀ ((ρ_ A).hom ≫ f)`
  apply e₀.injective
  -- we have the equality
  -- `(HasLeftIhom.homEquiv (𝟙_ C)) ((𝟙 A ⊗ₘ leftName A f) ≫ leval A) = leftName A f ≫ (HasLeftIhom.homEquiv (leftDual A)) (leval A)`
  let e₂ := HasLeftIhom.homEquivNaturalityₗ (A := A) (B := D.bot) (f := leftName A f) (g := leval A)
  rw [e₂]
  -- After applying e₂, we must show leftName A f ≫ (HasLeftIhom.homEquiv (leftDual A)) (leval A) = e₀ ((ρ_ A).hom ≫ f),
  -- but the left-hand side of the equality is equal to
  change leftName A f ≫ e₁ (e₁.symm (𝟙 (leftDual A))) = e₀ ((rightUnitor A).hom ≫ f)
  -- we must show `leftName A f ≫ e₁ (e₁.symm (𝟙 (leftDual A))) = e₀ ((ρ_ A).hom ≫ f)`,
  rw [e₁.apply_symm_apply]
  -- we must show `leftName A f ≫ 𝟙 (leftDual A) = e₀ ((ρ_ A).hom ≫ f)`
  simp [leftName, e₀]

lemma leftNameFact (A : C) (f : A ⟶ bot) : f = (rightUnitor A).inv ≫ ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A := by
  rw [leftNameUncurry]; simp

/-- The currification of right negation. -/
def rightName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ rightDual A :=
  HasRightIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C) ((leftUnitor A).hom ≫ f)

/-- The exponentiation property for `rightName` for a morphism `f : A ⟶ bot` for any `A`. -/
lemma rightNameUncurry (A : C) (f : A ⟶ bot) :
  (rightName A f ⊗ₘ (𝟙 A)) ≫ reval A = (leftUnitor A).hom ≫ f := by
  -- we have the bijection `(𝟙_ C ⊗ A ⟶ bot) ≃ (𝟙_ C ⟶ internalHomᵣ A bot)`
  let e₀ := HasRightIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  -- we have the bijection `(rightDual A ⊗ A ⟶ bot) ≃ (rightDual A ⟶ internalHomᵣ A bot)`
  let e₁ := HasRightIhom.homEquiv (A := A) (B := D.bot) (rightDual A)
  apply e₀.injective
  -- we must show that `e₀ ((rightName A f ⊗ₘ 𝟙 A) ≫ reval A) = e₀ ((λ_ A).hom ≫ f)`.

  -- We have `(HasRightIhom.homEquiv (𝟙_ C)) ((rightName A f ⊗ₘ 𝟙 A) ≫ reval A) = rightName A f ≫ (HasRightIhom.homEquiv (rightDual A)) (reval A)`
  let e₂ := HasRightIhom.homEquivNaturalityᵣ (A := A) (B := D.bot) (f := rightName A f) (g := reval A)
  rw [e₂]
  -- The current goal is `rightName A f ≫ (HasRightIhom.homEquiv (rightDual A)) (reval A) = e₀ ((λ_ A).hom ≫ f)`.
  change rightName A f ≫ e₁ (e₁.symm (𝟙 (rightDual A))) = e₀ ((leftUnitor A).hom ≫ f)
  rw [e₁.apply_symm_apply]
  simp [rightName, e₀]

lemma rightNameFact (A : C) (f : A ⟶ bot) : f = (leftUnitor A).inv ≫ (rightName A f ⊗ₘ (𝟙 A)) ≫ reval A := by
  rw [rightNameUncurry]; simp

/-- Two morphisms into `leftDual Y` are equal whenever their uncurried forms are. -/
lemma leftDual_hom_ext {X Y : C} {f g : X ⟶ leftDual Y}
    (h : Y ◁ f ≫ leval Y = Y ◁ g ≫ leval Y) : f = g := by
  apply left_hom_ext; exact h

/-- Two morphisms into `rightDual Y` are equal whenever their uncurried forms are. -/
lemma rightDual_hom_ext {X Y : C} {f g : X ⟶ rightDual Y}
    (h : f ▷ Y ≫ reval Y = g ▷ Y ≫ reval Y) : f = g := by
  apply right_hom_ext; exact h

/-- The compatibility of `lev` with the associator. -/
lemma lev_assoc (X Y Z : C) :
    (Y ⊗ Z) ◁ leftDualMap (α_ X Y Z).inv ≫ lev (Y ⊗ Z) X =
      (α_ Y Z (leftDual ((X ⊗ Y) ⊗ Z))).hom ≫ Y ◁ lev Z (X ⊗ Y) ≫ lev Y X := by
  apply leftDual_hom_ext
  rw [MonoidalCategory.whiskerLeft_comp_assoc, lev_leval, associator_inv_naturality_right_assoc,
    leftDualMap_leval]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc, lev_leval,
    associator_inv_naturality_right_assoc, lev_leval, pentagon_hom_inv_inv_inv_inv_assoc]

/-- The compatibility of `rev` with the associator. -/
lemma rev_assoc (X Y Z : C) :
    rightDualMap (α_ X Y Z).hom ▷ (X ⊗ Y) ≫ rev (X ⊗ Y) Z =
      (α_ (rightDual (X ⊗ (Y ⊗ Z))) X Y).inv ≫ rev X (Y ⊗ Z) ▷ Y ≫ rev Y Z := by
  apply rightDual_hom_ext
  rw [comp_whiskerRight_assoc, rev_reval, associator_naturality_left_assoc, rightDualMap_reval,
    comp_whiskerRight_assoc, comp_whiskerRight_assoc, rev_reval, associator_naturality_left_assoc,
    rev_reval]
  rw [← pentagon_assoc, inv_hom_whiskerRight_assoc]

/-- `lev` is natural in both of its arguments. -/
lemma lev_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    Y ◁ leftDualMap (f ⊗ₘ g) ≫ lev Y X = g ▷ leftDual (X' ⊗ Y') ≫ lev Y' X' ≫ leftDualMap f := by
  apply leftDual_hom_ext
  rw [MonoidalCategory.whiskerLeft_comp_assoc, lev_leval, associator_inv_naturality_right_assoc,
    leftDualMap_leval]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    leftDualMap_leval, whisker_exchange_assoc, lev_leval]
  rw [associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc, tensorHom_def',
    comp_whiskerRight_assoc]

/-- `rev` is natural in both of its arguments. -/
lemma rev_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    rightDualMap (f ⊗ₘ g) ▷ X ≫ rev X Y =
      rightDual (X' ⊗ Y') ◁ f ≫ rev X' Y' ≫ rightDualMap g := by
  apply rightDual_hom_ext
  rw [comp_whiskerRight_assoc, rev_reval, associator_naturality_left_assoc, rightDualMap_reval]
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, rightDualMap_reval, ← whisker_exchange_assoc,
    rev_reval]
  rw [associator_naturality_right_assoc, associator_naturality_middle_assoc,
    tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc]

lemma adjNatLeft {A₁ A₂ : C} (B : C) (f : A₂ ⟶ A₁) (g : A₁ ⟶ rightDual B) :
  HasLeftIhom.homEquiv B ((HasRightIhom.homEquiv A₂).symm (f ≫ g)) =
  HasLeftIhom.homEquiv B ((HasRightIhom.homEquiv A₁).symm g) ≫ HasLeftIhom.contramap f := by
  rw [HasRightIhom.symm_comp, HasLeftIhom.homEquiv_naturality_left]

lemma adjNatRight {A B₁ B₂ : C} (f : B₁ ⟶ leftDual A) (g : B₂ ⟶ B₁) :
    HasRightIhom.homEquiv A ((HasLeftIhom.homEquiv B₂).symm (g ≫ f)) =
    HasRightIhom.homEquiv A ((HasLeftIhom.homEquiv B₁).symm f) ≫ HasRightIhom.contramap g := by
  rw [HasLeftIhom.symm_comp, HasRightIhom.homEquiv_naturality_left]

lemma leftEquiv_rightEquiv_symm_comp {A₁ A₂ B : C}
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ rightDual B) :
    HasLeftIhom.homEquiv (A := A₁) B ((HasRightIhom.homEquiv (A := B) A₁).symm (f ≫ g)) =
      HasLeftIhom.homEquiv (A := A₂) B
        ((HasRightIhom.homEquiv (A := B) A₂).symm g) ≫
        HasLeftIhom.contramap f := by
  rw [HasRightIhom.symm_comp, HasLeftIhom.homEquiv_naturality_left]

lemma rightEquiv_leftEquiv_symm_comp {A₁ A₂ B : C}
    (f : A₂ ⟶ leftDual B) (g : A₁ ⟶ A₂) :
    HasRightIhom.homEquiv (A := A₁) B
        ((HasLeftIhom.homEquiv (A := B) A₁).symm (g ≫ f)) =
      HasRightIhom.homEquiv (A := A₂) B
        ((HasLeftIhom.homEquiv (A := B) A₂).symm f) ≫
        HasRightIhom.contramap g := by
  rw [HasLeftIhom.symm_comp, HasRightIhom.homEquiv_naturality_left]

end DialogueCategory
/-
open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ T.obj A
  etaStar₂ : ∀ A : C, A ≅ T'.obj A
-/
