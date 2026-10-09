module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Category
public import BraidedDialogueCategories.InternalHoms
public import BraidedDialogueCategories.MonadicStrength

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

/-- `leftDual` as a contravariant functor. It's called `L` in Melliés's manuscript.  -/
def L : C ⥤ Cᵒᵖ where
  obj A := Opposite.op (leftDual A)
  map f := (HasLeftIhom.contramap f).op
  map_id := by simp
  map_comp := by simp

/-- `leftDual` as a contravariant functor. It's called `L^op` in Melliés's manuscript. -/
def Lop : Cᵒᵖ ⥤ C where
  obj A := leftDual A.unop
  map f := HasLeftIhom.contramap f.unop
  map_id := by simp
  map_comp := by simp

/-- `rightDual` as a contravariant functor. It's called `R` in Melliés's manuscript. -/
def R : Cᵒᵖ ⥤ C where
  obj A := rightDual A.unop
  map f := HasRightIhom.contramap f.unop
  map_id := by simp
  map_comp := by simp

/-- `rightDual` as a contravariant functor. It's called `R^op` in Melliés's manuscript. -/
def Rop : C ⥤ Cᵒᵖ where
  obj A := Opposite.op (rightDual A)
  map f := (HasRightIhom.contramap f).op
  map_id := by simp
  map_comp := by simp

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

/-- The equivalence between `L A ⟶ B ≃ A ⟶ R B`. -/
def dialogueHomEquiv (A : C) (B : Cᵒᵖ) : (L.obj A ⟶ B) ≃ (A ⟶ R.obj B) :=
  (CategoryTheory.opEquiv (L.obj A) B).trans <|
    (HasLeftIhom.homEquiv B.unop).symm.trans <| HasRightIhom.homEquiv A

/-- The adjunction between between the left and the right dual functors. -/
def dialogueAdjunction : L (C := C) ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := dialogueHomEquiv
      homEquiv_naturality_left_symm := by
        intros A₁ A₂ B f g
        exact congrArg Quiver.Hom.op <| adjNatLeft B.unop f g
      homEquiv_naturality_right := by
        intros A B₁ B₂ f g; apply adjNatRight
    }

/-- The equivalence between `R^op A ⟶ B ≃ A ⟶ L^op B`. -/
def dialogueHomEquivOp (A : C) (B : Cᵒᵖ) : (Rop.obj A ⟶ B) ≃ (A ⟶ Lop.obj B) :=
  (CategoryTheory.opEquiv (Rop.obj A) B).trans <|
    (HasRightIhom.homEquiv B.unop).symm.trans <| HasLeftIhom.homEquiv A

/-- The adjunction dual to `L ⊣ R`. -/
def dialogueAdjunctionOp : Rop (C := C) ⊣ Lop :=
  Adjunction.mkOfHomEquiv
    { homEquiv := dialogueHomEquivOp
      homEquiv_naturality_left_symm := by
        intros A₂ A₁ B f g; exact congrArg Quiver.Hom.op (rightEquiv_leftEquiv_symm_comp g f)
      homEquiv_naturality_right := by
        intros A B₁ B₂ f g; exact leftEquiv_rightEquiv_symm_comp g.unop f.unop
    }

/-- The double negation monad `T : A ↦ rightDual (leftDual A)`. -/
def monadT : Monad C := Adjunction.toMonad dialogueAdjunction

/-- The underlying functor of `monadT`. -/
def T : C ⥤ C := monadT.toFunctor

/-- The double negation monad `T : A ↦ leftDual (rightDual A)`. -/
def monadT' : Monad C := Adjunction.toMonad dialogueAdjunctionOp

/-- The underlying functor of `monadT'`. -/
def T' : C ⥤ C := monadT'.toFunctor

lemma T'_map_eq {A B : C} (f : A ⟶ B) : T'.map f = leftDualMap (rightDualMap f) := rfl

lemma T'_eta_eq (X : C) :
  monadT'.η.app X = HasLeftIhom.homEquiv (A := rightDual X) (B := D.bot) X (reval X) := rfl

lemma etaUncurry (B : C) :
    (𝟙 (rightDual B) ⊗ₘ monadT'.η.app B) ≫ leval (rightDual B) = reval B := by
  rw [T'_eta_eq]
  exact HasLeftIhom.uncurry_curry _

/-- The monad `T' : C ⥤ C` satisfies the left tensorial strength condition. -/
instance : LeftStrength monadT' (C := C) where
  leftStrength A B := (𝟙 A ⊗ₘ leftDualMap (rev A B)) ≫ lev A (rightDual (A ⊗ B))
  leftStrengthEq₁ A B := by
    apply (HasLeftIhom.homEquiv (A := rightDual (A ⊗ B)) (B := D.bot) (A ⊗ B)).symm.injective
    erw [T'_eta_eq, Equiv.symm_apply_apply, HasLeftIhom.symm_comp, HasLeftIhom.symm_comp, Equiv.symm_apply_apply]
-- goal now: reval (A⊗B) = (𝟙 _ ⊗ₘ (𝟙 A ⊗ₘ monadT'.η.app B)) ≫ (𝟙 _ ⊗ₘ (𝟙 A ⊗ₘ leftDualMap (rev A B))) ≫
--             (α_ ...).inv ≫ leval (rightDual (A⊗B) ⊗ A)
    have key :
      (𝟙 (rightDual (A⊗B)) ⊗ₘ (𝟙 A ⊗ₘ monadT'.η.app B)) ≫
        (𝟙 (rightDual (A⊗B)) ⊗ₘ (𝟙 A ⊗ₘ leftDualMap (rev A B))) ≫
          (α_ (rightDual (A⊗B)) A (leftDual (rightDual (A⊗B) ⊗ A))).inv ≫ leval (rightDual (A⊗B) ⊗ A) =
      reval (A ⊗ B) := by
      conv_lhs => rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      sorry
    exact key.symm
  leftStrengthEq₂ := sorry
  leftStrengthAssoc := sorry
  leftStrengthNaturality := sorry

/-- The monad `T : C ⥤ C` satisfies the right tensorial strength condition. -/
instance : RightStrength monadT (C := C) where
  rightStrength A B := (rightDualMap (lev B A) ⊗ₘ 𝟙 B) ≫ rev B (leftDual (A ⊗ B))
  rightStrengthEq₁ := sorry
  rightStrengthEq₂ := sorry
  rightStrengthAssoc := sorry
  rightStrengthNaturality := sorry

end DialogueCategory

open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ T.obj A
  etaStar₂ : ∀ A : C, A ≅ T'.obj A
