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

/-- The right evaluation arrow `[A, bot]ᵣ ⊗ A ⟶ bot`-/
def reval (A : C) : rightDual A ⊗ A ⟶ bot :=
  HasRightIhom.evalRight (A := A) (B := DialogueCategory.bot)

/-- The useful tautological equality for `reval` explicitly identifying `reval`
with `HasRightIhom.evalRight` with `B` instantiated with `D.bot`. -/
lemma reval_eq_eval (A : C) :
  reval A = HasRightIhom.evalRight (A := A) (B := D.bot) := rfl

def lev (B A : C) : B ⊗ leftDual (A ⊗ B) ⟶ leftDual A :=
  HasLeftIhom.homEquiv (B ⊗ leftDual (A ⊗ B))
      ((associator A B (leftDual (A ⊗ B))).inv ≫
        leval (A ⊗ B))

/-- The useful combinator obtained from the right evaluation. -/
def rev (A B : C) : (rightDual (A ⊗ B)) ⊗ A ⟶ rightDual B :=
  HasRightIhom.homEquiv (rightDual (A ⊗ B) ⊗ A)
    ((associator (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B))

/-- The currification of the left negation. -/
def leftName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ leftDual A :=
  HasLeftIhom.homEquiv (𝟙_ C) ((rightUnitor A).hom ≫ f)

/-- The exponentiation property for `leftName`. -/
lemma leftNameUncurry (A : C) (f : A ⟶ bot) :
    ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A = (rightUnitor A).hom ≫ f := by
  let e₀ := HasLeftIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  let e₁ := HasLeftIhom.homEquiv (A := A) (B := D.bot) (leftDual A)
  apply e₀.injective
  let e₂ := HasLeftIhom.homEquivNaturalityₗ (A := A) (B := D.bot) (f := leftName A f) (g := leval A)
  rw [e₂]
  change leftName A f ≫ e₁ (e₁.symm (𝟙 (leftDual A))) = e₀ ((rightUnitor A).hom ≫ f)
  rw [e₁.apply_symm_apply]
  simp [leftName, e₀]

lemma leftNameFact (A : C) (f : A ⟶ bot) : f = (rightUnitor A).inv ≫ ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A := by
  rw [leftNameUncurry]; simp

/-- The currification of right negation. -/
def rightName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ rightDual A :=
  HasRightIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C) ((leftUnitor A).hom ≫ f)

/-- The exponentiation property for `rightName`. -/
lemma rightNameUncurry (A : C) (f : A ⟶ bot) :
  (rightName A f ⊗ₘ (𝟙 A)) ≫ reval A = (leftUnitor A).hom ≫ f := by
  let e₀ := HasRightIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  let e₁ := HasRightIhom.homEquiv (A := A) (B := D.bot) (rightDual A)
  apply e₀.injective
  let e₂ := HasRightIhom.homEquivNaturalityᵣ (A := A) (B := D.bot) (f := rightName A f) (g := reval A)
  rw [e₂]
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

/-- TODO -/
instance : RightStrength monadT (C := C) where
  rightStrength A B := sorry
  rightStrengthEq₁ := sorry
  rightStrengthEq₂ := sorry
  rightStrengthNaturality := sorry

/-- TODO -/
instance : LeftStrength monadT' (C := C) where
  leftStrength := sorry
  leftStrengthEq₁ := sorry
  leftStrengthEq₂ := sorry
  leftStrengthNaturality := sorry

end DialogueCategory

open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ T.obj A
  etaStar₂ : ∀ A : C, A ≅ T'.obj A
