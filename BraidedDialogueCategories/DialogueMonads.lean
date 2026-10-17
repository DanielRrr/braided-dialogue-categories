module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import BraidedDialogueCategories.DialogueCategories
public import BraidedDialogueCategories.MonadicStrength

@[expose] public section

universe v

namespace CategoryTheory
open DialogueCategory
open MonoidalCategory

namespace DialogueCategory

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C] [D : DialogueCategory.{v} C]

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

/-- The equivalence between `L A ⟶ B ≃ A ⟶ R B`. -/
def dialogueHomEquiv (A : C) (B : Cᵒᵖ) : (L.obj A ⟶ B) ≃ (A ⟶ R.obj B) :=
  (CategoryTheory.opEquiv (L.obj A) B).trans <|
    (HasLeftIhom.homEquiv B.unop).symm.trans <| HasRightIhom.homEquiv A

/-- The adjunction between between the left and the right dual functors. -/
def dialogueAdjunction : L (C := C) ⊣ R (C := C) :=
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
def dialogueAdjunctionOp : Rop (C := C) ⊣ Lop (C := C) :=
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

/-- The unit of `T'`, with its type written out. -/
def etaT' (B : C) : B ⟶ leftDual (rightDual B) :=
  HasLeftIhom.homEquiv (A := rightDual B) (B := D.bot) B (reval B)

lemma monadT'_eta_app (B : C) : monadT'.η.app B = etaT' B := rfl

lemma T'_eta_eq (X : C) :
  monadT'.η.app X = HasLeftIhom.homEquiv (A := rightDual X) (B := D.bot) X (reval X) := rfl

lemma etaUncurry (B : C) :
    (𝟙 (rightDual B) ⊗ₘ monadT'.η.app B) ≫ leval (rightDual B) = reval B := by
  rw [T'_eta_eq]
  exact HasLeftIhom.uncurry_curry _

/-- The whiskered version of `etaUncurry`. -/
@[reassoc]
lemma etaT'_leval (B : C) : rightDual B ◁ etaT' B ≫ leval (rightDual B) = reval B := by
  rw [← id_tensorHom]
  exact etaUncurry B

/-- Whiskering the unit and `leftDualMap (rev A B)` together, then evaluating. -/
lemma strengthKeyH3 (A B : C) :
    (𝟙 (rightDual (A ⊗ B) ⊗ A) ⊗ₘ (monadT'.η.app B ≫ leftDualMap (rev A B))) ≫
        leval (rightDual (A ⊗ B) ⊗ A) =
      (α_ (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B) := by
  calc _ = (𝟙 (rightDual (A ⊗ B) ⊗ A) ⊗ₘ monadT'.η.app B) ≫
          (𝟙 (rightDual (A ⊗ B) ⊗ A) ⊗ₘ leftDualMap (rev A B)) ≫
            leval (rightDual (A ⊗ B) ⊗ A) := by
        rw [← Category.assoc]
        exact congrArg (· ≫ leval (rightDual (A ⊗ B) ⊗ A))
          (MonoidalCategory.id_tensor_comp _ _)
    _ = (𝟙 (rightDual (A ⊗ B) ⊗ A) ⊗ₘ monadT'.η.app B) ≫
            (rev A B ⊗ₘ 𝟙 (leftDual (rightDual B))) ≫ leval (rightDual B) := by
          congr 1; exact HasLeftIhom.contramapEval (B := D.bot) (rev A B)
    _ = (rev A B ⊗ₘ 𝟙 B) ≫ (𝟙 (rightDual B) ⊗ₘ monadT'.η.app B) ≫
            leval (rightDual B) :=
        (id_tensor_comp_tensor_id_assoc (monadT'.η.app B) (rev A B) _).trans
            (tensor_id_comp_id_tensor_assoc (monadT'.η.app B) (rev A B) _).symm
    _ = (rev A B ⊗ₘ 𝟙 B) ≫ reval B := by
          congr 1; exact etaUncurry B
    _ = _ := revUncurry A B

/-- Merge the two whiskers into one. -/
lemma strengthKeyH1 (A B : C) :
    (𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ monadT'.η.app B)) ≫
        (𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ leftDualMap (rev A B))) =
      𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ (monadT'.η.app B ≫ leftDualMap (rev A B))) := by
  refine (id_tensor_comp _ _).symm.trans ?_
  exact congrArg (𝟙 (rightDual (A ⊗ B)) ⊗ₘ ·) (id_tensor_comp _ _).symm

/-- Move the whisker through the associator. -/
lemma strengthKeyH2 (A B : C) :
    (𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ (monadT'.η.app B ≫ leftDualMap (rev A B)))) ≫
        (α_ (rightDual (A ⊗ B)) A (leftDual (rightDual (A ⊗ B) ⊗ A))).inv =
      (α_ (rightDual (A ⊗ B)) A B).inv ≫
        (𝟙 (rightDual (A ⊗ B) ⊗ A) ⊗ₘ (monadT'.η.app B ≫ leftDualMap (rev A B))) := by simp

/-- The assembled key identity. -/
lemma strengthKey (A B : C) :
    (𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ monadT'.η.app B)) ≫
        (𝟙 (rightDual (A ⊗ B)) ⊗ₘ (𝟙 A ⊗ₘ leftDualMap (rev A B))) ≫
          (α_ (rightDual (A ⊗ B)) A (leftDual (rightDual (A ⊗ B) ⊗ A))).inv ≫
            leval (rightDual (A ⊗ B) ⊗ A) =
      reval (A ⊗ B) := by
  rw [← Category.assoc, strengthKeyH1, ← Category.assoc, strengthKeyH2,
    Category.assoc, strengthKeyH3, Iso.inv_hom_id_assoc]

lemma T'_map_eq {A B : C} (f : A ⟶ B) : T'.map f = leftDualMap (rightDualMap f) := rfl


/-- The monad `T' : C ⥤ C` satisfies the left tensorial strength condition. -/
instance : LeftStrength monadT' (C := C) where
  leftStrength A B := (𝟙 A ⊗ₘ leftDualMap (rev A B)) ≫ lev A (rightDual (A ⊗ B))
  leftStrengthEq₁ A B := by
    apply (HasLeftIhom.homEquiv (A := rightDual (A ⊗ B)) (B := D.bot) (A ⊗ B)).symm.injective
    erw [T'_eta_eq, Equiv.symm_apply_apply, HasLeftIhom.symm_comp, HasLeftIhom.symm_comp,
    Equiv.symm_apply_apply]
    exact (strengthKey A B).symm
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
