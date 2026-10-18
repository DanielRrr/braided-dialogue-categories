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

/-- The unit of `T`, with its type written out. -/
def etaT (A : C) : A ⟶ rightDual (leftDual A) :=
  HasRightIhom.homEquiv (A := leftDual A) (B := D.bot) A (leval A)

/-- The tautological reformulation of `monadT'.η.app` with `etaT'`. -/
lemma monadT'_eta_app (B : C) : monadT'.η.app B = etaT' B := rfl

/-- The tautological reformulation of `monadT.η.app` with `etaT`. -/
lemma monadT_eta_app (A : C) : monadT.η.app A = etaT A := rfl

/-- The unit of the monad `T'`. -/
lemma T'_eta_eq (X : C) :
  monadT'.η.app X = HasLeftIhom.homEquiv (A := rightDual X) (B := D.bot) X (reval X) := rfl

/-- `reval B` is the composite of `𝟙 (rightDual B) ⊗ₘ monadT'.η.app B` and `leval (rightDual B)`. -/
lemma etaUncurry (B : C) :
    (𝟙 (rightDual B) ⊗ₘ monadT'.η.app B) ≫ leval (rightDual B) = reval B := by
  rw [T'_eta_eq]
  exact HasLeftIhom.uncurry_curry _

/-- The whiskered version of `etaUncurry`. -/
@[reassoc]
lemma etaT'_leval (B : C) : rightDual B ◁ etaT' B ≫ leval (rightDual B) = reval B := by
  rw [← id_tensorHom]
  exact etaUncurry B

/-- The uncurried form of the unit of `T`. -/
@[reassoc]
lemma etaT_reval (A : C) : etaT A ▷ leftDual A ≫ reval (leftDual A) = leval A := by
  rw [etaT, ← tensorHom_id]
  exact HasRightIhom.uncurry_curry _

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

/-- `T'.map` is the composite of `leftDualMap` and `rightDualMap`. -/
lemma T'_map_eq {A B : C} (f : A ⟶ B) : T'.map f = leftDualMap (rightDualMap f) := rfl

/-- The left strength `A ⊗ T' B ⟶ T' (A ⊗ B)` of the monad `T'`. -/
def leftStrengthT' (A B : C) : A ⊗ leftDual (rightDual B) ⟶ leftDual (rightDual (A ⊗ B)) :=
  (𝟙 A ⊗ₘ leftDualMap (rev A B)) ≫ lev A (rightDual (A ⊗ B))

/-- The right strength `T A ⊗ B ⟶ T (A ⊗ B)` of the monad `T`. -/
def rightStrengthT (A B : C) : rightDual (leftDual A) ⊗ B ⟶ rightDual (leftDual (A ⊗ B)) :=
  (rightDualMap (lev B A) ⊗ₘ 𝟙 B) ≫ rev B (leftDual (A ⊗ B))

/-- The uncurried form of the left strength of `T'`. -/
@[reassoc]
lemma leftStrengthT'_leval (A B : C) :
    rightDual (A ⊗ B) ◁ leftStrengthT' A B ≫ leval (rightDual (A ⊗ B)) =
      (α_ (rightDual (A ⊗ B)) A (leftDual (rightDual B))).inv ≫
        rev A B ▷ leftDual (rightDual B) ≫ leval (rightDual B) := by
  rw [leftStrengthT', id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc, lev_leval,
    associator_inv_naturality_right_assoc, leftDualMap_leval]

/-- The uncurried form of the right strength of `T`. -/
@[reassoc]
lemma rightStrengthT_reval (A B : C) :
    rightStrengthT A B ▷ leftDual (A ⊗ B) ≫ reval (leftDual (A ⊗ B)) =
      (α_ (rightDual (leftDual A)) B (leftDual (A ⊗ B))).hom ≫
        rightDual (leftDual A) ◁ lev B A ≫ reval (leftDual A) := by
  rw [rightStrengthT, tensorHom_id, comp_whiskerRight_assoc, rev_reval,
    associator_naturality_left_assoc, rightDualMap_reval]

/-- The `etaT` of tensor is `etaT A ⊗ₘ 𝟙 B` postcomposed with `rightStrengthT`. -/
lemma rightStrengthT_eta (A B : C) :
    etaT (A ⊗ B) = (etaT A ⊗ₘ 𝟙 B) ≫ rightStrengthT A B := by
  apply rightDual_hom_ext
  rw [etaT_reval, tensorHom_id, comp_whiskerRight_assoc, rightStrengthT_reval,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, etaT_reval, lev_leval,
    Iso.hom_inv_id_assoc]

/-- The uncurried form of a morphism followed by `T'.map f`. -/
@[reassoc]
lemma comp_T'map_leval {X A B : C} (k : X ⟶ leftDual (rightDual A)) (f : A ⟶ B) :
    rightDual B ◁ (k ≫ leftDualMap (rightDualMap f)) ≫ leval (rightDual B) =
      rightDualMap f ▷ X ≫ rightDual A ◁ k ≫ leval (rightDual A) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, leftDualMap_leval,
    whisker_exchange_assoc]

/-- The uncurried form of a morphism followed by `T.map f`. -/
@[reassoc]
lemma comp_Tmap_reval {X A B : C} (k : X ⟶ rightDual (leftDual A)) (f : A ⟶ B) :
    (k ≫ rightDualMap (leftDualMap f)) ▷ leftDual B ≫ reval (leftDual B) =
      X ◁ leftDualMap f ≫ k ▷ leftDual A ≫ reval (leftDual A) := by
  rw [comp_whiskerRight_assoc, rightDualMap_reval, whisker_exchange_assoc]

/-- The compatibility of `leftStrengthT'` with the associator. -/
lemma leftStrengthT'_assoc (X Y Z : C) :
    leftStrengthT' (X ⊗ Y) Z ≫ leftDualMap (rightDualMap (α_ X Y Z).hom) =
      (α_ X Y (leftDual (rightDual Z))).hom ≫ (𝟙 X ⊗ₘ leftStrengthT' Y Z) ≫
        leftStrengthT' X (Y ⊗ Z) := by
  apply leftDual_hom_ext
  rw [comp_T'map_leval, leftStrengthT'_leval, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, rev_assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc]
  rw [id_tensorHom, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, leftStrengthT'_leval,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftStrengthT'_leval,
    associator_inv_naturality_left_assoc, pentagon_hom_inv_inv_inv_inv_assoc]

/-- The compositionality of `T'map_comp`. -/
lemma T'map_comp {A B E : C} (f : A ⟶ B) (g : B ⟶ E) :
    leftDualMap (rightDualMap (f ≫ g)) =
      leftDualMap (rightDualMap f) ≫ leftDualMap (rightDualMap g) := by
  simp [leftDualMap, rightDualMap]

/-- The compositionality of `Tmap_comp`. -/
lemma Tmap_comp {A B E : C} (f : A ⟶ B) (g : B ⟶ E) :
    rightDualMap (leftDualMap (f ≫ g)) =
      rightDualMap (leftDualMap f) ≫ rightDualMap (leftDualMap g) := by
  simp [leftDualMap, rightDualMap]

/-- `T'map_id` preserves identity. -/
lemma T'map_id (A : C) : leftDualMap (rightDualMap (𝟙 A)) = 𝟙 _ := by
  simp [leftDualMap, rightDualMap]

/-- `Tmap_id` preserves identity. -/
lemma Tmap_id (A : C) : rightDualMap (leftDualMap (𝟙 A)) = 𝟙 _ := by
  simp [leftDualMap, rightDualMap]

/-- The compatibility of `leftStrengthT'` with the inverse associator. -/
lemma leftStrengthT'_assoc_inv (X Y Z : C) :
    (α_ X Y (leftDual (rightDual Z))).inv ≫ leftStrengthT' (X ⊗ Y) Z =
      (𝟙 X ⊗ₘ leftStrengthT' Y Z) ≫ leftStrengthT' X (Y ⊗ Z) ≫
        leftDualMap (rightDualMap (α_ X Y Z).inv) := by
  rw [Iso.inv_comp_eq, ← reassoc_of% (leftStrengthT'_assoc X Y Z), ← T'map_comp,
    Iso.hom_inv_id, T'map_id, Category.comp_id]

/-- `leftStrengthT'` is natural in both arguments. -/
lemma leftStrengthT'_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    leftStrengthT' X Y ≫ leftDualMap (rightDualMap (f ⊗ₘ g)) =
      (f ⊗ₘ leftDualMap (rightDualMap g)) ≫ leftStrengthT' X' Y' := by
  apply leftDual_hom_ext
  -- left side: strength, then `T'(f ⊗ g)`
  rw [comp_T'map_leval, leftStrengthT'_leval, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, rev_naturality, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    ← leftDualMap_leval, ← whisker_exchange_assoc]
  -- right side: `f ⊗ T'(g)`, then strength
  rw [MonoidalCategory.whiskerLeft_comp_assoc, leftStrengthT'_leval, tensorHom_def,
    MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc]

/-- `rightStrengthT` is natural in both arguments. -/
lemma rightStrengthT_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    rightStrengthT X Y ≫ rightDualMap (leftDualMap (f ⊗ₘ g)) =
      (rightDualMap (leftDualMap f) ⊗ₘ g) ≫ rightStrengthT X' Y' := by
  apply rightDual_hom_ext
  -- left side: strength, then `T(f ⊗ g)`
  rw [comp_Tmap_reval, rightStrengthT_reval, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, lev_naturality, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Category.assoc, ← rightDualMap_reval,
    whisker_exchange_assoc]
  -- right side: `T(f) ⊗ g`, then strength
  rw [comp_whiskerRight_assoc, rightStrengthT_reval, tensorHom_def', comp_whiskerRight_assoc,
    associator_naturality_left_assoc, associator_naturality_middle_assoc]

/-- Compatability of `rightStrengthT` with the associator. -/
lemma rightStrengthT_assoc (X Y Z : C) :
    rightStrengthT X (Y ⊗ Z) ≫ rightDualMap (leftDualMap (α_ X Y Z).inv) =
      (α_ (rightDual (leftDual X)) Y Z).inv ≫ (rightStrengthT X Y ⊗ₘ 𝟙 Z) ≫
        rightStrengthT (X ⊗ Y) Z := by
  apply rightDual_hom_ext
  -- left side: one strength, then `T(α⁻¹)`
  rw [comp_Tmap_reval, rightStrengthT_reval, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, lev_assoc, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Category.assoc]
  -- right side: two strengths
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, rightStrengthT_reval, tensorHom_id,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, rightStrengthT_reval,
    associator_naturality_right_assoc]
  -- only associators differ: the pentagon
  rw [← pentagon_assoc, inv_hom_whiskerRight_assoc]

/-- The compatibility of `rightStrengthT` with the associator. -/
lemma rightStrengthT_assoc_hom (X Y Z : C) :
    rightStrengthT X (Y ⊗ Z) =
      (α_ (rightDual (leftDual X)) Y Z).inv ≫ (rightStrengthT X Y ⊗ₘ 𝟙 Z) ≫
        rightStrengthT (X ⊗ Y) Z ≫ rightDualMap (leftDualMap (α_ X Y Z).hom) := by
  rw [← reassoc_of% (rightStrengthT_assoc X Y Z), ← Tmap_comp, Iso.inv_hom_id, Tmap_id,
    Category.comp_id]

/-- The monad `T' : C ⥤ C` satisfies the left tensorial strength condition. -/
instance : LeftStrength monadT' (C := C) where
  leftStrength A B := leftStrengthT' A B
  leftStrengthEq₁ A B := by
    apply (HasLeftIhom.homEquiv (A := rightDual (A ⊗ B)) (B := D.bot) (A ⊗ B)).symm.injective
    erw [T'_eta_eq, Equiv.symm_apply_apply, HasLeftIhom.symm_comp, HasLeftIhom.symm_comp,
    Equiv.symm_apply_apply]
    exact (strengthKey A B).symm
  leftStrengthEq₂ := leftStrengthT'_assoc_inv
  leftStrengthAssoc := leftStrengthT'_assoc
  leftStrengthNaturality := leftStrengthT'_naturality

/-- The monad `T : C ⥤ C` satisfies the right tensorial strength condition. -/
instance : RightStrength monadT (C := C) where
  rightStrength A B := rightStrengthT A B
  rightStrengthEq₁ := rightStrengthT_eta
  rightStrengthEq₂ := rightStrengthT_assoc_hom
  rightStrengthAssoc := rightStrengthT_assoc
  rightStrengthNaturality := rightStrengthT_naturality

end DialogueCategory
