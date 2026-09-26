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

namespace DialogueCategory

variable [D : DialogueCategory C]

/-- `[A, bot]ₗ`. -/
abbrev leftDual (A : C) : C :=
  letI := D.leftClosed
  HasLeftIhom.internalHomₗ A D.bot

/-- `[A, bot]ᵣ`. -/
abbrev rightDual (A : C) : C :=
  letI := D.rightClosed
  HasRightIhom.internalHomᵣ A D.bot

/-- The left evaluation arrow `A ⊗ [A, bot]ₗ ⟶ bot`-/
abbrev leval (A : C) : A ⊗ leftDual A ⟶ bot :=
  letI := D.leftClosed
  HasLeftIhom.leftEval (A := A) (B := DialogueCategory.bot)

lemma leval_eq_eval (A : C) :
  letI := D.leftClosed
  leval A = HasLeftIhom.leftEval (A := A) (B := D.bot) := rfl

/-- `leftDual` is a contravariant functor. -/
def L : C ⥤ Cᵒᵖ where
  obj A := Opposite.op (leftDual A)
  map {A B} f :=
    letI := D.leftClosed
    (HasLeftIhom.contramap (B := D.bot) f).op
  map_id A := by simp
  map_comp {A B C} f g := by letI := D.leftClosed; simp

/-- `leftDual` is a contravariant functor. It's called L^op in Melliés's manuscript. -/
def Lop : Cᵒᵖ ⥤ C where
  obj A := leftDual A.unop
  map := fun {X Y} f =>
    letI := D.leftClosed
    HasLeftIhom.contramap f.unop
  map_id A := by simp
  map_comp {A B C} f g := by
   letI := D.leftClosed
   simp

/-- `rightDual` is a contravariant functor. It's called `R` in Melliés's manuscript. -/
def R : Cᵒᵖ ⥤ C where
  obj A := rightDual A.unop
  map {X Y} f :=
     letI := D.rightClosed
     HasRightIhom.contramap f.unop        -- f.unop : Y.unop ⟶ X.unop, purely in C
  map_id A := by simp
  map_comp f g := by letI := D.rightClosed; simp

def Rop : C ⥤ Cᵒᵖ where
  obj A := Opposite.op (rightDual A)
  map {A B} f :=
    letI := D.rightClosed
    (HasRightIhom.contramap (B := D.bot) f).op
  map_id A := by simp
  map_comp f g := by letI := D.rightClosed; simp


/-- The right evaluation arrow `[A, bot]ᵣ ⊗ A ⟶ bot`-/
def reval (A : C) : rightDual A ⊗ A ⟶ bot :=
  letI := D.rightClosed
  HasRightIhom.evalRight (A := A) (B := DialogueCategory.bot)

lemma reval_eq_eval (A : C) :
  letI := D.rightClosed
  reval A = HasRightIhom.evalRight (A := A) (B := D.bot) := rfl

def lev (B A : C) : B ⊗ leftDual (A ⊗ B) ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv
      (A := A)
      (B := DialogueCategory.bot)
      (B ⊗ leftDual (A ⊗ B))
      ((associator A B (leftDual (A ⊗ B))).inv ≫
        leval (A ⊗ B))

def rev (A B : C) : (rightDual (A ⊗ B)) ⊗ A ⟶ rightDual B :=
  letI := D.rightClosed
  HasRightIhom.homEquiv (A := B) (B := DialogueCategory.bot)
    (rightDual (A ⊗ B) ⊗ A)
    ((associator (rightDual (A ⊗ B)) A B).hom ≫ reval (A ⊗ B))

def leftName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv (A := A) (B := D.bot)
    (𝟙_ C)
    ((rightUnitor A).hom ≫ f)

lemma leftNameUncurry (A : C) (f : A ⟶ bot) :
    ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A = (rightUnitor A).hom ≫ f := by
  letI := D.leftClosed
  let e₀ :=
    HasLeftIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  let e₁ := HasLeftIhom.homEquiv (A := A) (B := D.bot) (leftDual A)
  apply e₀.injective
  let e₂ := HasLeftIhom.homEquivNaturalityₗ (A := A) (B := D.bot) (f := leftName A f) (g := leval A)
  rw [e₂]
  change leftName A f ≫ e₁ (e₁.symm (𝟙 (leftDual A))) = e₀ ((rightUnitor A).hom ≫ f)
  rw [e₁.apply_symm_apply]
  simp [leftName, e₀]

lemma leftNameFact (A : C) (f : A ⟶ bot) : f = (rightUnitor A).inv ≫ ((𝟙 A) ⊗ₘ leftName A f) ≫ leval A := by
  rw [leftNameUncurry]
  simp

def rightName (A : C) (f : A ⟶ bot) : (𝟙_ C) ⟶ rightDual A :=
  letI := D.rightClosed
  HasRightIhom.homEquiv
    (A := A)
    (B := D.bot)
    (𝟙_ C)
    ((leftUnitor A).hom ≫ f)

lemma rightNameUncurry (A : C) (f : A ⟶ bot) :
  (rightName A f ⊗ₘ (𝟙 A)) ≫ reval A = (leftUnitor A).hom ≫ f := by
  letI := D.rightClosed
  let e₀ := HasRightIhom.homEquiv (A := A) (B := D.bot) (𝟙_ C)
  let e₁ := HasRightIhom.homEquiv (A := A) (B := D.bot) (rightDual A)
  apply e₀.injective
  let e₂ := HasRightIhom.homEquivNaturalityᵣ (A := A) (B := D.bot) (f := rightName A f) (g := reval A)
  rw [e₂]
  change rightName A f ≫ e₁ (e₁.symm (𝟙 (rightDual A))) = e₀ ((leftUnitor A).hom ≫ f)
  rw [e₁.apply_symm_apply]
  simp [rightName, e₀]

lemma rightNameFact (A : C) (f : A ⟶ bot) : f = (leftUnitor A).inv ≫ (rightName A f ⊗ₘ (𝟙 A)) ≫ reval A := by
  rw [rightNameUncurry]
  simp
end DialogueCategory

open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category.{v} C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ leftDual (rightDual A)
  etaStar₂ : ∀ A : C, A ≅ rightDual (leftDual A)
