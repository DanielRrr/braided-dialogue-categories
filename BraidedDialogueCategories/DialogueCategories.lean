module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Yoneda
public import BraidedDialogueCategories.InternalHoms

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory

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

/-- The left evaluation arrow `A ⊗ [A, bot]ₗ ⟶ bot`-/
def leval (A : C) : A ⊗ leftDual A ⟶ bot :=
  letI := D.leftClosed
  (HasLeftIhom.homEquiv (A := A) (B := DialogueCategory.bot) (leftDual A)).symm (𝟙 (leftDual A))

/-- `leftDual` is a contravariant functor. -/
def leftDualMap {A B : C} (f : A ⟶ B) : leftDual B ⟶ leftDual A :=
  letI := D.leftClosed
  HasLeftIhom.homEquiv
      (A := A)
      (B := DialogueCategory.bot)
      (leftDual B)
      ((f ⊗ₘ 𝟙 (leftDual B)) ≫ leval B)

def leftDualFunctor : Cᵒᵖ ⥤ C where
  obj A := leftDual A.unop
  map := fun {X Y} f =>
    letI := D.leftClosed
    HasLeftIhom.homEquiv
      (A := Y.unop)
      (B := D.bot)
      (leftDual X.unop)
      ((f.unop ⊗ₘ 𝟙 (leftDual X.unop)) ≫ leval X.unop)
  map_id X := by
    simp[leftDual, leval]
  map_comp {A B C} f g := by
    letI := D.leftClosed
    rw [← HasLeftIhom.homEquivNaturalityₗ]
    simp[leftDual, leval]
    sorry

/-- `[A, bot]ᵣ`. -/
abbrev rightDual (A : C) : C :=
  letI := D.rightClosed
  HasRightIhom.internalHomᵣ A D.bot

/-- The right evaluation arrow `[A, bot]ᵣ ⊗ A ⟶ bot`-/
def reval (A : C) : rightDual A ⊗ A ⟶ bot :=
  letI := D.rightClosed
  (HasRightIhom.homEquiv (A := A) (B := DialogueCategory.bot) (rightDual A)).symm (𝟙 (rightDual A))

/-- `rightDual` is a contravariant functor. -/
def rightDualMap {A B : C} (f : A ⟶ B) : rightDual B ⟶ rightDual A :=
  letI := D.rightClosed
  HasRightIhom.homEquiv (A := A) (B := DialogueCategory.bot) (rightDual B)
    ((𝟙 (rightDual B) ⊗ₘ f) ≫ reval B)

/-- `rightDual` is a contravariant functor.  -/
def rightDualFunctor : Cᵒᵖ ⥤ C where
  obj A := rightDual A.unop
  map := fun {X Y} f =>
    letI := D.rightClosed
    HasRightIhom.homEquiv
      (A := Y.unop)
      (B := D.bot)
      (rightDual X.unop)
      ((𝟙 (rightDual X.unop) ⊗ₘf.unop) ≫ reval X.unop)
  map_id X := by simp[rightDual, reval]
  map_comp {A B C} f g := by sorry

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

structure Turn (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [DialogueCategory.{v} C] where
  turn : ∀ A : C, leftDual A ≅ rightDual A
  turnNaturality : ∀ {A B : C} (f : B ⟶ A),
    leftDualFunctor.map f.op ≫ (turn B).hom = (turn A).hom ≫ rightDualFunctor.map f.op

structure Wheel (C : Type v) [Category.{v} C] [MonoidalCategory C] [DialogueCategory.{v} C] where
  wheel : ∀ (A B : C), (A ⊗ B ⟶ bot) ≃ (B ⊗ A ⟶ bot)
  wheelNatInA : ∀ {A₁ A₂ B : C} (f : A₁ ⟶ A₂) (g : A₂ ⊗ B ⟶ bot),
    wheel A₁ B ((f ⊗ₘ 𝟙 B) ≫ g) = (𝟙 B ⊗ₘ f) ≫ wheel A₂ B g
  wheelNatInB : ∀ {A B₁ B₂ : C} (f : B₁ ⟶ B₂) (g : A ⊗ B₂ ⟶ bot),
    wheel A B₁ ((𝟙 A ⊗ₘ f) ≫ g) = (f ⊗ₘ 𝟙 A) ≫ wheel A B₂ g

variable (C : Type v) [Category.{v} C] [MonoidalCategory C] [D : DialogueCategory.{v} C]

def turnToWheel₁ (t : Turn C) (A B : C) (f : A ⊗ B ⟶ D.bot) :
  letI := D
  (B ⊗ A ⟶ D.bot) :=
  letI := D.leftClosed
  letI := D.rightClosed
  (HasRightIhom.homEquiv (A := A) (B := D.bot) B).symm ((HasLeftIhom.homEquiv (A := A) (B := D.bot) B).toFun f ≫ (t.turn A).hom)

def turnToWheel₂ (t : Turn C) (A B : C) (f : B ⊗ A ⟶ D.bot) :
  letI := D
  (A ⊗ B ⟶ D.bot) :=
  letI := D.leftClosed
  letI := D.rightClosed
  (HasLeftIhom.homEquiv (A := A) (B := D.bot) B).symm ((HasRightIhom.homEquiv (A := A) (B := D.bot) B).toFun f ≫ (t.turn A).inv)

lemma turnToWheelInv₁ (t : Turn C) (A B : C) : Function.LeftInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro f
  simp [turnToWheel₁, turnToWheel₂]

lemma turnToWheelInv₂ (t : Turn C) (A B : C) :  Function.RightInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro f
  simp [turnToWheel₁, turnToWheel₂]

/-- The first key lemma in showing naturality in the proof that turns in dialogue categories induces wheels. -/
lemma turnToWheelNat₁ (t : Turn C) (A₁ A₂ B : C) (g : A₁ ⟶ A₂) (f : A₂ ⊗ B ⟶ bot) :
  turnToWheel₁ C t A₁ B (g ▷ B ≫ f) = B ◁ g ≫ turnToWheel₁ C t A₂ B f := by
  letI := D.leftClosed
  letI := D.rightClosed
  unfold turnToWheel₁
  have hleft : (HasLeftIhom.homEquiv (A := A₁) (B := D.bot) B).toFun (g ▷ B ≫ f)=
    (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f ≫ leftDualMap g := by
    unfold leftDualMap
    rw [← HasLeftIhom.homEquivNaturalityₗ]
    simp only [leval]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    have eval_beta :
      (𝟙 A₂ ⊗ₘ (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f) ≫ leval A₂ = f := by
      apply (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).injective
      rw [HasLeftIhom.homEquivNaturalityₗ]
      simp [leval]
    congr 1
    simp only [Category.id_comp, Category.comp_id]
    change
      g ▷ B ≫ f =
        (g ⊗ₘ (HasLeftIhom.homEquiv B).toFun f) ≫ leval A₂
    have htensor :
        (g ⊗ₘ (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f) =
          (g ⊗ₘ 𝟙 B) ≫
            (𝟙 A₂ ⊗ₘ
              (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f) := by
      simp
      simpa using
        (tensorHom_comp_tensorHom
          (f₁ := g)
          (f₂ := 𝟙 B)
          (g₁ := 𝟙 A₂)
          (g₂ := (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f)).symm
    rw [htensor, Category.assoc, eval_beta]
    simp
  have hturn :
    leftDualMap g ≫ (t.turn A₁).hom =
      (t.turn A₂).hom ≫ rightDualMap g := by
    exact t.turnNaturality g
  have hright :
    (HasRightIhom.homEquiv (A := A₁) (B := D.bot) B).toFun
        (B ◁ g ≫
          (HasRightIhom.homEquiv (A := A₂) (B := D.bot) B).invFun
            ((HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f ≫ (t.turn A₂).hom)) =
        (HasLeftIhom.homEquiv (A := A₂) (B := D.bot) B).toFun f ≫ (t.turn A₂).hom ≫ rightDualMap g := by
    unfold rightDualMap
    rw [← HasRightIhom.homEquivNaturalityᵣ]
    sorry
  apply (HasRightIhom.homEquiv (A := A₁) (B := D.bot) B).injective
  rw [Equiv.apply_symm_apply, hleft, Category.assoc, hturn, ← hright]
  rfl

/-- The first key lemma in showing naturality in the proof that turns in dialogue categories induces wheels. -/
lemma turnToWheelNat₂ (t : Turn C) (A B₁ B₂ : C) (g : B₁ ⟶ B₂) (f : A ⊗ B₂ ⟶ bot)
  : turnToWheel₁ C t A B₁ (A ◁ g ≫ f) = g ▷ A ≫ turnToWheel₁ C t A B₂ f := by
  letI := D.leftClosed
  letI := D.rightClosed
  unfold turnToWheel₁
  sorry

def wheelToTurn₁ (wheel : Wheel C) (A : C) : (leftDual A ⟶ leftDual A) ≃ (leftDual A ⟶ rightDual A) :=
  letI := D.leftClosed
  letI := D.rightClosed
  let leftIHomEq := (HasLeftIhom.homEquiv (A := A) (B := D.bot) (leftDual A)).symm
  let wheelEq := wheel.wheel A (leftDual A)
  let rightIHomEq := (HasRightIhom.homEquiv (A := A) (B := D.bot) (leftDual A))
  Equiv.trans (Equiv.trans leftIHomEq wheelEq) rightIHomEq

def wheelToTurn₂ (wheel : Wheel C) (A : C) : (rightDual A ⟶ rightDual A) ≃ (rightDual A ⟶ leftDual A) :=
  letI := D.leftClosed
  letI := D.rightClosed
  let rightIHomEq := (HasRightIhom.homEquiv (A := A) (B := D.bot) (rightDual A)).symm
  let wheelEq := (wheel.wheel A (rightDual A)).symm
  let leftIHomEq := HasLeftIhom.homEquiv (A := A) (B := D.bot) (rightDual A)
  Equiv.trans (Equiv.trans rightIHomEq wheelEq) leftIHomEq

lemma wheelToTurnLemma₁ (wheel : Wheel C) (A : C) : (wheelToTurn₁ C wheel A) (𝟙 (leftDual A)) ≫ (wheelToTurn₂ C wheel A) (𝟙 (rightDual A)) = 𝟙 (leftDual A) := by
  unfold wheelToTurn₁ wheelToTurn₂

/--
The following establishes the equivalence between turns and wheels in any dialogue category.
-/
def TurnEquivWheel : Turn C ≃ Wheel C where
  toFun t :=
    letI := D.leftClosed
    letI := D.rightClosed
    match t with
      | { turn, turnNaturality } =>
        Wheel.mk
         (fun A B =>
            Equiv.mk
              (turnToWheel₁ C t A B)
              (turnToWheel₂ C t A B)
              (turnToWheelInv₁ C t A B)
              (turnToWheelInv₂ C t A B)
          )
         (fun {A₁ A₂ B} (g : A₁ ⟶ A₂) (f : A₂ ⊗ B ⟶ bot) => by
           simp
           apply turnToWheelNat₁
          )
         (fun {A B₁ B₂} (g : B₁ ⟶ B₂) (f : A ⊗ B₂ ⟶ bot) => by
           simp
           apply turnToWheelNat₂
         )
  invFun w :=
    letI := D.leftClosed
    letI := D.rightClosed
    match w with
      | { wheel, wheelNatInA, wheelNatInB } =>
        Turn.mk
          (fun A => CategoryTheory.Iso.mk
             (wheelToTurn₁ C w A (𝟙 (leftDual A)))
             (wheelToTurn₂ C w A (𝟙 (rightDual A)))
             (wheelToTurnLemma₁ C w A)
             sorry
          )
          (fun {A B} f => sorry)
  left_inv := sorry
  right_inv := sorry

class PivotalDialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C] [DialogueCategory C] where
    pivotalTurn : Turn C

end DialogueCategory

open DialogueCategory in
class StarAutonomousCategory (C : Type v)
    [Category.{v} C] [MonoidalCategory C] [DialogueCategory C] where
  etaStar₁ : ∀ A : C, A ≅ leftDual (rightDual A)
  etaStar₂ : ∀ A : C, A ≅ rightDual (leftDual A)
