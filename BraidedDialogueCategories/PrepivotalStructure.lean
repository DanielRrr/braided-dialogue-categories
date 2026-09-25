module

public import Mathlib.CategoryTheory.Monoidal.Category
public import BraidedDialogueCategories.DialogueCategories
import Mathlib.Tactic.CategoryTheory.Slice

@[expose] public section

namespace CategoryTheory
open MonoidalCategory
open DialogueCategory

namespace DialogueCategory
structure Turn (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [DialogueCategory.{v} C] where
  turn : ∀ A : C, leftDual A ≅ rightDual A
  turnNaturality : ∀ {A B : C} (f : B ⟶ A),
    leftDualFunctor.map f.op ≫ (turn B).hom = (turn A).hom ≫ rightDualFunctor.map f.op

class PrepivotalCategory (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [DialogueCategory.{v} C] where
  turn : Turn C

@[ext]
structure Wheel (C : Type v) [Category.{v} C] [MonoidalCategory C] [DialogueCategory.{v} C] where
  wheel : ∀ (A B : C), (A ⊗ B ⟶ bot) ≃ (B ⊗ A ⟶ bot)
  wheelNatInA : ∀ {A₁ A₂ B : C} (f : A₁ ⟶ A₂) (g : A₂ ⊗ B ⟶ bot),
    wheel A₁ B ((f ⊗ₘ 𝟙 B) ≫ g) = (𝟙 B ⊗ₘ f) ≫ wheel A₂ B g
  wheelNatInB : ∀ {A B₁ B₂ : C} (f : B₁ ⟶ B₂) (g : A ⊗ B₂ ⟶ bot),
    wheel A B₁ ((𝟙 A ⊗ₘ f) ≫ g) = (f ⊗ₘ 𝟙 A) ≫ wheel A B₂ g

variable (C : Type v) [Category.{v} C] [MonoidalCategory C] [D : DialogueCategory.{v} C]

/-- Getting a wheel from a turn. -/
def turnToWheel₁ (t : Turn C) (A B : C) (f : A ⊗ B ⟶ D.bot) :
  letI := D
  (B ⊗ A ⟶ D.bot) :=
  letI := D.leftClosed
  letI := D.rightClosed
  (HasRightIhom.homEquiv (A := A) (B := D.bot) B).symm ((HasLeftIhom.homEquiv (A := A) (B := D.bot) B).toFun f ≫ (t.turn A).hom)

/-- Getting a wheel from a turn: the other way round. -/
def turnToWheel₂ (t : Turn C) (A B : C) (f : B ⊗ A ⟶ D.bot) :
  letI := D
  (A ⊗ B ⟶ D.bot) :=
  letI := D.leftClosed
  letI := D.rightClosed
  (HasLeftIhom.homEquiv (A := A) (B := D.bot) B).symm ((HasRightIhom.homEquiv (A := A) (B := D.bot) B).toFun f ≫ (t.turn A).inv)

lemma turnToWheelInv₁ (t : Turn C) (A B : C) : Function.LeftInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro
  simp [turnToWheel₁, turnToWheel₂]

lemma turnToWheelInv₂ (t : Turn C) (A B : C) :  Function.RightInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro
  simp [turnToWheel₁, turnToWheel₂]

/-- The first key lemma in showing naturality in the proof that turns in dialogue categories induce wheels. -/
lemma turnToWheelNat₁ (t : Turn C) (A₁ A₂ B : C) (g : A₁ ⟶ A₂) (f : A₂ ⊗ B ⟶ bot) :
    turnToWheel₁ C t A₁ B (g ▷ B ≫ f) = B ◁ g ≫ turnToWheel₁ C t A₂ B f := by
  letI := D.leftClosed
  letI := D.rightClosed
  have hturn : HasLeftIhom.contramap (B := bot) g ≫ (t.turn A₁).hom =
      (t.turn A₂).hom ≫ HasRightIhom.contramap (B := bot) g := by
    exact t.turnNaturality g
  show (HasRightIhom.homEquiv (A := A₁) (B := bot) B).symm
      (HasLeftIhom.homEquiv (A := A₁) (B := bot) B (g ▷ B ≫ f) ≫ (t.turn A₁).hom) =
    B ◁ g ≫ (HasRightIhom.homEquiv (A := A₂) (B := bot) B).symm
      (HasLeftIhom.homEquiv (A := A₂) (B := bot) B f ≫ (t.turn A₂).hom)
  rw [← MonoidalCategory.tensorHom_id, HasLeftIhom.homEquiv_naturality_left (B := bot) g f, Category.assoc, hturn, ← Category.assoc, ← MonoidalCategory.id_tensorHom]
  exact (HasRightIhom.symm_naturality_left (B := bot) g _).symm

/-- The second key lemma in showing naturality in the proof that turns in dialogue categories induce wheels. -/
lemma turnToWheelNat₂ (t : Turn C) (A B₁ B₂ : C) (g : B₁ ⟶ B₂) (f : A ⊗ B₂ ⟶ bot)
  : turnToWheel₁ C t A B₁ (A ◁ g ≫ f) = g ▷ A ≫ turnToWheel₁ C t A B₂ f := by
  letI := D.leftClosed
  letI := D.rightClosed
  show
    (HasRightIhom.homEquiv (A := A) (B := bot) B₁).symm
      ((HasLeftIhom.homEquiv (A := A) (B := bot) B₁)
        (A ◁ g ≫ f) ≫ (t.turn A).hom) = g ▷ A ≫
      (HasRightIhom.homEquiv (A := A) (B := bot) B₂).symm
        ((HasLeftIhom.homEquiv (A := A) (B := bot) B₂) f ≫
          (t.turn A).hom)
  rw [← MonoidalCategory.id_tensorHom, HasLeftIhom.homEquivNaturalityₗ, Category.assoc]
  apply (HasRightIhom.homEquiv (A := A) (B := bot) B₁).injective
  simp [HasRightIhom.symm_apply_eq]


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

lemma wheelToTurnLemma₁ (wheel : Wheel C) (A : C) :
  (wheelToTurn₁ C wheel A) (𝟙 (leftDual A)) ≫ (wheelToTurn₂ C wheel A) (𝟙 (rightDual A)) = 𝟙 (leftDual A) := by
  letI := D.leftClosed
  letI := D.rightClosed
  unfold wheelToTurn₁ wheelToTurn₂
  set wheelA := wheel.wheel A (leftDual A) (leval A) with hWheelA
  set wheelB := (wheel.wheel A (rightDual A)).symm (reval A) with hWheelB
  set p : leftDual A ⟶ rightDual A :=
    HasRightIhom.homEquiv (A := A) (B := bot) (leftDual A) wheelA with hp
  set q : rightDual A ⟶ leftDual A :=
    HasLeftIhom.homEquiv (A := A) (B := bot) (rightDual A) wheelB with hq
  show p ≫ q = 𝟙 (leftDual A)
  apply (HasLeftIhom.homEquiv (A := A) (B := bot) (leftDual A)).symm.injective
  show (HasLeftIhom.homEquiv (A := A) (B := bot) (leftDual A)).symm (p ≫ q) = leval A
  rw [HasLeftIhom.symm_comp p q]
  have hq' : (HasLeftIhom.homEquiv (A := A) (B := bot) (rightDual A)).symm q = wheelB := by
    rw [hq, Equiv.symm_apply_apply]
  rw [hq']
  have hnat := wheel.wheelNatInB (A := A) (B₁ := leftDual A) (B₂ := rightDual A) p wheelB
  have hrw : wheel.wheel A (rightDual A) wheelB = reval A := by
    rw [hWheelB, Equiv.apply_symm_apply]
  rw [hrw] at hnat
  have hwheel :
      (𝟙 A ⊗ₘ p) ≫ wheelB = (wheel.wheel A (leftDual A)).symm ((p ⊗ₘ 𝟙 A) ≫ reval A) := by
    apply (wheel.wheel A (leftDual A)).injective
    rw [Equiv.apply_symm_apply]
    exact hnat
  rw [hwheel]
  have hp' : (p ⊗ₘ 𝟙 A) ≫ reval A = wheelA := by
    rw [hp, reval_eq_eval, HasRightIhom.uncurry_curry]
  rw [hp', hWheelA, Equiv.symm_apply_apply]

lemma wheelToTurnLemma₂ (wheel : Wheel C) (A : C) :
  (wheelToTurn₂ C wheel A) (𝟙 (rightDual A)) ≫ (wheelToTurn₁ C wheel A) (𝟙 (leftDual A)) = 𝟙 (rightDual A) := by
  letI := D.leftClosed
  letI := D.rightClosed
  unfold wheelToTurn₁ wheelToTurn₂
  set wheelA := wheel.wheel A (leftDual A) (leval A) with hWheelA
  set wheelB := (wheel.wheel A (rightDual A)).symm (reval A) with hWheelB
  set p : leftDual A ⟶ rightDual A := HasRightIhom.homEquiv (A := A) (B := bot) (leftDual A) wheelA with hp
  set q : rightDual A ⟶ leftDual A := HasLeftIhom.homEquiv (A := A) (B := bot) (rightDual A) wheelB with hq
  show q ≫ p = 𝟙 (rightDual A)
  apply (HasRightIhom.homEquiv (A := A) (B := bot) (rightDual A)).symm.injective
  show (HasRightIhom.homEquiv (A := A) (B := bot) (rightDual A)).symm (q ≫ p) = reval A
  rw [HasRightIhom.symm_comp]
  have hp' : (HasRightIhom.homEquiv (A := A) (B := bot) (leftDual A)).symm p = wheelA := by
    rw [Equiv.symm_apply_apply]
  rw [hp']
  have huncurry : (𝟙 A ⊗ₘ q) ≫ leval A = wheelB := by rw [hq, leval_eq_eval, HasLeftIhom.uncurry_curry]
  have hnat := wheel.wheelNatInB (A := A) (B₁ := rightDual A) (B₂ := leftDual A) q (leval A)
  rw [huncurry] at hnat
  have hrw : wheel.wheel A (rightDual A) wheelB = reval A := by
    rw [hWheelB, Equiv.apply_symm_apply]
  rw [hrw] at hnat
  exact hnat.symm

abbrev wheelToTurn : Turn C → Wheel C
  | t@{ turn, turnNaturality } =>
        Wheel.mk
         (fun A B =>
            Equiv.mk
              (turnToWheel₁ C t A B)
              (turnToWheel₂ C t A B)
              (turnToWheelInv₁ C t A B)
              (turnToWheelInv₂ C t A B))
         (fun {A₁ A₂ B} (g : A₁ ⟶ A₂) (f : A₂ ⊗ B ⟶ bot) => by simp; apply turnToWheelNat₁)
         (fun {A B₁ B₂} (g : B₁ ⟶ B₂) (f : A ⊗ B₂ ⟶ bot) => by simp; apply turnToWheelNat₂)
/--
The following establishes the equivalence between turns and wheels in any dialogue category.
-/
def TurnEquivWheel : Turn C ≃ Wheel C where
  toFun t := wheelToTurn C t
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
             (wheelToTurnLemma₂ C w A))
          (fun {A B} f => by
            letI := D.leftClosed
            letI := D.rightClosed
            show HasLeftIhom.contramap (B := bot) f ≫
                   HasRightIhom.homEquiv
                     (A := B)
                     (B := bot)
                     (leftDual B)
                     (w.wheel B (leftDual B) (leval B)) =
                  HasRightIhom.homEquiv
                     (A := A)
                     (B := bot)
                     (leftDual A)
                     (w.wheel A (leftDual A) (leval A)) ≫
                    HasRightIhom.contramap (B := bot) f
            set wheelB := w.wheel B (leftDual B) (leval B) with hwheelB
            set wheelA := w.wheel A (leftDual A) (leval A) with hwheelA
            set turnB := HasRightIhom.homEquiv (A := B) (B := bot) (leftDual B) wheelB with hturnB
            set turnA := HasRightIhom.homEquiv (A := A) (B := bot) (leftDual A) wheelA with hturnA
            show HasLeftIhom.contramap (B := bot) f ≫ turnB = turnA ≫ HasRightIhom.contramap (B := bot) f
            apply (HasRightIhom.homEquiv (A := B) (B := bot) (leftDual A)).symm.injective
            rw [HasRightIhom.symm_comp, HasRightIhom.symm_comp]
            have hturnB' : (HasRightIhom.homEquiv (A := B) (B := bot) (leftDual B)).symm turnB = wheelB := by
              rw [hturnB, Equiv.symm_apply_apply]
            have hcontramapR' : HasRightIhom.contramap (B := bot) f = HasRightIhom.homEquiv (A := B) (B := bot) (rightDual A)
               ((𝟙 (rightDual A) ⊗ₘ f) ≫ reval A) := by rfl
            have hcontramapR :
                 (HasRightIhom.homEquiv (A := B) (B := bot) (rightDual A)).symm
                 (HasRightIhom.contramap (B := bot) f) = (𝟙 (rightDual A) ⊗ₘ f) ≫ reval A := by simp [hcontramapR']
            rw [hturnB', hcontramapR, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
            have hreval : (turnA ⊗ₘ 𝟙 A) ≫ reval A = wheelA := by rw [hturnA]; exact HasRightIhom.uncurry_curry wheelA
            have turnReval : (turnA ⊗ₘ f) ≫ reval A = (𝟙 (leftDual A) ⊗ₘ f) ≫ (turnA ⊗ₘ 𝟙 A) ≫ reval A :=
              by rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
            rw [turnReval, hreval, hwheelB]
            have leftContraWheel :
              (HasLeftIhom.contramap (B := bot) f ⊗ₘ 𝟙 B) ≫ w.wheel B (leftDual B) (leval B) =
                w.wheel B (leftDual A) ((𝟙 B ⊗ₘ HasLeftIhom.contramap (B := bot) f) ≫ leval B) := by
              exact (w.wheelNatInB (HasLeftIhom.contramap (B := bot) f) (leval B)).symm
            rw [leftContraWheel, HasLeftIhom.contramapEval f, w.wheelNatInA f (leval A), hwheelA]
          )
  left_inv turn := by
    unfold wheelToTurn turnToWheel₁ turnToWheel₂ wheelToTurn₁ wheelToTurn₂
    simp
  right_inv wheel := by
    ext A B f
    letI := D.leftClosed
    letI := D.rightClosed
    show (HasRightIhom.homEquiv (A := A) (B := bot) B).symm (HasLeftIhom.homEquiv (A := A) (B := bot) B f ≫
        wheelToTurn₁ C wheel A (𝟙 (leftDual A))) = wheel.wheel A B f
    set fromBtoLeftDualA := HasLeftIhom.homEquiv (A := A) (B := bot) B f with hk
    set wheelA := wheel.wheel A (leftDual A) (leval A) with hwheelA
    set turnA := HasRightIhom.homEquiv (A := A) (B := bot) (leftDual A) wheelA with hturnA
    have hturnAeq : wheelToTurn₁ C wheel A (𝟙 (leftDual A)) = turnA := rfl
    rw [hturnAeq]
    have hf : f = (𝟙 A ⊗ₘ fromBtoLeftDualA) ≫ leval A := (HasLeftIhom.uncurry_curry f).symm
    have wheelf : wheel.wheel A B f = (fromBtoLeftDualA ⊗ₘ 𝟙 A) ≫ wheelA := by rw [hf]; exact wheel.wheelNatInB fromBtoLeftDualA (leval A)
    have wheelReval : wheelA = (turnA ⊗ₘ 𝟙 A) ≫ reval A := by rw [hturnA]; exact (HasRightIhom.uncurry_curry wheelA).symm
    rw [wheelf, wheelReval, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
    exact HasRightIhom.symm_apply_eq (fromBtoLeftDualA ≫ turnA)


@[instance_reducible]
def prepivotalWithWheel (C : Type v) [Category.{v,v} C] [m : MonoidalCategory.{v} C] [DialogueCategory.{v} C] (wheel : Wheel C) : PrepivotalCategory C where
  turn := (TurnEquivWheel C).symm wheel

lemma nameConnectedWithTurn (A B : C) [p : PrepivotalCategory C] (f : A ⊗ B ⟶ D.bot) :
  turnToWheel₁ C p.turn A B f =
  ((ρ_ B).inv ⊗ₘ 𝟙 A) ≫ ((𝟙 B ⊗ₘ (leftName (A ⊗ B) f)) ⊗ₘ 𝟙 A) ≫
  ((lev B A) ⊗ₘ 𝟙 A) ≫
  ((p.turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A := by
  letI := D.leftClosed
  letI := D.rightClosed
  simp
  slice_rhs 2 3 => rw [associator_inv_naturality_middle B (leftName (A ⊗ B) f) A]
  rw [Category.assoc, Category.assoc, Category.assoc]
  slice_rhs 1 2 => rw [triangle_assoc_comp_left_inv B A]
  rw [Category.assoc, Category.assoc, Category.assoc]
  have fact : (B ◁ leftName (A ⊗ B) f) ▷ A ≫ lev B A ▷ A
    = (B ◁ leftName (A ⊗ B) f ≫ lev B A) ▷ A := by simp
  slice_rhs 2 3 => rw [fact]
  unfold lev
  rw [← HasLeftIhom.homEquivNaturalityₗ]
  have fact'' : (𝟙 A ⊗ₘ B ◁ leftName (A ⊗ B) f) ≫ (α_ A B (leftDual (A ⊗ B))).inv
    = (α_ A B (𝟙_ C)).inv ≫ (𝟙 (A ⊗ B) ⊗ₘ leftName (A ⊗ B) f) := by simp
  slice_rhs 2 3 =>
    rw [← Category.assoc, fact'', Category.assoc, leftNameUncurry (A ⊗ B) f]
    congr
    rw [← Category.assoc, ← whiskerLeft_rightUnitor]
  have idWhisker : A ◁ (ρ_ B).hom = 𝟙 A ⊗ₘ (ρ_ B).hom := by simp
  slice_rhs 2 3 => rw [idWhisker, HasLeftIhom.homEquivNaturalityₗ]
  simp; unfold turnToWheel₁ reval; simp
  rw [← Category.assoc, ← comp_whiskerRight ((HasLeftIhom.homEquiv B) f) (PrepivotalCategory.turn.turn A).hom A, HasRightIhom.symm_apply_eq]
  simp

lemma wheel_via_turn_evals (A : C) [p : PrepivotalCategory C] :
  turnToWheel₁ C p.turn A (leftDual A) (leval A) =
  ((p.turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A := by
  rw [nameConnectedWithTurn]
  have ident :
    ((ρ_ (leftDual A)).inv ⊗ₘ 𝟙 A) ≫
    ((𝟙 (leftDual A) ⊗ₘ leftName (A ⊗ leftDual A) (leval A)) ⊗ₘ 𝟙 A) ≫
      (lev (leftDual A) A ⊗ₘ 𝟙 A) = 𝟙 (leftDual A ⊗ A) := by sorry
  sorry

end DialogueCategory
