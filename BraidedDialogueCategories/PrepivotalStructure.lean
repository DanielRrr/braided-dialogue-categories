module

public import Mathlib.CategoryTheory.Monoidal.Category
public import BraidedDialogueCategories.DialogueCategories
import Mathlib.Tactic.CategoryTheory.Slice

@[expose] public section

namespace CategoryTheory
open MonoidalCategory
open DialogueCategory

namespace DialogueCategory

/-- The isomorphism between the left and right negations in a dialogue category. -/
structure Turn (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [DialogueCategory.{v} C] where
  turn : ∀ A : C, leftDual A ≅ rightDual A
  turnNaturality : ∀ {A B : C} (f : B ⟶ A),
    Lop.map f.op ≫ (turn B).hom = (turn A).hom ≫ R.map f.op

class PrepivotalCategory (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [DialogueCategory.{v} C] where
  turn : Turn C

/-- The negative symmetry: the isomorphism between the negated `A ⊗ B` and the negated `B ⊗ A`.-/
@[ext] structure Wheel (C : Type v) [Category.{v} C] [MonoidalCategory C] [DialogueCategory.{v} C] where
  wheel : ∀ (A B : C), (A ⊗ B ⟶ bot) ≃ (B ⊗ A ⟶ bot)
  wheelNatInA : ∀ {A₁ A₂ B : C} (f : A₁ ⟶ A₂) (g : A₂ ⊗ B ⟶ bot),
    wheel A₁ B ((f ⊗ₘ 𝟙 B) ≫ g) = (𝟙 B ⊗ₘ f) ≫ wheel A₂ B g
  wheelNatInB : ∀ {A B₁ B₂ : C} (f : B₁ ⟶ B₂) (g : A ⊗ B₂ ⟶ bot),
    wheel A B₁ ((𝟙 A ⊗ₘ f) ≫ g) = (f ⊗ₘ 𝟙 A) ≫ wheel A B₂ g

variable (C : Type v) [Category.{v} C] [MonoidalCategory C] [D : DialogueCategory.{v} C]

/-- Getting a wheel from a turn. -/
@[simp] def turnToWheel₁ (t : Turn C) (A B : C) (f : A ⊗ B ⟶ D.bot) :
  (B ⊗ A ⟶ D.bot) :=
  (HasRightIhom.homEquiv B).symm ((HasLeftIhom.homEquiv B).toFun f ≫ (t.turn A).hom)

/-- Getting a wheel from a turn: the other way round. -/
def turnToWheel₂ (t : Turn C) (A B : C) (f : B ⊗ A ⟶ D.bot) :
  (A ⊗ B ⟶ D.bot) :=
  (HasLeftIhom.homEquiv B).symm ((HasRightIhom.homEquiv B).toFun f ≫ (t.turn A).inv)

/-- `turnToWheel₂` is the left inverse to `turnToWheel₁`. -/
lemma turnToWheel_leftInv (t : Turn C) (A B : C) : Function.LeftInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro
  simp [turnToWheel₁, turnToWheel₂]

/-- `turnToWheel` is the right inverse to `turnToWheel₁`. -/
lemma turnToWheel_rightInv (t : Turn C) (A B : C) :  Function.RightInverse (turnToWheel₂ C t A B) (turnToWheel₁ C t A B) := by
  intro
  simp [turnToWheel₁, turnToWheel₂]

/-- Rephrasing the turn naturality via contramap. -/
@[simp] lemma left_turn_right {A B : C} (t : Turn C) (f : A ⟶ B) : HasLeftIhom.contramap f ≫ (t.turn A).hom = (t.turn B).hom ≫ HasRightIhom.contramap f := by
  exact t.turnNaturality f

/-- The first key lemma in showing naturality in the proof that turns in dialogue categories induce wheels. -/
lemma turnToWheelNat₁ (t : Turn C) (A₁ A₂ B : C) (f : A₁ ⟶ A₂) (g : A₂ ⊗ B ⟶ bot) :
    turnToWheel₁ C t A₁ B (f ▷ B ≫ g) = B ◁ f ≫ turnToWheel₁ C t A₂ B g := by
  simp [turnToWheel₁]
  rw [← MonoidalCategory.tensorHom_id, HasLeftIhom.homEquiv_naturality_left f g,
      Category.assoc, left_turn_right, ← Category.assoc, ← MonoidalCategory.id_tensorHom]
  exact (HasRightIhom.symm_naturality_left f _).symm

/-- The second key lemma in showing naturality in the proof that turns in dialogue categories induce wheels. -/
lemma turnToWheelNat₂ (t : Turn C) (A B₁ B₂ : C) (g : B₁ ⟶ B₂) (f : A ⊗ B₂ ⟶ bot)
  : turnToWheel₁ C t A B₁ (A ◁ g ≫ f) = g ▷ A ≫ turnToWheel₁ C t A B₂ f := by
  simp [turnToWheel₁]
  rw [← MonoidalCategory.id_tensorHom, HasLeftIhom.homEquivNaturalityₗ, Category.assoc]
  apply (HasRightIhom.homEquiv B₁).injective
  simp [HasRightIhom.symm_apply_eq]

/-- The 1-to-1 correspondence between `leftDual A ⟶ leftDual A` and `leftDual A ⟶ rightDual A` obtain from `Wheel`. -/
def wheelToTurn₁ (wheel : Wheel C) (A : C) : (leftDual A ⟶ leftDual A) ≃ (leftDual A ⟶ rightDual A) :=
  calc
  (leftDual A ⟶ leftDual A) ≃ (A ⊗ leftDual A ⟶ bot) := (HasLeftIhom.homEquiv (leftDual A)).symm
  _ ≃ (leftDual A ⊗ A ⟶ bot) := wheel.wheel A (leftDual A)
  _ ≃ (leftDual A ⟶ rightDual A) := HasRightIhom.homEquiv (leftDual A)

/-- The 1-to-1 correspondence between `rightDual A ⟶ rightDual A` and `rightDual A ⟶ leftDual A` obtain from `Wheel`. -/
def wheelToTurn₂ (wheel : Wheel C) (A : C) : (rightDual A ⟶ rightDual A) ≃ (rightDual A ⟶ leftDual A) :=
  calc
  (rightDual A ⟶ rightDual A) ≃ (rightDual A ⊗ A ⟶ bot) := (HasRightIhom.homEquiv (rightDual A)).symm
  _ ≃ (A ⊗ rightDual A ⟶ bot) := (wheel.wheel A (rightDual A)).symm
  _ ≃ (rightDual A ⟶ leftDual A) := HasLeftIhom.homEquiv (rightDual A)

/-- The wheel of the left evaluation map. -/
def wheel_leval (wheel : Wheel C) (A : C) := wheel.wheel A (leftDual A) (leval A)

/-- The wheel of the right evaluation map. -/
def wheel_reval (wheel : Wheel C) (A : C) := (wheel.wheel A (rightDual A)).symm (reval A)

/-- mapping the left dual to the right dual via the right internal hom definition applied to
the wheel of the left evaluation map -/
def left_to_right (wheel : Wheel C) (A : C) : leftDual A ⟶ rightDual A :=
  HasRightIhom.homEquiv (leftDual A) (wheel_leval C wheel A)

/-- Mapping the right dual to the left dual via the left internal hom definition applied to
the wheel of the right evaluation map. -/
def right_to_left (wheel : Wheel C) (A : C) : rightDual A ⟶ leftDual A :=
  HasLeftIhom.homEquiv (rightDual A) (wheel_reval C wheel A)

/-- The composition of `left_to_right` and `right_to_left` is identity. -/
lemma left_to_right_to_left_id (wheel : Wheel C) (A : C) : left_to_right C wheel A ≫ right_to_left C wheel A = 𝟙 (leftDual A) := by
  apply (HasLeftIhom.homEquiv (leftDual A)).symm.injective
  -- now we must show that `(homEquiv (leftDual A)).symm (left_to_right ≫ right_to_left) = (homEquiv (leftDual A)).symm (𝟙 (leftDual A))`:
  show (HasLeftIhom.homEquiv (leftDual A)).symm (left_to_right C wheel A ≫ right_to_left C wheel A) = leval A
  rw [HasLeftIhom.symm_comp (left_to_right C wheel A) (right_to_left C wheel A)]
  -- observe that the wheel of the right evaluation map is equal to `homEquiv (rightDual A)` applied to `right_to_left`:
  have hq' : (HasLeftIhom.homEquiv (rightDual A)).symm (right_to_left C wheel A)  = wheel_reval C wheel A := by
    rw [right_to_left, Equiv.symm_apply_apply]
  rw [hq']
  -- instantiate the naturality of `wheel` for `left_to_right` and `wheel_reval`:
  have hnat := wheel.wheelNatInB (left_to_right C wheel A) (wheel_reval C wheel A)
  -- expressing `reval` with the wheel applied to the wheel of the right evaluation map
  have hrw : wheel.wheel A (rightDual A) (wheel_reval C wheel A) = reval A := by
    rw [wheel_reval, Equiv.apply_symm_apply]
  rw [hrw] at hnat
  have hwheel :
      (𝟙 A ⊗ₘ left_to_right C wheel A) ≫ wheel_reval C wheel A = (wheel.wheel A (leftDual A)).symm ((left_to_right C wheel A ⊗ₘ 𝟙 A) ≫ reval A) := by
    apply (wheel.wheel A (leftDual A)).injective
    rw [Equiv.apply_symm_apply]
    exact hnat
  rw [hwheel]
  have hp' : (left_to_right C wheel A ⊗ₘ 𝟙 A) ≫ reval A = wheel_leval C wheel A := by
    rw [left_to_right, reval_eq_eval, HasRightIhom.uncurry_curry]
  rw [hp', wheel_leval, Equiv.symm_apply_apply]

/-- The composition of `wheelToTurn₂` and `wheelToTurn₁` is identity. -/
lemma right_to_left_to_right_id (wheel : Wheel C) (A : C) :
  (right_to_left C wheel A) ≫ (left_to_right C wheel A) = 𝟙 (rightDual A) := by
  apply (HasRightIhom.homEquiv (rightDual A)).symm.injective
  show (HasRightIhom.homEquiv (rightDual A)).symm (right_to_left C wheel A ≫ left_to_right C wheel A) = reval A
  rw [HasRightIhom.symm_comp]
  have hp' : (HasRightIhom.homEquiv (leftDual A)).symm (left_to_right C wheel A) = (wheel_leval C wheel A) := by
    apply Equiv.symm_apply_apply
  rw [hp']
  have huncurry : (𝟙 A ⊗ₘ right_to_left C wheel A) ≫ leval A = (wheel_reval C wheel A) := by rw [right_to_left, leval_eq_eval, HasLeftIhom.uncurry_curry]
  have hnat := wheel.wheelNatInB (right_to_left C wheel A) (leval A)
  rw [huncurry] at hnat
  have hrw : wheel.wheel A (rightDual A) (wheel_reval C wheel A) = reval A := by
    rw [wheel_reval, Equiv.apply_symm_apply]
  rw [hrw] at hnat
  exact hnat.symm

abbrev wheelToTurn : Turn C → Wheel C
  | t => Wheel.mk
         (fun A B => Equiv.mk (turnToWheel₁ C t A B) (turnToWheel₂ C t A B)
              (turnToWheel_leftInv C t A B)
              (turnToWheel_rightInv C t A B))
         (by simp; apply turnToWheelNat₁)
         (by simp; apply turnToWheelNat₂)
/--
The following establishes the equivalence between turns and wheels in any dialogue category.
-/
def TurnEquivWheel : Turn C ≃ Wheel C where
  toFun t := wheelToTurn C t
  invFun
    | w@{ wheel, wheelNatInA, wheelNatInB } =>
        Turn.mk
          (fun A => CategoryTheory.Iso.mk
             (wheelToTurn₁ C w A (𝟙 (leftDual A)))
             (wheelToTurn₂ C w A (𝟙 (rightDual A)))
             (left_to_right_to_left_id C w A)
             (right_to_left_to_right_id C w A))
          (fun {A B} f => by
            show HasLeftIhom.contramap f ≫
                  HasRightIhom.homEquiv (leftDual B) (w.wheel B (leftDual B) (leval B)) =
                  HasRightIhom.homEquiv (leftDual A) (w.wheel A (leftDual A) (leval A)) ≫ HasRightIhom.contramap f
            set wheelB := w.wheel B (leftDual B) (leval B) with hwheelB
            set wheelA := w.wheel A (leftDual A) (leval A) with hwheelA
            set turnB := HasRightIhom.homEquiv (leftDual B) wheelB with hturnB
            set turnA := HasRightIhom.homEquiv (leftDual A) wheelA with hturnA
            show HasLeftIhom.contramap f ≫ turnB = turnA ≫ HasRightIhom.contramap f
            apply (HasRightIhom.homEquiv (leftDual A)).symm.injective
            rw [HasRightIhom.symm_comp, HasRightIhom.symm_comp]
            have hturnB' : (HasRightIhom.homEquiv (leftDual B)).symm turnB = wheelB := by
              rw [hturnB, Equiv.symm_apply_apply]
            have hcontramapR' : HasRightIhom.contramap f = HasRightIhom.homEquiv (rightDual A)
               ((𝟙 (rightDual A) ⊗ₘ f) ≫ reval A) := by rfl
            have hcontramapR : (HasRightIhom.homEquiv (rightDual A)).symm
                 (HasRightIhom.contramap f) = (𝟙 (rightDual A) ⊗ₘ f) ≫ reval A := by simp [hcontramapR']
            rw [hturnB', hcontramapR, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
            have hreval : (turnA ⊗ₘ 𝟙 A) ≫ reval A = wheelA := by rw [hturnA]; exact HasRightIhom.uncurry_curry wheelA
            have turnReval : (turnA ⊗ₘ f) ≫ reval A = (𝟙 (leftDual A) ⊗ₘ f) ≫ (turnA ⊗ₘ 𝟙 A) ≫ reval A :=
              by rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
            rw [turnReval, hreval, hwheelB]
            have leftContraWheel :
              (HasLeftIhom.contramap f ⊗ₘ 𝟙 B) ≫ w.wheel B (leftDual B) (leval B) =
                w.wheel B (leftDual A) ((𝟙 B ⊗ₘ HasLeftIhom.contramap f) ≫ leval B) := by
              exact (w.wheelNatInB (HasLeftIhom.contramap f) (leval B)).symm
            rw [leftContraWheel, HasLeftIhom.contramapEval f, w.wheelNatInA f (leval A), hwheelA]
          )
  left_inv turn := by
    unfold wheelToTurn turnToWheel₁ turnToWheel₂ wheelToTurn₁ wheelToTurn₂
    simp
  right_inv wheel := by
    ext A B f
    show (HasRightIhom.homEquiv B).symm (HasLeftIhom.homEquiv B f ≫ wheelToTurn₁ C wheel A (𝟙 (leftDual A))) = wheel.wheel A B f
    set fromBtoLeftDualA := HasLeftIhom.homEquiv B f with hk
    set wheelA := wheel.wheel A (leftDual A) (leval A) with hwheelA
    set turnA := HasRightIhom.homEquiv (leftDual A) wheelA with hturnA
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

variable [p : PrepivotalCategory C]

/-- The connection between `turn`,`turnToWheel₁`, `leftName` and `reval` -/
lemma nameConnectedWithTurn (A B : C) (f : A ⊗ B ⟶ D.bot) :
  turnToWheel₁ C p.turn A B f =
  ((ρ_ B).inv ⊗ₘ 𝟙 A) ≫ ((𝟙 B ⊗ₘ (leftName (A ⊗ B) f)) ⊗ₘ 𝟙 A) ≫
  ((lev B A) ⊗ₘ 𝟙 A) ≫
  ((p.turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A := by
  simp
  slice_rhs 2 3 => rw [associator_inv_naturality_middle B (leftName (A ⊗ B) f) A]
  rw [Category.assoc, Category.assoc, Category.assoc]
  slice_rhs 1 2 => rw [triangle_assoc_comp_left_inv B A]
  rw [Category.assoc, Category.assoc, Category.assoc]
  have fact : (B ◁ leftName (A ⊗ B) f) ▷ A ≫ lev B A ▷ A = (B ◁ leftName (A ⊗ B) f ≫ lev B A) ▷ A := by simp
  slice_rhs 2 3 => rw [fact]
  unfold lev
  rw [← HasLeftIhom.homEquivNaturalityₗ]
  have fact'' : (𝟙 A ⊗ₘ B ◁ leftName (A ⊗ B) f) ≫ (α_ A B (leftDual (A ⊗ B))).inv
    = (α_ A B (𝟙_ C)).inv ≫ (𝟙 (A ⊗ B) ⊗ₘ leftName (A ⊗ B) f) := by simp
  slice_rhs 2 3 =>
    rw [← Category.assoc, fact'', Category.assoc, leftNameUncurry (A ⊗ B) f]
    rw [← Category.assoc, ← whiskerLeft_rightUnitor]
  have idWhisker : A ◁ (ρ_ B).hom = 𝟙 A ⊗ₘ (ρ_ B).hom := by simp
  slice_rhs 2 3 => rw [idWhisker, HasLeftIhom.homEquivNaturalityₗ]
  simp; unfold reval;
  rw [← Category.assoc, ← comp_whiskerRight ((HasLeftIhom.homEquiv B) f) (PrepivotalCategory.turn.turn A).hom A, HasRightIhom.symm_apply_eq]
  simp

lemma wheel_via_turn_evals (A : C) :
  turnToWheel₁ C p.turn A (leftDual A) (leval A) =
  ((p.turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A := by
  show (HasRightIhom.homEquiv (leftDual A)).symm (HasLeftIhom.homEquiv (leftDual A) (leval A) ≫ (p.turn.turn A).hom) =
    ((p.turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A
  have hcurry : HasLeftIhom.homEquiv (leftDual A) (leval A) = 𝟙 (leftDual A) := Equiv.apply_symm_apply _ _
  rw [hcurry, Category.id_comp, HasRightIhom.symm_apply_eq]
  simp; rfl

/-- TODO: Paul-André's formulation from the draft of the lemma is incomplete as it uses undeclared entities. -/
lemma wheel_reval_lemma (A : C) :
  turnToWheel₁ C p.turn (rightDual A) A (reval A) = sorry := by
  sorry

end DialogueCategory
