module

public import Mathlib.CategoryTheory.Monoidal.Category
public import BraidedDialogueCategories.DialogueCategories

namespace CategoryTheory
open MonoidalCategory
open DialogueCategory

class PivotalDialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C] [D : DialogueCategory C] where
    pivotalTurn : Wheel C
    pivotalCoherence : ∀ X Y Z : C,
      (pivotalTurn.wheel X (Y ⊗ Z)).trans (CategoryTheory.Iso.homFromEquiv (C := C) (associator Y Z X) (Z := D.bot).trans (pivotalTurn.wheel Y (Z ⊗ X))) =
      CategoryTheory.Iso.homFromEquiv (C := C) ((associator X Y Z).symm) (Z := D.bot).trans
        ((pivotalTurn.wheel (X ⊗ Y) Z).trans (CategoryTheory.Iso.homFromEquiv (C := C) ((associator Z X Y).symm) (Z := D.bot)))

namespace DialogueCategory

variable (C : Type v) [Category.{v} C] [MonoidalCategory C] [D : DialogueCategory C]

open DialogueCategory in
def turnToPivots (A B : C)
  (turn : Turn C)
  (turnEval : ((lev B A ⊗ₘ 𝟙 A) ≫ ((turn.turn A).hom ⊗ₘ 𝟙 A) ≫ reval A) =
  (associator B (leftDual (A ⊗ B)) A).hom ≫
    (𝟙 B ⊗ₘ ((turn.turn (A ⊗ B)).hom) ⊗ₘ 𝟙 A) ≫ (𝟙 B ⊗ₘ rev A B) ≫ (𝟙 B ⊗ₘ (turn.turn B).inv) ≫ leval B)
  : PivotalDialogueCategory C where
  pivotalTurn := TurnEquivWheel C turn
  pivotalCoherence X Y Z := by sorry

end DialogueCategory
