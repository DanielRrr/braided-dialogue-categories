module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import BraidedDialogueCategories.InternalHoms

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory ComonObj MonObj BraidedCategory HopfObj

/-- A tensorial pole with right negations, on a merely monoidal category. -/
class RightDialogueStructure (C : Type v) [Category.{v} C] [MonoidalCategory C] where
  bot : C
  [rightClosed : RightClosedAt bot]

/-- A right dialogue category: a braided category with a right dialogue structure. -/
class RightDialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] extends RightDialogueStructure C

variable (C : Type v) [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

instance [D : RightDialogueCategory C] : RightClosedAt D.bot where
  hasRightIhom := D.rightClosed.hasRightIhom

/-- Mathlib has the category `Mod C H` but no monoidal structure on it. -/
instance Mod.monoidal (H : C) [BimonObj H] : MonoidalCategory (Mod C H) := sorry

/-- `h ▷ ψ = (a ↦ h₁ ▷ ψ (S h₂ ▷ a))`, curried. -/
def Mod.rightIhomSmul (H : C) [HopfObj H] (A B : C) [ModObj H A] [ModObj H B]
    [HasRightIhom A B] :
    H ⊗ HasRightIhom.internalHomᵣ A B ⟶ HasRightIhom.internalHomᵣ A B :=
  HasRightIhom.homEquiv _ <|
    (Δ[H] ▷ _) ▷ A ≫ (α_ H H _).hom ▷ A ≫ (H ◁ (β_ H _).hom) ▷ A ≫ (α_ H _ H).inv ▷ A ≫
      (α_ (H ⊗ _) H A).hom ≫ (H ⊗ _) ◁ (𝒮[H] ▷ A ≫ γ[H, A]) ≫ (α_ H _ A).hom ≫
      H ◁ HasRightIhom.evalRight ≫ γ[H, B]

instance Mod.rightIhomModObj (H : C) [HopfObj H] (A B : C) [ModObj H A] [ModObj H B]
    [HasRightIhom A B] : ModObj H (HasRightIhom.internalHomᵣ A B) where
  smul := Mod.rightIhomSmul H A B
  one_smul := sorry
  mul_smul := sorry

/--
Suppose that `H` a Hopf algebra in a braided category `C` and that (bot, )
is a left `H`-module. Then, every right dialogue structure with tensorial pole `bot` on the
braided category C induces a right dialogue structure with tensorial pole `(bot, )` on the
monoidal category `Mod(H)`.
-/
def Mod.rightDialogueStructure (H : C) [HopfObj H] [D : RightDialogueCategory C]
    [ModObj H D.bot] : RightDialogueStructure (Mod C H) where
  bot := ⟨D.bot⟩
  rightClosed :=
    { hasRightIhom A :=
        letI := D.rightClosed
        { internalHomᵣ := ⟨HasRightIhom.internalHomᵣ A.X D.bot⟩
          homEquiv X :=
            { toFun f := Mod.Hom.mk' (HasRightIhom.homEquiv X.X f.hom) sorry
              invFun g := Mod.Hom.mk' ((HasRightIhom.homEquiv X.X).symm g.hom) sorry
              left_inv f := by ext; simp
              right_inv g := by ext; simp }
          homEquivNaturalityᵣ f g := by
            ext; exact HasRightIhom.homEquivNaturalityᵣ f.hom g.hom } }
