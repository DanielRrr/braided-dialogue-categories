module

public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import BraidedDialogueCategories.InternalHoms
public import BraidedDialogueCategories.HopfModules

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory ComonObj MonObj BraidedCategory HopfObj

/-- A tensorial pole with left negations, on a merely monoidal category. -/
class LeftDialogueStructure (C : Type v) [Category.{v} C] [MonoidalCategory C] where
  bot : C
  [leftClosed : LeftClosedAt bot]

/-- A right dialogue category: a braided category with a right dialogue structure. -/
class LeftDialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] extends LeftDialogueStructure C


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
  smul := Mod.rightIhomSmul C H A B
  one_smul := sorry
  mul_smul := sorry

/-- The right internal hom `[A, B]ᵣ` in `Mod C H`, computed in `C`. -/
def Mod.hasRightIhom (H : C) [HopfObj H] (A B : Mod C H) [HasRightIhom A.X B.X] :
    HasRightIhom A B where
  internalHomᵣ := ⟨HasRightIhom.internalHomᵣ A.X B.X⟩
  homEquiv X :=
    { toFun f := Mod.Hom.mk' (HasRightIhom.homEquiv X.X f.hom) sorry
      invFun g := Mod.Hom.mk' ((HasRightIhom.homEquiv X.X).symm g.hom) sorry
      left_inv f := by ext; simp
      right_inv g := by ext; simp }
  homEquivNaturalityᵣ f g := by
    ext
    simpa using HasRightIhom.homEquivNaturalityᵣ f.hom g.hom

/--
Suppose that `H` a Hopf algebra in a braided category `C` and that `(bot, smul)`
is a left `H`-module. Then, every right dialogue structure with tensorial pole `bot` on the
braided category `C` induces a right dialogue structure with tensorial pole `(bot, smul)` on the
monoidal category `Mod(H)`.
-/
def Mod.rightDialogueStructure (H : C) [HopfObj H] [D : RightDialogueCategory C]
    [ModObj H D.bot] : RightDialogueStructure (Mod C H) where
  bot := ⟨D.bot⟩
  rightClosed :=
    letI := D.rightClosed
    { hasRightIhom A := Mod.hasRightIhom C H A ⟨D.bot⟩ }

/-- `h ⊗ v ⊗ f ↦ h₍₂₎ ▷ leval (S⁻¹ h₍₁₎ ▷ v, f)`. -/
noncomputable def Mod.leftIhomSmulRHS (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V] [ModObj H B]
    [HasLeftIhom V B] : (H ⊗ V) ⊗ HasLeftIhom.internalHomₗ V B ⟶ B :=
  (Δ[H] ▷ V) ▷ _ ≫ ((β_ H H).hom ▷ V) ▷ _ ≫ (α_ H H V).hom ▷ _ ≫
    (H ◁ (inv 𝒮[H] ▷ V ≫ γ[H, V])) ▷ _ ≫ (α_ H V _).hom ≫
    H ◁ HasLeftIhom.leftEval ≫ γ[H, B]

/-- The action of `H` on `V ⊸ ⊥`: the unique morphism satisfying the pictured equation. -/
noncomputable def Mod.leftIhomSmul (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V] [ModObj H B]
    [HasLeftIhom V B] :
    H ⊗ HasLeftIhom.internalHomₗ V B ⟶ HasLeftIhom.internalHomₗ V B :=
  HasLeftIhom.homEquiv _ <|
    (α_ V H _).inv ≫ (β_ H V).inv ▷ _ ≫ Mod.leftIhomSmulRHS C H V B

/-- The pictured equation. -/
lemma Mod.leftIhomSmul_spec (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V]
    [ModObj H B] [HasLeftIhom V B] :
    (β_ H V).hom ▷ _ ≫ (α_ V H _).hom ≫ V ◁ Mod.leftIhomSmul C H V B ≫ HasLeftIhom.leftEval =
      Mod.leftIhomSmulRHS C H V B := by
  rw [Mod.leftIhomSmul, ← id_tensorHom, HasLeftIhom.uncurry_curry]
  simp

noncomputable instance Mod.leftIhomModObj (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V]
    [ModObj H B] [HasLeftIhom V B] : ModObj H (HasLeftIhom.internalHomₗ V B) where
  smul := Mod.leftIhomSmul C H V B
  one_smul := sorry
  mul_smul := sorry

noncomputable def Mod.hasLeftIhom (H : C) [HopfObj H] [IsIso 𝒮[H]] (A B : Mod C H) [HasLeftIhom A.X B.X] :
    HasLeftIhom A B where
  internalHomₗ := ⟨HasLeftIhom.internalHomₗ A.X B.X⟩
  homEquiv X :=
    { toFun f := Mod.Hom.mk' (HasLeftIhom.homEquiv X.X f.hom) sorry
      invFun g := Mod.Hom.mk' ((HasLeftIhom.homEquiv X.X).symm g.hom) sorry
      left_inv f := by ext; simp
      right_inv g := by ext; simp }
  homEquivNaturalityₗ f g := by
    ext
    simpa using HasLeftIhom.homEquivNaturalityₗ f.hom g.hom

/-- Suppose that `H` is a Hopf algebra with an invertible antipode `S` in a
braided category `C` and that `(bot, smul)` is a left `H`-module. Then, every left dialogue structure
with tensorial pole `bot` on the braided category `C` induces a left dialogue structure with
tensorial pole `(bot, inv)` on the monoidal category `Mod(H)`. -/
noncomputable def Mod.leftDialogueStructure (H : C) [HopfObj H] [IsIso 𝒮[H]] [D : LeftDialogueCategory C]
    [ModObj H D.bot] : LeftDialogueStructure (Mod C H) where
  bot := ⟨D.bot⟩
  leftClosed :=
    letI := D.leftClosed
    { hasLeftIhom A := Mod.hasLeftIhom C H A ⟨D.bot⟩ }
