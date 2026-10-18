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

/-- The first half of the action on `[A, B]ᵣ`: split `h`, let `h₂` cross `y`, and act with
`S(h₂)` on `a`. In elements: `h ⊗ y ⊗ a ↦ h₁ ⊗ (y ⊗ S(h₂) ▷ a)`. -/
def Mod.rightIhomPre (H : C) [HopfObj H] (A : C) [ModObj H A] (Y : C) :
    (H ⊗ Y) ⊗ A ⟶ H ⊗ (Y ⊗ A) :=
  (Δ[H] ▷ Y) ▷ A ≫ (α_ H H Y).hom ▷ A ≫ (H ◁ (β_ H Y).hom) ▷ A ≫ (α_ H Y H).inv ▷ A ≫
    (α_ (H ⊗ Y) H A).hom ≫ (H ⊗ Y) ◁ (𝒮[H] ▷ A ≫ γ[H, A]) ≫ (α_ H Y A).hom

/-- `h ▷ ψ = (a ↦ h₁ ▷ ψ (S h₂ ▷ a))`, curried. -/
def Mod.rightIhomSmul (H : C) [HopfObj H] (A B : C) [ModObj H A] [ModObj H B]
    [HasRightIhom A B] :
    H ⊗ HasRightIhom.internalHomᵣ A B ⟶ HasRightIhom.internalHomᵣ A B :=
  HasRightIhom.homEquiv (H ⊗ HasRightIhom.internalHomᵣ A B)
    (Mod.rightIhomPre C H A (HasRightIhom.internalHomᵣ A B) ≫
      H ◁ HasRightIhom.evalRight ≫ γ[H, B])

/-- In any `H`-module, acting with h₂ and then with S(h₁) does the same as multiplying by the scalar ε(h). -/
lemma Mod.antipode_comul_smul (H : C) [HopfObj H] (A : C) (aA : H ⊗ A ⟶ A)
    (h_mul : H ◁ aA ≫ aA = (α_ H H A).inv ≫ μ[H] ▷ A ≫ aA)
    (h_one : η[H] ▷ A ≫ aA = (λ_ A).hom) :
    Δ[H] ▷ A ⊗≫ H ◁ aA ⊗≫ (𝒮[H] ▷ A ≫ aA) = ε[H] ▷ A ≫ (λ_ A).hom := by calc
    _ = 𝟙 _ ⊗≫ Δ[H] ▷ A ⊗≫ (H ◁ aA ≫ 𝒮[H] ▷ A) ≫ aA := by monoidal
    _ = 𝟙 _ ⊗≫ (Δ[H] ≫ 𝒮[H] ▷ H) ▷ A ⊗≫ (H ◁ aA ≫ aA) := by rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (Δ[H] ≫ 𝒮[H] ▷ H ≫ μ[H]) ▷ A ≫ aA := by rw [h_mul]; monoidal
    _ = 𝟙 _ ⊗≫ ε[H] ▷ A ⊗≫ η[H] ▷ A ≫ aA := by rw [HopfObj.antipode_left]; monoidal
    _ = _ := by rw [h_one]; monoidal

lemma Mod.comul_antipode_smul (H : C) [HopfObj H] (A : C) (aA : H ⊗ A ⟶ A)
    (h_mul : H ◁ aA ≫ aA = (α_ H H A).inv ≫ μ[H] ▷ A ≫ aA)
    (h_one : η[H] ▷ A ≫ aA = (λ_ A).hom) :
    Δ[H] ▷ A ⊗≫ H ◁ (𝒮[H] ▷ A ≫ aA) ⊗≫ aA = ε[H] ▷ A ≫ (λ_ A).hom := by
  calc _ = 𝟙 _ ⊗≫ (Δ[H] ≫ H ◁ 𝒮[H]) ▷ A ⊗≫ (H ◁ aA ≫ aA) := by monoidal
    _ = 𝟙 _ ⊗≫ (Δ[H] ≫ H ◁ 𝒮[H] ≫ μ[H]) ▷ A ≫ aA := by rw [h_mul]; monoidal
    _ = 𝟙 _ ⊗≫ ε[H] ▷ A ⊗≫ η[H] ▷ A ≫ aA := by rw [HopfObj.antipode_right]; monoidal
    _ = _ := by rw [h_one]; monoidal

lemma Mod.rightIhomPre_smul_aux (H : C) [HopfObj H] (X A : C) (aX : H ⊗ X ⟶ X)
    (aA : H ⊗ A ⟶ A)
    (h_mul : H ◁ aA ≫ aA = (α_ H H A).inv ≫ μ[H] ▷ A ≫ aA)
    (h_one : η[H] ▷ A ≫ aA = (λ_ A).hom) :
    ((Δ[H] ▷ X) ▷ A ≫ (α_ H H X).hom ▷ A ≫ (H ◁ (β_ H X).hom) ▷ A ≫ (α_ H X H).inv ▷ A ≫
      (α_ (H ⊗ X) H A).hom ≫ (H ⊗ X) ◁ (𝒮[H] ▷ A ≫ aA) ≫ (α_ H X A).hom) ≫
      Δ[H] ▷ (X ⊗ A) ≫ tensorμ H H X A ≫ (aX ⊗ₘ aA) = aX ▷ A := by
  calc _ = 𝟙 _ ⊗≫ Δ[H] ▷ X ▷ A ⊗≫
        (H ◁ ((β_ H X).hom ▷ A ⊗≫ X ◁ (𝒮[H] ▷ A ≫ aA)) ≫ Δ[H] ▷ (X ⊗ A)) ⊗≫
        H ◁ (β_ H X).hom ▷ A ⊗≫ aX ▷ H ▷ A ⊗≫ X ◁ aA := by
        simp only [tensorμ, tensorHom_def]
        monoidal
    _ = 𝟙 _ ⊗≫ (Δ[H] ≫ Δ[H] ▷ H ≫ (α_ H H H).hom) ▷ X ▷ A ⊗≫
        H ◁ H ◁ (β_ H X).hom ▷ A ⊗≫
        H ◁ ((H ⊗ X) ◁ (𝒮[H] ▷ A ≫ aA) ≫ (β_ H X).hom ▷ A) ⊗≫
        aX ▷ H ▷ A ⊗≫ X ◁ aA := by
        conv_lhs => rw [whisker_exchange]
        monoidal
    _ = 𝟙 _ ⊗≫ Δ[H] ▷ X ▷ A ⊗≫ H ◁ ((Δ[H] ▷ X ≫ (β_ (H ⊗ H) X).hom) ▷ A) ⊗≫
        H ◁ X ◁ H ◁ (𝒮[H] ▷ A ≫ aA) ⊗≫ aX ▷ H ▷ A ⊗≫ X ◁ aA := by
        rw [← ComonObj.comul_assoc, whisker_exchange, braiding_tensor_left_hom]
        monoidal
    _ = 𝟙 _ ⊗≫ Δ[H] ▷ X ▷ A ⊗≫ H ◁ (β_ H X).hom ▷ A ⊗≫ H ◁ X ◁ Δ[H] ▷ A ⊗≫
        H ◁ X ◁ H ◁ (𝒮[H] ▷ A ≫ aA) ⊗≫ (aX ▷ (H ⊗ A) ≫ X ◁ aA) := by
        rw [BraidedCategory.braiding_naturality_left]
        monoidal
    _ = 𝟙 _ ⊗≫ Δ[H] ▷ X ▷ A ⊗≫ H ◁ (β_ H X).hom ▷ A ⊗≫
        H ◁ X ◁ (Δ[H] ▷ A ⊗≫ H ◁ (𝒮[H] ▷ A ≫ aA) ⊗≫ aA) ⊗≫ aX ▷ A := by
        rw [← whisker_exchange]
        monoidal
    _ = 𝟙 _ ⊗≫ Δ[H] ▷ X ▷ A ⊗≫ H ◁ (((β_ H X).hom ≫ X ◁ ε[H]) ▷ A) ⊗≫ aX ▷ A := by
        rw [Mod.comul_antipode_smul C H A aA h_mul h_one]
        monoidal
    _ = 𝟙 _ ⊗≫ (Δ[H] ≫ H ◁ ε[H]) ▷ X ▷ A ⊗≫ aX ▷ A := by
        rw [← BraidedCategory.braiding_naturality_left, braiding_tensorUnit_left]
        monoidal
    _ = _ := by
        rw [ComonObj.comul_counit]
        monoidal

lemma Mod.unit_rightIhomPre_aux (H : C) [HopfObj H] (Y A : C) (aA : H ⊗ A ⟶ A)
    (h_one : η[H] ▷ A ≫ aA = (λ_ A).hom) :
    (η[H] ▷ Y) ▷ A ≫
      ((Δ[H] ▷ Y) ▷ A ≫ (α_ H H Y).hom ▷ A ≫ (H ◁ (β_ H Y).hom) ▷ A ≫ (α_ H Y H).inv ▷ A ≫
        (α_ (H ⊗ Y) H A).hom ≫ (H ⊗ Y) ◁ (𝒮[H] ▷ A ≫ aA) ≫ (α_ H Y A).hom) =
      (α_ (𝟙_ C) Y A).hom ≫ η[H] ▷ (Y ⊗ A) := by
  calc _ = 𝟙 _ ⊗≫ (η[H] ≫ Δ[H]) ▷ Y ▷ A ⊗≫ H ◁ (β_ H Y).hom ▷ A ⊗≫
        H ◁ Y ◁ (𝒮[H] ▷ A ≫ aA) := by
        monoidal
    _ = 𝟙 _ ⊗≫ η[H] ▷ Y ▷ A ⊗≫ H ◁ ((η[H] ▷ Y ≫ (β_ H Y).hom) ▷ A) ⊗≫
        H ◁ Y ◁ (𝒮[H] ▷ A ≫ aA) := by
        rw [Bimon.one_comul, tensorHom_def]
        monoidal
    _ = 𝟙 _ ⊗≫ η[H] ▷ Y ▷ A ⊗≫ H ◁ Y ◁ ((η[H] ≫ 𝒮[H]) ▷ A ≫ aA) := by
        rw [BraidedCategory.braiding_naturality_left, braiding_tensorUnit_left]
        monoidal
    _ = 𝟙 _ ⊗≫ η[H] ▷ Y ▷ A ⊗≫ H ◁ Y ◁ (λ_ A).hom := by
        rw [HopfObj.one_antipode, h_one]
    _ = _ := by
        monoidal

@[reassoc]
lemma Mod.unit_rightIhomPre (H : C) [HopfObj H] (Y A : C) [ModObj H A] :
    (η[H] ▷ Y) ▷ A ≫ Mod.rightIhomPre C H A Y = (α_ (𝟙_ C) Y A).hom ≫ η[H] ▷ (Y ⊗ A) :=
  Mod.unit_rightIhomPre_aux C H Y A γ[H, A]
    (by have h := ModObj.one_smul (M := H) A; dsimp at h; exact h)

instance Mod.rightIhomModObj (H : C) [HopfObj H] (A B : C) [ModObj H A] [ModObj H B]
    [HasRightIhom A B] : ModObj H (HasRightIhom.internalHomᵣ A B) where
  smul := Mod.rightIhomSmul C H A B
  one_smul := by
    have hB := ModObj.one_smul (M := H) B
    dsimp at hB ⊢
    apply HasRightIhom.right_hom_ext
    rw [comp_whiskerRight_assoc, Mod.rightIhomSmul, HasRightIhom.homEquiv_whiskerRight_evalRight,
      Mod.unit_rightIhomPre_assoc, ← whisker_exchange_assoc, hB, leftUnitor_naturality,
      leftUnitor_whiskerRight_assoc]
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
  (Δ[H] ▷ V) ▷ HasLeftIhom.internalHomₗ V B ≫ ((β_ H H).hom ▷ V) ▷ HasLeftIhom.internalHomₗ V B ≫
  (α_ H H V).hom ▷ HasLeftIhom.internalHomₗ V B ≫
  (H ◁ (inv 𝒮[H] ▷ V ≫ γ[H, V])) ▷ HasLeftIhom.internalHomₗ V B ≫
  (α_ H V (HasLeftIhom.internalHomₗ V B)).hom ≫ H ◁ HasLeftIhom.leftEval ≫ γ[H, B]

/-- The action of `H` on `leftDual V`. -/
noncomputable def Mod.leftIhomSmul (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V] [ModObj H B]
  [HasLeftIhom V B] : H ⊗ HasLeftIhom.internalHomₗ V B ⟶ HasLeftIhom.internalHomₗ V B :=
  HasLeftIhom.homEquiv (H ⊗ HasLeftIhom.internalHomₗ V B)
    ((α_ V H (HasLeftIhom.internalHomₗ V B)).inv ≫ (β_ H V).inv ▷ HasLeftIhom.internalHomₗ V B ≫ Mod.leftIhomSmulRHS C H V B)

lemma Mod.leftIhomSmul_spec (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V]
    [ModObj H B] [HasLeftIhom V B] :
    (β_ H V).hom ▷ HasLeftIhom.internalHomₗ V B ≫ (α_ V H (HasLeftIhom.internalHomₗ V B)).hom ≫
      V ◁ Mod.leftIhomSmul C H V B ≫ HasLeftIhom.leftEval = Mod.leftIhomSmulRHS C H V B := by
  rw [Mod.leftIhomSmul, ← id_tensorHom, HasLeftIhom.uncurry_curry]
  simp

noncomputable instance Mod.leftIhomModObj (H : C) [HopfObj H] [IsIso 𝒮[H]] (V B : C) [ModObj H V]
    [ModObj H B] [HasLeftIhom V B] : ModObj H (HasLeftIhom.internalHomₗ V B) where
  smul := Mod.leftIhomSmul C H V B
  one_smul := sorry
  mul_smul := sorry

@[instance_reducible] noncomputable def Mod.hasLeftIhom (H : C) [HopfObj H] [IsIso 𝒮[H]] (A B : Mod C H) [HasLeftIhom A.X B.X] :
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
@[instance_reducible] noncomputable def Mod.leftDialogueStructure (H : C) [HopfObj H] [IsIso 𝒮[H]] [D : LeftDialogueCategory C]
    [ModObj H D.bot] : LeftDialogueStructure (Mod C H) where
  bot := ⟨D.bot⟩
  leftClosed :=
    letI := D.leftClosed
    { hasLeftIhom A := Mod.hasLeftIhom C H A ⟨D.bot⟩ }
