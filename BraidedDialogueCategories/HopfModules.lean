module

public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
Mathlib has the category `Mod C H` of left `H`-modules but no monoidal structure on it.
This file provides it.

* `H` acts on `V ⊗ W` through `Δ` followed by the braiding (`tensorμ`);
* `H` acts on the unit `𝟙_ C` through the counit `ε`.
-/

@[expose] public section

universe v

namespace CategoryTheory
open MonoidalCategory MonObj ComonObj

variable {C : Type v} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

namespace Mod

variable (H : C) [BimonObj H]

/-- The action of `H` on `V ⊗ W`: if `H` acts on `V` and `W`, where `V` and `W` are
from a monoidal category `C`, then `H` acts on `V ⊗ W`. -/
instance tensorModObj (V W : C) [ModObj H V] [ModObj H W] : ModObj H (V ⊗ W) where
  smul := Δ[H] ▷ (V ⊗ W) ≫ tensorμ H H V W ≫ (γ[H, V] ⊗ₘ γ[H, W])
  one_smul := by
    dsimp
    rw [← comp_whiskerRight_assoc, BimonObj.one_comul, MonObj.tensorObj.one_def,
          comp_whiskerRight_assoc, tensorμ_natural_left_assoc, tensorHom_comp_tensorHom]
    have hV := ModObj.one_smul (M := H) V
    have hW := ModObj.one_smul (M := H) W
    dsimp at hV hW
    rw [hV, hW, tensor_left_unitality]
  mul_smul := by
    dsimp
    have hV := ModObj.mul_smul (M := H) V
    have hW := ModObj.mul_smul (M := H) W
    dsimp at hV hW
    -- Stage 1: open up `μ ≫ Δ` and use the module axioms of `V` and `W`
    rw [← comp_whiskerRight_assoc, BimonObj.mul_comul, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, tensorμ_natural_left_assoc, tensorHom_comp_tensorHom, hV, hW,
    ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, tensor_associativity_assoc, ← tensorμ_natural_right_assoc]
    -- Stage 2: group the inner action
    rw [tensorHom_def, comp_whiskerRight_assoc, associator_naturality_middle_assoc,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    -- Stage 3: match the right-hand side
    rw [associator_naturality_left_assoc, whisker_exchange_assoc, Category.assoc]

/-- The action of `H` on the unit. -/
instance unitModObj : ModObj H (𝟙_ C) where
  smul := ε[H] ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom
  one_smul := by
    dsimp
    rw [← comp_whiskerRight_assoc, BimonObj.one_counit, id_whiskerRight, Category.id_comp]
  mul_smul := by
    dsimp
    rw [← comp_whiskerRight_assoc, BimonObj.mul_counit, Comon.tensorObj_counit, tensorHom_def']
    monoidal

/-- An isomorphism of `C` between modules which is a module map is an isomorphism in `Mod C H`. -/
def isoOfIso {V W : Mod C H} (e : V.X ≅ W.X) (he : IsModHom H e.hom) : V ≅ W where
  hom := ⟨e.hom⟩
  inv := letI := he; ⟨e.inv⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp] lemma tensorModObj_smul (V W : C) [ModObj H V] [ModObj H W] :
    γ[H, V ⊗ W] = Δ[H] ▷ (V ⊗ W) ≫ tensorμ H H V W ≫ (γ[H, V] ⊗ₘ γ[H, W]) := rfl

@[simp]
lemma unitModObj_smul : γ[H, 𝟙_ C] = ε[H] ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom := rfl

/-- `Mod C H` has a structure of a monoidal category. -/
instance monoidalStruct : MonoidalCategoryStruct (Mod C H) where
  tensorObj V W := ⟨V.X ⊗ W.X⟩
  whiskerLeft V A B g := Hom.mk' (V.X ◁ g.hom) (by
    have hg := g.isModHom.smul_hom
    dsimp at hg ⊢
    rw [whisker_exchange_assoc]
    have h := tensorμ_natural_right H H (𝟙 V.X) g.hom
    simp only [id_tensorHom, MonoidalCategory.whiskerLeft_id] at h
    rw [reassoc_of% h]
    simp only [Category.assoc, tensorHom_def, ← MonoidalCategory.whiskerLeft_comp, hg]
    rw [whisker_exchange_assoc, MonoidalCategory.whiskerLeft_comp]
  )
  whiskerRight f W := Hom.mk' (f.hom ▷ W.X) (by
    have hf := f.isModHom.smul_hom
    dsimp at hf ⊢
    rw [whisker_exchange_assoc]
    have h := tensorμ_natural_right H H f.hom (𝟙 W.X)
    simp only [tensorHom_id, MonoidalCategory.whiskerLeft_id] at h
    rw [reassoc_of% h]
    simp only [Category.assoc, tensorHom_def]
    rw [whisker_exchange, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, hf]
  )
  tensorUnit := ⟨𝟙_ C⟩
  associator U V W := isoOfIso H (α_ U.X V.X W.X) (by
    constructor
    dsimp
    rw [← whiskerRight_comp_tensorHom, ← whiskerRight_comp_tensorHom,
        ← whiskerLeft_comp_tensorHom, ← whiskerLeft_comp_tensorHom]
    have h1 := tensorμ_natural_left Δ[H] (𝟙 H) (U.X ⊗ V.X) W.X
    have h2 := tensorμ_natural_left (𝟙 H) Δ[H] U.X (V.X ⊗ W.X)
    simp only [tensorHom_id, id_tensorHom, id_whiskerRight] at h1 h2
    rw [Category.assoc, ← reassoc_of% h1, ← reassoc_of% h2]
    -- move the associator of the modules to the front, then use `associator_monoidal`
    rw [Category.assoc, Category.assoc, Category.assoc, associator_naturality,
      associator_monoidal_assoc]
    -- coassociativity, then move the module associator to the front
    rw [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      ← comp_whiskerRight_assoc, Category.assoc, ← ComonObj.comul_assoc, ← whisker_exchange_assoc]
  )
  leftUnitor V := isoOfIso H (λ_ V.X) (by
    constructor
    dsimp
    rw [← whiskerRight_comp_tensorHom]
    have h := tensorμ_natural_left ε[H] (𝟙 H) (𝟙_ C) V.X
    simp only [tensorHom_id, id_whiskerRight] at h
    rw [Category.assoc, ← reassoc_of% h]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, ComonObj.counit_comul]
    -- the action of the unit factor is trivial
    rw [tensorHom_def, Category.assoc, leftUnitor_naturality, ← leftUnitor_monoidal_assoc]
    -- cancel `λ_ H` against its inverse
    rw [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  )
  rightUnitor V := isoOfIso H (ρ_ V.X) (by
    constructor
    dsimp
    rw [← whiskerLeft_comp_tensorHom]
    have h := tensorμ_natural_left (𝟙 H) ε[H] V.X (𝟙_ C)
    simp only [id_tensorHom, id_whiskerRight] at h
    rw [Category.assoc, ← reassoc_of% h]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, ComonObj.comul_counit]
    rw [tensorHom_def', Category.assoc, rightUnitor_naturality, ← rightUnitor_monoidal_assoc,
      tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  )

section simpLemmas

variable {H}

@[simp] lemma tensorObj_X (V W : Mod C H) : (V ⊗ W).X = V.X ⊗ W.X := rfl

@[simp] lemma tensorUnit_X : (𝟙_ (Mod C H)).X = 𝟙_ C := rfl

@[simp] lemma whiskerLeft_hom (V : Mod C H) {W₁ W₂ : Mod C H} (g : W₁ ⟶ W₂) :
    (V ◁ g).hom = V.X ◁ g.hom := rfl

@[simp] lemma whiskerRight_hom {V₁ V₂ : Mod C H} (f : V₁ ⟶ V₂) (W : Mod C H) :
    (f ▷ W).hom = f.hom ▷ W.X := rfl

@[simp] lemma tensorHom_hom {V₁ V₂ W₁ W₂ : Mod C H} (f : V₁ ⟶ V₂) (g : W₁ ⟶ W₂) :
    (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom := by
  simp [MonoidalCategoryStruct.tensorHom, tensorHom_def]

@[simp] lemma associator_hom_hom (U V W : Mod C H) : (α_ U V W).hom.hom = (α_ U.X V.X W.X).hom := rfl

@[simp] lemma associator_inv_hom (U V W : Mod C H) :
    (α_ U V W).inv.hom = (α_ U.X V.X W.X).inv := rfl

@[simp] lemma leftUnitor_hom_hom (V : Mod C H) : (λ_ V).hom.hom = (λ_ V.X).hom := rfl

@[simp] lemma leftUnitor_inv_hom (V : Mod C H) : (λ_ V).inv.hom = (λ_ V.X).inv := rfl

@[simp] lemma rightUnitor_hom_hom (V : Mod C H) : (ρ_ V).hom.hom = (ρ_ V.X).hom := rfl

@[simp] lemma rightUnitor_inv_hom (V : Mod C H) : (ρ_ V).inv.hom = (ρ_ V.X).inv := rfl

end simpLemmas

instance : (forget (D := C) H).Faithful where
  map_injective h := Hom.ext h

/-- `Mod C H` is monoidal; the axioms are inherited from `C` along the faithful
forgetful functor. -/
instance monoidal : MonoidalCategory (Mod C H) :=
  Monoidal.induced (forget (D := C) H)
    { μIso _ _ := Iso.refl _
      whiskerLeft_eq _ _ _ _ := by dsimp [forget]; simp
      whiskerRight_eq _ _ := by dsimp [forget]; simp
      tensorHom_eq _ _ := by dsimp [forget]; simp
      εIso := Iso.refl _
      associator_eq _ _ _ := by dsimp [forget]; simp
      leftUnitor_eq _ := by dsimp [forget]; simp
      rightUnitor_eq _ := by dsimp [forget]; simp }

end Mod

end CategoryTheory
