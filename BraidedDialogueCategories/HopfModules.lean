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

/-- The action of `H` on `V ⊗ W`. -/
instance tensorModObj (V W : C) [ModObj H V] [ModObj H W] : ModObj H (V ⊗ W) where
  smul := Δ[H] ▷ (V ⊗ W) ≫ tensorμ H H V W ≫ (γ[H, V] ⊗ₘ γ[H, W])
  one_smul := sorry
  mul_smul := sorry

/-- The action of `H` on the unit. -/
instance unitModObj : ModObj H (𝟙_ C) where
  smul := ε[H] ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom
  one_smul := sorry
  mul_smul := sorry

/-- An isomorphism of `C` between modules which is a module map is an isomorphism in `Mod C H`. -/
def isoOfIso {V W : Mod C H} (e : V.X ≅ W.X) (he : IsModHom H e.hom) : V ≅ W where
  hom := ⟨e.hom⟩
  inv :=
    letI := he
    ⟨e.inv⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

instance monoidalStruct : MonoidalCategoryStruct (Mod C H) where
  tensorObj V W := ⟨V.X ⊗ W.X⟩
  whiskerLeft V _ _ g := Hom.mk' (V.X ◁ g.hom) sorry
  whiskerRight f W := Hom.mk' (f.hom ▷ W.X) sorry
  tensorUnit := ⟨𝟙_ C⟩
  associator U V W := isoOfIso H (α_ U.X V.X W.X) sorry
  leftUnitor V := isoOfIso H (λ_ V.X) sorry
  rightUnitor V := isoOfIso H (ρ_ V.X) sorry

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
@[simp] lemma associator_hom_hom (U V W : Mod C H) :
    (α_ U V W).hom.hom = (α_ U.X V.X W.X).hom := rfl
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
