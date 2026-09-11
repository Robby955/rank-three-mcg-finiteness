import Normalizer.OpenSheafCohomology
import Normalizer.AffineH1Vanishing
import Normalizer.ClosedPushforwardCohomology
import Normalizer.ModuleAbelianPushforward
import Normalizer.ModuleSheafCohomologyScalars

/-! Cohomology of actual scheme-module restrictions and affine open vanishing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u

/-- Forgetting scalars commutes with restriction to the actual open subscheme. -/
def schemeOpenAbelianRestrictionIso {X : Scheme.{u}} (U : X.Opens) :
    schemeModulesToAbelianSheaves X ⋙ U.sheafRestrict ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ schemeModulesToAbelianSheaves U.toScheme :=
  Iso.refl _

/-- Actual cohomology of a module sheaf on an ambient open equals cohomology
of its actual restriction to the open subscheme. -/
def schemeOpenCohomologyEquiv {X : Scheme.{u}} (U : X.Opens) (F : X.Modules) (n : ℕ) :
    ((schemeModulesToAbelianSheaves X).obj F).H' n U ≃+
      Sheaf.H ((schemeModulesToAbelianSheaves U.toScheme).obj (F.restrict U.ι)) n :=
  (openSheafCohomologyEquiv U ((schemeModulesToAbelianSheaves X).obj F) n).trans
    (((Sheaf.functorH _ n).mapIso ((schemeOpenAbelianRestrictionIso U).app F)).addCommGroupIsoToAddEquiv)

/-- Forgetting the restricted module changes none of the underlying
abelian cohomology classes in the open comparison. -/
theorem schemeOpenCohomologyEquiv_apply {X : Scheme.{u}} (U : X.Opens)
    (F : X.Modules) (n : ℕ) (x : ((schemeModulesToAbelianSheaves X).obj F).H' n U) :
    schemeOpenCohomologyEquiv U F n x =
      openSheafCohomologyEquiv U ((schemeModulesToAbelianSheaves X).obj F) n x :=
  Sheaf.H.map_id_apply _

/-- Restriction and direct image along a scheme isomorphism recover the
original actual module sheaf by the canonical adjunction unit. -/
theorem schemeIsoRestriction_unit_isIso {X Y : Scheme.{u}} (i : Y ⟶ X) [IsIso i]
    (F : X.Modules) : IsIso ((Scheme.Modules.restrictAdjunction i).unit.app F) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have heq : i ''ᵁ (i ⁻¹ᵁ U) = U := by
    apply SetLike.coe_injective
    exact @Set.image_preimage_eq _ _ i U.1 i.homeomorph.surjective
  have : IsIso (homOfLE (i.image_preimage_le U)) := by
    have h : homOfLE (i.image_preimage_le U) = (eqToIso heq).hom := Subsingleton.elim _ _
    rw [h]
    infer_instance
  infer_instance

/-- Actual cohomology of every quasicoherent module sheaf on an arbitrary
affine scheme vanishes in degree one, transported through its canonical
isomorphism to Spec of its global ring. -/
theorem quasicoherent_affine_H1_subsingleton {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] :
    Subsingleton (Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1) := by
  let i := X.isoSpec.inv
  have := schemeIsoRestriction_unit_isIso i F
  let e := (schemeModulesToAbelianSheaves X).mapIso
    (asIso ((Scheme.Modules.restrictAdjunction i).unit.app F))
  have hz := quasicoherent_Spec_H1_subsingleton (F.restrict i)
  let c := closedPushforwardCohomologyEquiv i.base
    (TopCat.homeoOfIso (asIso i.base)).isClosedEmbedding
    ((schemeModulesToAbelianSheaves _).obj (F.restrict i)) 1
  exact (((Sheaf.functorH _ 1).mapIso e).addCommGroupIsoToAddEquiv.trans c).injective.subsingleton

/-- First cohomology of an actual quasicoherent module sheaf on any affine
open of an ambient scheme is zero. This is ambient cohomology-presheaf
evaluation at U, with no supplied restriction or vanishing interface. -/
theorem quasicoherent_affineOpen_H1_subsingleton {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U) (F : X.Modules) [F.IsQuasicoherent] :
    Subsingleton (((schemeModulesToAbelianSheaves X).obj F).H' 1 U) := by
  have : IsAffine U.toScheme := hU
  have := quasicoherent_affine_H1_subsingleton (F.restrict U.ι)
  exact (schemeOpenCohomologyEquiv U F 1).injective.subsingleton

/-- Base constants on an actual open subscheme are the restrictions of the
ambient base constants to that same open. -/
theorem schemeConstantAt_open {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (V : U.toScheme.Opens) (a : k) :
    schemeConstantAt (U.ι ≫ p) V a = schemeConstantAt p (U.ι ''ᵁ V) a := by
  change X.presheaf.map _ (X.presheaf.map _ (schemeConstantMap p a)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Actual scalar multiplication commutes with the actual open restriction
functor. Both actions come from the specified scheme structure morphisms. -/
theorem schemeModuleScalarEnd_open {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) (a : k) :
    U.sheafRestrict.map (schemeModuleScalarEnd p F a) =
      schemeModuleScalarEnd (U.ι ≫ p) (F.restrict U.ι) a := by
  apply Sheaf.hom_ext
  ext V s
  change Γ(F, U.ι ''ᵁ V.unop) at s
  change schemeConstantAt p (U.ι ''ᵁ V.unop) a • s =
    (U.ι.appIso V.unop).inv (schemeConstantAt (U.ι ≫ p) V.unop a) • s
  rw [Scheme.Opens.ι_appIso, schemeConstantAt_open]
  rfl

/-- Scalars on ambient-open cohomology act through the actual scalar
endomorphism of the ambient sheaf. -/
@[instance_reducible]
def schemeModuleOpenCohomologyModule {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) (n : ℕ) :
    Module k (((schemeModulesToAbelianSheaves X).obj F).H' n U) where
  smul a x := x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F a)) (add_zero n)
  one_smul x := by
    change x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F 1)) (add_zero n) = x
    simp
  mul_smul a b x := by
    change x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F (a * b))) (add_zero n) =
      (x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F b)) (add_zero n)).comp
        (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F a)) (add_zero n)
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, map_mul]
    rfl
  smul_zero a := Abelian.Ext.zero_comp _ _ _ _ _
  smul_add a x y := Abelian.Ext.add_comp _ _ _ _
  add_smul a b x := by
    change x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F (a + b))) (add_zero n) =
      x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F a)) (add_zero n) +
        x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F b)) (add_zero n)
    rw [map_add, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]
  zero_smul x := by
    change x.comp (Abelian.Ext.mk₀ (schemeModuleScalarEnd p F 0)) (add_zero n) = 0
    simp

/-- The ambient-open scalar action is exactly the map of the actual
cohomology presheaf induced by multiplying the sheaf by that scalar. -/
theorem schemeModuleOpenCohomology_smul {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) (n : ℕ) (a : k)
    (x : ((schemeModulesToAbelianSheaves X).obj F).H' n U) :
    letI := schemeModuleOpenCohomologyModule p U F n
    a • x = (((Sheaf.cohomologyPresheafFunctor _ n).map
      (schemeModuleScalarEnd p F a)).app (op U)) x := rfl

set_option maxHeartbeats 600000 in
/-- The actual open restriction comparison is linear for the base-field
actions induced independently by the ambient and restricted schemes. -/
def schemeOpenCohomologyLinearEquiv {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) (n : ℕ) :
    letI := schemeModuleOpenCohomologyModule p U F n
    letI := schemeModuleCohomologyModule (U.ι ≫ p) (F.restrict U.ι) n
    ((schemeModulesToAbelianSheaves X).obj F).H' n U ≃ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves U.toScheme).obj (F.restrict U.ι)) n := by
  letI := schemeModuleOpenCohomologyModule p U F n
  letI := schemeModuleCohomologyModule (U.ι ≫ p) (F.restrict U.ι) n
  refine { __ := schemeOpenCohomologyEquiv U F n, map_smul' := ?_ }
  intro a x
  change schemeOpenCohomologyEquiv U F n
    (((Sheaf.cohomologyPresheafFunctor _ n).map (schemeModuleScalarEnd p F a)).app (op U) x) =
      Sheaf.H.map (schemeModuleScalarEnd (U.ι ≫ p) (F.restrict U.ι) a) n
        (schemeOpenCohomologyEquiv U F n x)
  rw [schemeOpenCohomologyEquiv_apply, schemeOpenCohomologyEquiv_apply,
    openSheafCohomologyEquiv_naturality, schemeModuleScalarEnd_open]
  rfl

end Normalizer
