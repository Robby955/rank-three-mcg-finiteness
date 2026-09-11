import Normalizer.SchemeOpenCohomology
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.LinearAlgebra.Isomorphisms

/-! The actual Mayer-Vietoris presentation of first cohomology for a cover
by two affine opens. No global cohomology finiteness is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Abelian
universe u
variable {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)

/-- The actual two-open cover square, with ambient top open as its terminal
corner. -/
def twoOpenCoverSquare : (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U ⊓ V, X₂ := U, X₃ := V, X₄ := ⊤
      f₁₂ := homOfLE inf_le_left, f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top, f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ } hUV.symm rfl

/-- The original Mayer-Vietoris connecting map, with target transported
from ambient-top evaluation to actual global first cohomology. -/
def twoOpenCohomologyδ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.H' 0 (U ⊓ V) →+ F.H 1 :=
  (sheafCohomologyTerminalEquiv _ isTerminalTop F 1).toAddMonoidHom.comp
    ((twoOpenCoverSquare U V hUV).δ F 0 1 rfl).hom

/-- With two affine opens and an actual quasicoherent sheaf, every global
first-cohomology class is the boundary of a degree-zero class on the
intersection. The two local vanishings are proved, not supplied. -/
theorem quasicoherent_twoAffine_δ_surjective (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) [F.IsQuasicoherent] :
    Function.Surjective (twoOpenCohomologyδ U V hUV
      ((schemeModulesToAbelianSheaves X).obj F)) := by
  let A := (schemeModulesToAbelianSheaves X).obj F
  let S := twoOpenCoverSquare U V hUV
  have : Subsingleton (A.H' 1 S.X₂) := quasicoherent_affineOpen_H1_subsingleton U hU F
  have : Subsingleton (A.H' 1 S.X₃) := quasicoherent_affineOpen_H1_subsingleton V hV F
  intro x
  let y := (sheafCohomologyTerminalEquiv _ isTerminalTop A 1).symm x
  have ht : S.toBiprod A 1 y = 0 := by
    apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    exact Subsingleton.elim _ _
  have hz : (Ext.mk₀ S.shortComplex.g).comp y (zero_add 1) = 0 := by
    rw [← S.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply, ht]
    simp only [map_zero]
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ S.shortComplex_shortExact A y hz
    (show 1 + 0 = 1 from rfl)
  refine ⟨z, ?_⟩
  change sheafCohomologyTerminalEquiv _ isTerminalTop A 1
    (S.shortComplex_shortExact.extClass.comp z (by omega)) = x
  rw [hz]
  exact (sheafCohomologyTerminalEquiv _ isTerminalTop A 1).apply_symm_apply x

/-- The kernel of the actual global connecting map consists exactly of
differences of the two cohomological restriction maps in degree zero. -/
theorem twoOpenCohomologyδ_eq_zero_iff (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : F.H' 0 (U ⊓ V)) :
    twoOpenCohomologyδ U V hUV F x = 0 ↔
      ∃ y : ↑(F.H' 0 U ⊞ F.H' 0 V), (twoOpenCoverSquare U V hUV).fromBiprod F 0 y = x := by
  let S := twoOpenCoverSquare U V hUV
  constructor
  · intro hx
    have hz : S.shortComplex_shortExact.extClass.comp x (show 1 + 0 = 1 from rfl) = 0 :=
      (sheafCohomologyTerminalEquiv _ isTerminalTop F 1).map_eq_zero_iff.mp hx
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ S.shortComplex_shortExact F x rfl hz
    let z : ↑(F.H' 0 S.X₂ ⊞ F.H' 0 S.X₃) :=
      (AddCommGrpCat.biprodIsoProd (F.H' 0 S.X₂) (F.H' 0 S.X₃)).inv (Ext.biprodAddEquiv y)
    refine ⟨z, ?_⟩
    rw [← S.mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom]
    simpa [z] using hy
  · rintro ⟨y, rfl⟩
    change sheafCohomologyTerminalEquiv _ isTerminalTop F 1
      (S.δ F 0 1 rfl (S.fromBiprod F 0 y)) = 0
    rw [← ConcreteCategory.comp_apply, S.fromBiprod_δ]
    exact map_zero _

/-- The actual two-open connecting map is linear over the structure field.
This follows from composition of extension classes and the natural terminal
comparison, with the previously constructed scalar actions. -/
def twoOpenCohomologyδLinear {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (F : X.Modules) :
    letI := schemeModuleOpenCohomologyModule p (U ⊓ V) F 0
    letI := schemeModuleCohomologyModule p F 1
    ((schemeModulesToAbelianSheaves X).obj F).H' 0 (U ⊓ V) →ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1 := by
  letI := schemeModuleOpenCohomologyModule p (U ⊓ V) F 0
  letI := schemeModuleCohomologyModule p F 1
  refine { __ := twoOpenCohomologyδ U V hUV _, map_smul' := ?_ }
  intro a x
  let S := twoOpenCoverSquare U V hUV
  change sheafCohomologyTerminalEquiv _ isTerminalTop _ 1
    (S.shortComplex_shortExact.extClass.comp
      (x.comp (Ext.mk₀ (schemeModuleScalarEnd p F a)) (add_zero 0)) (by omega)) =
      Sheaf.H.map (schemeModuleScalarEnd p F a) 1
        (sheafCohomologyTerminalEquiv _ isTerminalTop _ 1
          (S.shortComplex_shortExact.extClass.comp x (by omega)))
  rw [← Ext.comp_assoc_of_third_deg_zero]
  exact sheafCohomologyTerminalEquiv_naturality _ isTerminalTop
    (schemeModuleScalarEnd p F a) 1 _

/-- First cohomology on an actual two-affine cover is the base-field-linear
quotient of intersection H⁰ by the kernel of the actual connecting map.
The preceding kernel theorem identifies it with the restriction differences. -/
def twoAffineH1QuotientEquiv {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) [F.IsQuasicoherent] :
    letI := schemeModuleOpenCohomologyModule p (U ⊓ V) F 0
    letI := schemeModuleCohomologyModule p F 1
    (((schemeModulesToAbelianSheaves X).obj F).H' 0 (U ⊓ V) ⧸
      (twoOpenCohomologyδLinear U V hUV p F).ker) ≃ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1 := by
  letI := schemeModuleOpenCohomologyModule p (U ⊓ V) F 0
  letI := schemeModuleCohomologyModule p F 1
  exact (twoOpenCohomologyδLinear U V hUV p F).quotKerEquivOfSurjective
    (quasicoherent_twoAffine_δ_surjective U V hUV hU hV F)

end Normalizer
