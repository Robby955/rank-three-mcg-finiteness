import Normalizer.SchemeGenericEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Coordinates of an actual finite trivial module sheaf, obtained from
its categorical biproduct rather than supplied as a family of linear maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

universe u
variable (X : Scheme.{u}) (ι : Type u) [Fintype ι]

/-- The actual finite trivial bundle, as a biproduct of unit sheaves. -/
abbrev schemeTrivialBundle : X.Modules :=
  ⨁ (fun _ : ι => SheafOfModules.unit X.ringCatSheaf)

/-- The chosen biproduct model is canonically isomorphic to mathlib's
free sheaf on the same finite index type. -/
def schemeTrivialBundleIsoFree :
    schemeTrivialBundle X ι ≅ SheafOfModules.free (R := X.ringCatSheaf) ι :=
  biproduct.isoCoproduct _

/-- Each coordinate is an actual morphism of module sheaves. -/
def schemeTrivialProjection (i : ι) :
    schemeTrivialBundle X ι ⟶ SheafOfModules.unit X.ringCatSheaf :=
  biproduct.π _ i

/-- A standard frame vector is an actual section on each open. -/
def schemeTrivialSection (U : X.Opens) (i : ι) : Γ(schemeTrivialBundle X ι, U) :=
  (biproduct.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i).val.app (op U) (1 : Γ(X, U))

/-- Evaluation identifies sections of the actual trivial bundle with
tuples of regular functions on that open. -/
def schemeTrivialCoordinates (U : X.Opens) :
    Γ(schemeTrivialBundle X ι, U) ≃ₗ[Γ(X, U)] (ι → Γ(X, U)) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let B := fun _ : ι => SheafOfModules.unit X.ringCatSheaf
  letI : PreservesBiproduct B F := preservesBiproduct_of_preservesProduct F
  exact ((F.mapBiproduct B).trans
    ((biproduct.isoProduct (F.obj ∘ B)).trans (ModuleCat.piIsoPi (F.obj ∘ B)))).toLinearEquiv

/-- The coordinate equivalence is evaluation of the actual projections. -/
theorem schemeTrivialCoordinates_apply (U : X.Opens)
    (s : Γ(schemeTrivialBundle X ι, U)) (i : ι) :
    schemeTrivialCoordinates X ι U s i =
      (schemeTrivialProjection X ι i).val.app (op U) s := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let B := fun _ : ι => SheafOfModules.unit X.ringCatSheaf
  let : PreservesBiproduct B F := preservesBiproduct_of_preservesProduct F
  have h := F.biproductComparison_π B i
  have h₂ := ModuleCat.piIsoPi_hom_ker_subtype (F.obj ∘ B) i
  have hr : (F.mapBiproduct B).hom ≫ (biproduct.isoProduct (F.obj ∘ B)).hom ≫
      (ModuleCat.piIsoPi (F.obj ∘ B)).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      F.map (biproduct.π B i) := by
    rw [h₂, biproduct.isoProduct_hom, Pi.lift_π]
    exact h
  exact ConcreteCategory.congr_hom hr s

/-- The constructed standard frame has the expected Kronecker coordinates. -/
theorem schemeTrivialCoordinates_section [DecidableEq ι] (U : X.Opens) (i j : ι) :
    schemeTrivialCoordinates X ι U (schemeTrivialSection X ι U i) j =
      if i = j then 1 else 0 := by
  rw [schemeTrivialCoordinates_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf => f.val.app (op U) (1 : Γ(X, U)))
      (biproduct.ι_π_self (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i)
  · rw [ite_eq_right hij]
    exact congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf => f.val.app (op U) (1 : Γ(X, U)))
      (biproduct.ι_π_ne (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) hij)

/-- Standard frame sections are compatible on all opens. -/
theorem schemeTrivialSection_restrict {U V : X.Opens} (h : V ≤ U) (i : ι) :
    (schemeTrivialBundle X ι).presheaf.map (homOfLE h).op (schemeTrivialSection X ι U i) =
      schemeTrivialSection X ι V i := by
  have hn := PresheafOfModules.naturality_apply
    (biproduct.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i).val (homOfLE h).op (1 : Γ(X, U))
  have ho : (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op (1 : Γ(X, U)) =
      (1 : X.presheaf.obj (op V)) := map_one (X.presheaf.map (homOfLE h).op).hom
  exact hn.symm.trans (congrArg
    ((biproduct.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i).val.app (op V)) ho)

/-- Actual sections expand in the constructed finite frame with their
actual regular-function coordinates. -/
theorem schemeTrivialSection_expansion [DecidableEq ι] (U : X.Opens)
    (s : Γ(schemeTrivialBundle X ι, U)) :
    ∑ i, schemeTrivialCoordinates X ι U s i • schemeTrivialSection X ι U i = s := by
  apply (schemeTrivialCoordinates X ι U).injective
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    schemeTrivialCoordinates_section, smul_eq_mul]
  simp

end Normalizer
