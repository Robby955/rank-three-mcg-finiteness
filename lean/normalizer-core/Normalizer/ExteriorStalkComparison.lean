import Normalizer.ExteriorSheaf
import Normalizer.SheafStalkMap
import Normalizer.LocalFrameStalk
import Normalizer.StalkBracket
import Mathlib.Topology.Sheaves.Sheafify

/-! The canonical comparison from the stalk of the constructed exterior sheaf
to the exterior power of the actual module stalk. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u
variable {X : Scheme.{u}} (H : X.Modules) (n : ℕ) (x : X)

local instance exteriorComparisonSourceSectionModule (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) (H.presheaf.obj U) :=
  (H.val.obj U).isModule

private abbrev exteriorAdditivePresheaf : TopCat.Presheaf AddCommGrpCat.{u} X :=
  (schemeExteriorPresheaf H n).presheaf

local instance exteriorComparisonPresheafSectionModule (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((exteriorAdditivePresheaf H n).obj U) :=
  ((schemeExteriorPresheaf H n).obj U).isModule

/-- The actual module germ is semilinear over the actual local-ring germ. -/
def schemeModuleGermSemilinear (U : X.Opens) (hx : x ∈ U) :
    Γ(H, U) →ₛₗ[(X.presheaf.germ U x hx).hom] H.presheaf.stalk x where
  __ := (H.presheaf.germ U x hx).hom
  map_smul' := schemeModule_germ_smul H x U hx

private def exteriorGerm (U : X.Opens) (hx : x ∈ U) :
    (⋀[Γ(X, U)]^n Γ(H, U)) →ₛₗ[(X.presheaf.germ U x hx).hom]
      (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x)) :=
  exteriorSemilinearMap n (X.presheaf.germ U x hx).hom (schemeModuleGermSemilinear H x U hx)

private theorem exteriorGerm_restrict {U V : X.Opens} (f : V ⟶ U) (hx : x ∈ V)
    (s : (schemeExteriorPresheaf H n).obj (op U)) :
    exteriorGerm H n x V hx ((schemeExteriorPresheaf H n).map f.op s) =
      exteriorGerm H n x U (f.le hx) s := by
  have hs : s ∈ Submodule.span Γ(X, U) (Set.range (exteriorPower.ιMulti Γ(X, U) n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hs using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨v, rfl⟩ := ht
    simp only [schemeExteriorPresheaf_restrict, exteriorGerm, exteriorSemilinearMap_ιMulti]
    congr 1
    funext i
    exact H.presheaf.germ_res_apply f x hx (v i)
  | zero => simp only [map_zero]
  | add a b ha hb ia ib => simp only [map_add, ia, ib]
  | smul r t ht ih =>
    rw [(schemeExteriorPresheaf H n).map_smul, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ, ih]
    congr 1
    exact X.presheaf.germ_res_apply f x hx r

private def exteriorStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (schemeExteriorPresheaf H n).presheaf) where
  pt := AddCommGrpCat.of (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x))
  ι := {
    app := fun U ↦ AddCommGrpCat.ofHom (exteriorGerm H n x U.unop.1 U.unop.2).toAddMonoidHom
    naturality := by
      intro U V f
      ext s
      exact exteriorGerm_restrict H n x ((OpenNhds.inclusion x).map f.unop) V.unop.2 s }

private def exteriorStalkAdd :
    (exteriorAdditivePresheaf H n).stalk x →+
      (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x)) :=
  (colimit.desc _ (exteriorStalkCocone H n x)).hom

private theorem exteriorStalkAdd_germ (U : X.Opens) (hx : x ∈ U)
    (s : (schemeExteriorPresheaf H n).obj (op U)) :
    exteriorStalkAdd H n x ((exteriorAdditivePresheaf H n).germ U x hx s) =
      exteriorGerm H n x U hx s :=
  ConcreteCategory.congr_hom (colimit.ι_desc (exteriorStalkCocone H n x) (op ⟨U, hx⟩)) s

/-- Exterior powers of section germs induce a linear map from the actual
exterior-presheaf stalk, using the colimit that defines that stalk. -/
def exteriorPresheafStalkComparison :
    (exteriorAdditivePresheaf H n).stalk x →ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x)) where
  __ := exteriorStalkAdd H n x
  map_smul' r s := by
    change exteriorStalkAdd H n x (r • s) = r • exteriorStalkAdd H n x s
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := (exteriorAdditivePresheaf H n).exists_le_germ_eq s hxU
    let i : V ⟶ U := homOfLE hVU
    rw [← X.presheaf.germ_res_apply i x hxV a, ← PresheafOfModules.germ_smul]
    change exteriorStalkAdd H n x ((exteriorAdditivePresheaf H n).germ V x hxV
      (X.presheaf.map i.op a • b)) =
      X.presheaf.germ V x hxV (X.presheaf.map i.op a) •
        exteriorStalkAdd H n x ((exteriorAdditivePresheaf H n).germ V x hxV b)
    rw [exteriorStalkAdd_germ, exteriorStalkAdd_germ]
    exact (exteriorGerm H n x V hxV).map_smulₛₗ (X.presheaf.map i.op a) b

private def projectionStalkAdd : (exteriorAdditivePresheaf H n).stalk x →+
    (schemeExteriorSheaf H n).presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (schemeExteriorProjection H n))).hom

private theorem projectionStalkAdd_germ (U : X.Opens) (hx : x ∈ U)
    (s : (schemeExteriorPresheaf H n).obj (op U)) :
    projectionStalkAdd H n x ((exteriorAdditivePresheaf H n).germ U x hx s) =
      (schemeExteriorSheaf H n).presheaf.germ U x hx
        ((schemeExteriorProjection H n).app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (schemeExteriorProjection H n)) s

/-- The actual exterior sheafification projection induces a local-ring-linear
map of the actual stalks. -/
def schemeExteriorProjectionStalk :
    (exteriorAdditivePresheaf H n).stalk x →ₗ[X.presheaf.stalk x]
      (schemeExteriorSheaf H n).presheaf.stalk x where
  __ := projectionStalkAdd H n x
  map_smul' r s := by
    change projectionStalkAdd H n x (r • s) = r • projectionStalkAdd H n x s
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := (exteriorAdditivePresheaf H n).exists_le_germ_eq s hxU
    let i : V ⟶ U := homOfLE hVU
    rw [← X.presheaf.germ_res_apply i x hxV a, ← PresheafOfModules.germ_smul]
    change projectionStalkAdd H n x ((exteriorAdditivePresheaf H n).germ V x hxV
      (X.presheaf.map i.op a • b)) =
      X.presheaf.germ V x hxV (X.presheaf.map i.op a) •
        projectionStalkAdd H n x ((exteriorAdditivePresheaf H n).germ V x hxV b)
    rw [projectionStalkAdd_germ, projectionStalkAdd_germ, map_smul, schemeModule_germ_smul]

/-- Sheafification leaves the actual exterior-presheaf stalk unchanged. -/
theorem schemeExteriorProjectionStalk_bijective :
    Function.Bijective (schemeExteriorProjectionStalk H n x) := by
  let q := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (schemeExteriorProjection H n))
  have : IsIso q := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x
    AddCommGrpCat.{u} (exteriorAdditivePresheaf H n)
  exact ConcreteCategory.bijective_of_isIso q

/-- The actual stalk equivalence supplied by the sheafification projection. -/
def schemeExteriorProjectionStalkEquiv :
    (exteriorAdditivePresheaf H n).stalk x ≃ₗ[X.presheaf.stalk x]
      (schemeExteriorSheaf H n).presheaf.stalk x :=
  LinearEquiv.ofBijective (schemeExteriorProjectionStalk H n x)
    (schemeExteriorProjectionStalk_bijective H n x)

/-- Canonical comparison from the actual exterior-sheaf stalk to the exterior
power of the actual original module stalk. No exterior identification or frame
is supplied as an assumption. -/
def schemeExteriorStalkComparison :
    (schemeExteriorSheaf H n).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x)) :=
  (exteriorPresheafStalkComparison H n x).comp
    (schemeExteriorProjectionStalkEquiv H n x).symm.toLinearMap

/-- The canonical comparison takes the germ of every actual pure exterior
section to the exterior product of its actual section germs. -/
theorem schemeExteriorStalkComparison_germ_pure (U : X.Opens) (hx : x ∈ U)
    (v : Fin n → Γ(H, U)) :
    schemeExteriorStalkComparison H n x
      ((schemeExteriorSheaf H n).presheaf.germ U x hx (schemeExteriorPure H n U v)) =
        exteriorPower.ιMulti (X.presheaf.stalk x) n (fun i ↦ H.presheaf.germ U x hx (v i)) := by
  have hp := projectionStalkAdd_germ H n x U hx (exteriorPower.ιMulti Γ(X, U) n v)
  change schemeExteriorProjectionStalkEquiv H n x
    ((exteriorAdditivePresheaf H n).germ U x hx (exteriorPower.ιMulti Γ(X, U) n v)) =
    (schemeExteriorSheaf H n).presheaf.germ U x hx (schemeExteriorPure H n U v) at hp
  rw [← hp]
  change exteriorPresheafStalkComparison H n x
    ((schemeExteriorProjectionStalkEquiv H n x).symm
      (schemeExteriorProjectionStalkEquiv H n x _)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (exteriorStalkAdd_germ H n x U hx _).trans
    (exteriorSemilinearMap_ιMulti n (X.presheaf.germ U x hx).hom
      (schemeModuleGermSemilinear H x U hx) v)

variable {H n x} {I : Type u} [Fintype I] {U : X.Opens}
  (j : I ≃ Fin n) (eU : (schemeTrivialBundle X I).over U ≅ H.over U) (hxU : x ∈ U)

private def exteriorLineStalkFrame :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (schemeExteriorSheaf H n).presheaf.stalk x :=
  (schemeUnitStalkEquiv x).symm.trans
    (schemeLocalStalkEquiv (bundleTopExteriorSheafIsoOver j eU) x hxU)

private theorem exteriorLineStalkFrame_one :
    exteriorLineStalkFrame j eU hxU 1 =
      (schemeExteriorSheaf H n).presheaf.germ U x hxU
        (schemeExteriorPure H n U (bundleLocalFrameBasis j eU U le_rfl)) := by
  have hu : schemeUnitStalkEquiv x
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hxU
        (1 : Γ(X, U))) = 1 := by
    rw [schemeUnitStalkEquiv_germ, map_one]
  change schemeLocalStalkEquiv (bundleTopExteriorSheafIsoOver j eU) x hxU
    ((schemeUnitStalkEquiv x).symm 1) = _
  rw [← hu, LinearEquiv.symm_apply_apply,
    schemeLocalStalkEquiv_germ _ x hxU U le_rfl hxU,
    bundleTopExteriorSheafIsoOver_hom_one]

include j eU hxU in
/-- At every point with a genuine rank-n bundle chart, the canonical
exterior-stalk comparison is bijective. Its inverse is derived from the actual
line frame and the actual stalk basis, rather than supplied as an assumption. -/
theorem schemeExteriorStalkComparison_bijective_of_chart :
    Function.Bijective (schemeExteriorStalkComparison H n x) := by
  let b := schemeLocalFrameStalkBasis j eU x hxU
  let a := exteriorLineStalkFrame j eU hxU
  let t := (topExteriorCoordinateEquiv b).symm
  have ht : (schemeExteriorStalkComparison H n x).comp a.toLinearMap = t.toLinearMap := by
    apply LinearMap.ext_ring
    change schemeExteriorStalkComparison H n x (exteriorLineStalkFrame j eU hxU 1) =
      (topExteriorCoordinateEquiv b).symm 1
    rw [exteriorLineStalkFrame_one, schemeExteriorStalkComparison_germ_pure,
      topExteriorCoordinateEquiv_symm_apply, one_smul]
    congr 1
    funext i
    exact (schemeLocalFrameStalkBasis_apply j eU x hxU i).symm
  have he : schemeExteriorStalkComparison H n x = (a.symm.trans t).toLinearMap := by
    apply LinearMap.ext
    intro s
    have hs := DFunLike.congr_fun ht (a.symm s)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearEquiv.trans_apply] using hs
  rw [he]
  exact (a.symm.trans t).bijective

/-- The constructed identification of the actual top exterior sheaf stalk with
the top exterior power of the actual stalk, from a genuine local bundle chart. -/
def schemeExteriorStalkEquivOfChart :
    (schemeExteriorSheaf H n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n (H.presheaf.stalk x)) :=
  LinearEquiv.ofBijective (schemeExteriorStalkComparison H n x)
    (schemeExteriorStalkComparison_bijective_of_chart j eU hxU)

/-- The actual stalk identification has the pure-wedge formula for arbitrary
sections on any neighbourhood, whether or not contained in the chosen chart. -/
theorem schemeExteriorStalkEquivOfChart_germ_pure (V : X.Opens) (hxV : x ∈ V)
    (v : Fin n → Γ(H, V)) :
    schemeExteriorStalkEquivOfChart j eU hxU
      ((schemeExteriorSheaf H n).presheaf.germ V x hxV (schemeExteriorPure H n V v)) =
        exteriorPower.ιMulti (X.presheaf.stalk x) n (fun i ↦ H.presheaf.germ V x hxV (v i)) :=
  schemeExteriorStalkComparison_germ_pure H n x V hxV v

end Normalizer
