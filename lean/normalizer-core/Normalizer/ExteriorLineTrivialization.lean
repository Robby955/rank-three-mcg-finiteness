import Normalizer.ExteriorSheaf
import Normalizer.TopExteriorCoordinate
import Normalizer.TrivialBundle
import Normalizer.SheafifyLocalIso
import Normalizer.FiniteBundlePresentation
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! A genuine bundle frame trivializes its constructed top exterior sheaf. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} {H : X.Modules} {I : Type u} [Fintype I]
  {n : ℕ} (j : I ≃ Fin n) (e : schemeTrivialBundle X I ≅ H)

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U) (H.presheaf.obj U) :=
  (H.val.obj U).isModule

/-- A bundle sheaf trivialization supplies an actual basis on each open. -/
def bundleFrameBasis (U : X.Opens) : Module.Basis (Fin n) Γ(X, U) Γ(H, U) :=
  ((Pi.basisFun Γ(X, U) I).map
    ((schemeTrivialCoordinates X I U).symm.trans
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv)).reindex j

/-- The extracted basis vectors are the images of the actual trivial-bundle sections. -/
theorem bundleFrameBasis_apply (U : X.Opens) (i : Fin n) :
    bundleFrameBasis j e U i = e.hom.val.app (op U) (schemeTrivialSection X I U (j.symm i)) := by
  classical
  change (((Pi.basisFun Γ(X, U) I).map
    ((schemeTrivialCoordinates X I U).symm.trans
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv)).reindex j) i = _
  rw [Module.Basis.coe_reindex]
  change e.hom.val.app (op U) ((schemeTrivialCoordinates X I U).symm
    ((Pi.basisFun Γ(X, U) I) (j.symm i))) = _
  congr 1
  apply (schemeTrivialCoordinates X I U).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  simp [Pi.basisFun_apply, schemeTrivialCoordinates_section, Pi.single_apply, eq_comm]

/-- These bases commute with restriction because the original frame is a sheaf isomorphism. -/
theorem bundleFrameBasis_restrict {U V : X.Opens} (f : V ⟶ U) (i : Fin n) :
    H.presheaf.map f.op (bundleFrameBasis j e U i) = bundleFrameBasis j e V i := by
  rw [bundleFrameBasis_apply, bundleFrameBasis_apply]
  have hn := PresheafOfModules.naturality_apply e.hom.val f.op
    (schemeTrivialSection X I U (j.symm i))
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  rw [hf] at hn ⊢
  exact hn.symm.trans (congrArg (e.hom.val.app (op V))
    (schemeTrivialSection_restrict X I (leOfHom f) (j.symm i)))

/-- The wedge of a genuine frame identifies the unit presheaf with the
actual sectionwise top exterior presheaf. -/
def bundleTopExteriorPresheafIso :
    (SheafOfModules.unit X.ringCatSheaf).val ≅ schemeExteriorPresheaf H n := by
  refine PresheafOfModules.isoMk
    (fun U ↦ (topExteriorCoordinateEquiv (bundleFrameBasis j e U.unop)).symm.toModuleIso) ?_
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change X.presheaf.map f r • exteriorPower.ιMulti _ n (bundleFrameBasis j e V.unop) =
    (schemeExteriorPresheaf H n).map f
      (r • exteriorPower.ιMulti _ n (bundleFrameBasis j e U.unop))
  rw [(schemeExteriorPresheaf H n).map_smul, schemeExteriorPresheaf_restrict]
  congr 2
  funext i
  exact (bundleFrameBasis_restrict j e f.unop i).symm

/-- Sheafifying the actual frame-wedge presheaf isomorphism yields a genuine
trivialization of the constructed top exterior sheaf. -/
def bundleTopExteriorSheafIso :
    SheafOfModules.unit X.ringCatSheaf ≅ schemeExteriorSheaf H n :=
  (asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (SheafOfModules.unit X.ringCatSheaf))).symm ≪≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
        (bundleTopExteriorPresheafIso j e)

/-- A local bundle trivialization supplies bases on every smaller open. -/
def bundleLocalFrameBasis {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) (V : X.Opens) (h : V ≤ U) :
    Module.Basis (Fin n) Γ(X, V) Γ(H, V) :=
  ((Pi.basisFun Γ(X, V) I).map
    ((schemeTrivialCoordinates X I V).symm.trans
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE h)))).mapIso eU).toLinearEquiv)).reindex j

/-- Local basis vectors are actual images of the standard frame. -/
theorem bundleLocalFrameBasis_apply {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) (V : X.Opens) (h : V ≤ U)
    (i : Fin n) :
    bundleLocalFrameBasis j eU V h i =
      eU.hom.val.app (op (Over.mk (homOfLE h))) (schemeTrivialSection X I V (j.symm i)) := by
  classical
  change (((Pi.basisFun Γ(X, V) I).map
    ((schemeTrivialCoordinates X I V).symm.trans
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE h)))).mapIso eU).toLinearEquiv)).reindex j) i = _
  rw [Module.Basis.coe_reindex]
  change eU.hom.val.app (op (Over.mk (homOfLE h))) ((schemeTrivialCoordinates X I V).symm
    ((Pi.basisFun Γ(X, V) I) (j.symm i))) = _
  congr 1
  apply (schemeTrivialCoordinates X I V).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  simp [Pi.basisFun_apply, schemeTrivialCoordinates_section, Pi.single_apply, eq_comm]

/-- The local bases have the restriction compatibility of the original sheaf frame. -/
theorem bundleLocalFrameBasis_restrict {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U)
    {V W : X.Opens} (h : W ≤ V) (k : V ≤ U) (i : Fin n) :
    H.presheaf.map (homOfLE h).op (bundleLocalFrameBasis j eU V k i) =
      bundleLocalFrameBasis j eU W (h.trans k) i := by
  rw [bundleLocalFrameBasis_apply, bundleLocalFrameBasis_apply]
  let f : Over.mk (homOfLE (h.trans k)) ⟶ Over.mk (homOfLE k) :=
    Over.homMk (homOfLE h)
  have hn := PresheafOfModules.naturality_apply eU.hom.val f.op
    (schemeTrivialSection X I V (j.symm i))
  exact hn.symm.trans (congrArg (eU.hom.val.app (op (Over.mk (homOfLE (h.trans k)))))
    (schemeTrivialSection_restrict X I h (j.symm i)))

private def exteriorOverPresheaf (U : X.Opens) :
    PresheafOfModules (X.ringCatSheaf.over U).obj :=
  (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj
    (schemeExteriorPresheaf H n)

/-- On a trivializing open, the actual sectionwise top exterior presheaf is
already a line presheaf. -/
def bundleTopExteriorPresheafIsoOver {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) :
    ((SheafOfModules.unit X.ringCatSheaf).over U).val ≅
      exteriorOverPresheaf (H := H) (n := n) U := by
  refine PresheafOfModules.isoMk
    (fun V ↦ (topExteriorCoordinateEquiv
      (bundleLocalFrameBasis j eU V.unop.left (leOfHom V.unop.hom))).symm.toModuleIso) ?_
  intro V W f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change X.presheaf.map f.unop.left.op r • exteriorPower.ιMulti _ n
      (bundleLocalFrameBasis j eU W.unop.left (leOfHom W.unop.hom)) =
    (schemeExteriorPresheaf H n).map f.unop.left.op
      (r • exteriorPower.ιMulti _ n (bundleLocalFrameBasis j eU V.unop.left (leOfHom V.unop.hom)))
  rw [(schemeExteriorPresheaf H n).map_smul, schemeExteriorPresheaf_restrict]
  congr 2
  funext i
  exact (bundleLocalFrameBasis_restrict j eU (leOfHom f.unop.left)
    (leOfHom V.unop.hom) i).symm

/-- The actual local line-frame map into the constructed exterior sheaf. -/
def bundleTopExteriorSheafMapOver {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over U ⟶ (schemeExteriorSheaf H n).over U where
  val := (bundleTopExteriorPresheafIsoOver j eU).hom ≫
    (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      (schemeExteriorProjection H n)

/-- The local frame map is an isomorphism: the sheafification projection is
locally bijective after restriction, and the presheaf frame map is invertible. -/
theorem bundleTopExteriorSheafMapOver_isIso {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) :
    IsIso (bundleTopExteriorSheafMapOver j eU) := by
  let J := Opens.grothendieckTopology X
  let q := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
    (schemeExteriorProjection H n)
  have hqi : Presheaf.IsLocallyInjective J q := by
    change Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (schemeExteriorPresheaf H n).presheaf)
    infer_instance
  have hqs : Presheaf.IsLocallySurjective J q := by
    change Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (schemeExteriorPresheaf H n).presheaf)
    infer_instance
  have hi := Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) q
  have hs := Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) q
  let g := (SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map
    (bundleTopExteriorSheafMapOver j eU)
  have hg : g.hom =
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map
        (bundleTopExteriorPresheafIsoOver j eU).hom ≫
          Functor.whiskerLeft (Over.forget U).op q := rfl
  have : Presheaf.IsLocallyInjective (J.over U) g.hom := by
    rw [hg]
    infer_instance
  have : Presheaf.IsLocallySurjective (J.over U) g.hom := by
    rw [hg]
    infer_instance
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso (bundleTopExteriorSheafMapOver j eU)
    (SheafOfModules.toSheaf (X.ringCatSheaf.over U))

/-- A genuine local rank-n trivialization yields a genuine line trivialization
of the constructed top exterior sheaf on the same open. -/
def bundleTopExteriorSheafIsoOver {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅ (schemeExteriorSheaf H n).over U := by
  have := bundleTopExteriorSheafMapOver_isIso j eU
  exact asIso (bundleTopExteriorSheafMapOver j eU)

/-- The local exterior-line isomorphism sends the unit to the actual exterior
product of the bundle frame on every smaller open. -/
theorem bundleTopExteriorSheafIsoOver_hom_one {U : X.Opens}
    (eU : (schemeTrivialBundle X I).over U ≅ H.over U) (V : X.Opens) (h : V ≤ U) :
    (bundleTopExteriorSheafIsoOver j eU).hom.val.app (op (Over.mk (homOfLE h)))
      (1 : Γ(X, V)) = schemeExteriorPure H n V (bundleLocalFrameBasis j eU V h) := by
  change (schemeExteriorProjection H n).app (op V)
    ((1 : Γ(X, V)) • exteriorPower.ιMulti _ n (bundleLocalFrameBasis j eU V h)) = _
  rw [one_smul]
  rfl

/-- The standard trivial bundle restricted to an open is the actual free
sheaf on the same finite index set over that open. -/
def schemeTrivialBundleOverIsoFree (U : X.Opens) :
    (schemeTrivialBundle X I).over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) I := by
  let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} F := inferInstance
  let eO : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      F.obj (SheafOfModules.unit X.ringCatSheaf) := Iso.refl _
  exact F.mapIso (schemeTrivialBundleIsoFree X I) ≪≫
    (SheafOfModules.mapFreeIso F I eO).symm

/-- An actual free-sheaf trivialization of rank n gives an actual exterior
line trivialization, with no supplied exterior comparison. -/
def exteriorLineIsoOfFree {U : X.Opens}
    (eU : H.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) I) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅ (schemeExteriorSheaf H n).over U :=
  bundleTopExteriorSheafIsoOver j (schemeTrivialBundleOverIsoFree U ≪≫ eU.symm)

include j in
/-- Genuine finite-free charts of fixed rank make the constructed top exterior
sheaf locally free in mathlib's sense. -/
theorem exteriorSheaf_isLocallyFree_of_free_cover
    {A : Type u} (U : A → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (eU : ∀ a, H.over (U a) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U a)) I) :
    (schemeExteriorSheaf H n).IsLocallyFree := by
  let J : A → Type u := fun _ ↦ PUnit.{u + 1}
  let eL (a : A) : (schemeExteriorSheaf H n).over (U a) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (U a)) (J a) :=
    (exteriorLineIsoOfFree j (eU a)).symm ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit (X.ringCatSheaf.over (U a)))).symm
  let q := freeCoverLocalGeneratorsData (schemeExteriorSheaf H n) U hU J eL
  let : q.IsLocallyFreeData :=
    freeCoverLocalGeneratorsData_isLocallyFree (schemeExteriorSheaf H n) U hU J eL
  exact q.isLocallyFree

include j in
/-- The same actual rank-one charts give finite presentation of the constructed
top exterior sheaf; finite presentation is a conclusion, not an extra input. -/
theorem exteriorSheaf_isFinitePresentation_of_free_cover
    {A : Type u} (U : A → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (eU : ∀ a, H.over (U a) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U a)) I) :
    (schemeExteriorSheaf H n).IsFinitePresentation := by
  let J : A → Type u := fun _ ↦ PUnit.{u + 1}
  let eL (a : A) : (schemeExteriorSheaf H n).over (U a) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (U a)) (J a) :=
    (exteriorLineIsoOfFree j (eU a)).symm ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit (X.ringCatSheaf.over (U a)))).symm
  exact sheaf_isFinitePresentation_of_finiteFree_cover (schemeExteriorSheaf H n) U hU J eL

end Normalizer
