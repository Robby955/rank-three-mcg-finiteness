import Normalizer.SheafFreeNeighborhood

/-! Assembling actual finite free neighborhoods into local generating data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u
variable {X Y : Scheme.{u}} (E : X.Modules)

/-- A free trivialization on an open immersion gives a free trivialization
on the over-site of its actual open image. -/
def openImmersionOverFreeIso (f : Y ⟶ X) [IsOpenImmersion f]
    (I : Type u) (eFree : E.restrict f ≅ SheafOfModules.free I) :
    E.over f.opensRange ≅ SheafOfModules.free I := by
  let U := f.opensRange
  have h : Set.range f = Set.range U.ι := by simp [U]
  let e : Y ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq f U.ι h
  have he : e.inv ≫ f = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac f U.ι h
  let F := Scheme.Modules.restrictFunctor e.inv
  have : PreservesColimitsOfSize.{u, u} F :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor e.inv))
  let eU : E.restrict U.ι ≅ SheafOfModules.free I :=
    ((Scheme.Modules.restrictFunctorCongr he).symm.app E) ≪≫
      (Scheme.Modules.restrictFunctorComp e.inv f).app E ≪≫ F.mapIso eFree ≪≫
      (SheafOfModules.mapFreeIso F I (Scheme.Modules.restrictUnitIso e.inv).symm).symm
  let Q := Scheme.Modules.overEquiv U
  exact Q.unitIso.app (E.over U) ≪≫
    Q.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app E ≪≫ eU) ≪≫
    (SheafOfModules.mapFreeIso Q.inverse I
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).symm

/-- Free trivializations on an actual open cover supply local generators. -/
def freeCoverLocalGeneratorsData {A : Type u} (U : A → X.Opens)
    (hU : IsOpenCover U) (I : A → Type u)
    (e : ∀ a, E.over (U a) ≅ SheafOfModules.free (I a)) :
    SheafOfModules.LocalGeneratorsData.{u} E where
  I := A
  X := U
  coversTop := (Opens.coversTop_iff X U).mpr hU
  generators a := (SheafOfModules.free.generatingSections (I a)).ofEpi (e a).inv

/-- Each local generator map from a free trivialization is an isomorphism. -/
theorem freeCoverLocalGeneratorsData_isLocallyFree {A : Type u} (U : A → X.Opens)
    (hU : IsOpenCover U) (I : A → Type u)
    (e : ∀ a, E.over (U a) ≅ SheafOfModules.free (I a)) :
    (freeCoverLocalGeneratorsData E U hU I e).IsLocallyFreeData := by
  constructor
  intro a
  change IsIso ((SheafOfModules.free.generatingSections (I a)).ofEpi (e a).inv).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A finitely presented actual scheme module sheaf with free actual stalks
is locally free in mathlib's sense. The proof constructs the local generators
from the previously proved affine neighborhoods. -/
theorem sheaf_isLocallyFree_of_free_stalks [E.IsFinitePresentation]
    (hfree : ∀ x : X, Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x)) :
    E.IsLocallyFree := by
  have h (x : X) : ∃ U : X.Opens, x ∈ U ∧ ∃ I : Type u,
      Nonempty (E.over U ≅ SheafOfModules.free I) := by
    let := hfree x
    obtain ⟨S, f, hf, hx, I, _, ⟨e⟩⟩ := sheafStalk_exists_finiteFree_neighborhood E x
    let := hf
    exact ⟨f.opensRange, hx, I, ⟨openImmersionOverFreeIso E f I e⟩⟩
  choose U hx I e using h
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let q := freeCoverLocalGeneratorsData E U hU I (fun x => (e x).some)
  let : q.IsLocallyFreeData :=
    freeCoverLocalGeneratorsData_isLocallyFree E U hU I (fun x => (e x).some)
  exact q.isLocallyFree

end Normalizer
