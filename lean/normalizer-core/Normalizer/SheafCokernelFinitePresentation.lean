import Normalizer.SheafFinitePresentation
import Normalizer.StalkLocalFreeness

/-! Finite presentations of actual sheaf cokernels, via affine module presentations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

variable {R : CommRingCat.{u}}

/-- A finitely presented module has a finite global presentation after tilde. -/
theorem tilde_exists_finitePresentation (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    ∃ (P : (tilde M).Presentation), P.IsFinite := by
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
  exact ⟨presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht,
    presentationTilde_isFinite M s hs t ht⟩

/-- Finite global presentations of both affine sheaves give a finite global
presentation of their actual categorical cokernel. The proof transports the
map through the affine equivalence, rather than asserting right exactness of
global sections for arbitrary sheaves. -/
theorem affineCokernel_exists_finitePresentation
    {E H : (Spec R).Modules} (f : E ⟶ H)
    (PE : E.Presentation) [PE.IsFinite] (PH : H.Presentation) [PH.IsFinite] :
    ∃ (P : (cokernel f).Presentation), P.IsFinite := by
  let ME := (moduleSpecΓFunctor (R := R)).obj E
  let MH := (moduleSpecΓFunctor (R := R)).obj H
  let : Module.FinitePresentation R ME := affinePresentation_sections_finitePresentation E PE
  let : Module.FinitePresentation R MH := affinePresentation_sections_finitePresentation H PH
  let : E.IsQuasicoherent := PE.isQuasicoherent
  let : H.IsQuasicoherent := PH.isQuasicoherent
  let eE : tilde ME ≅ E := asIso E.fromTildeΓ
  let eH : tilde MH ≅ H := asIso H.fromTildeΓ
  let g : ME ⟶ MH := (tilde.functor R).preimage (eE.hom ≫ f ≫ eH.inv)
  have hquot : Module.FinitePresentation R (MH ⧸ LinearMap.range g.hom) := by
    apply Module.finitePresentation_of_surjective (LinearMap.range g.hom).mkQ
      (LinearMap.range g.hom).mkQ_surjective
    rw [Submodule.ker_mkQ]
    exact Submodule.fg_range g.hom
  let := hquot
  let : Module.FinitePresentation R ↑(cokernel g) :=
    Module.FinitePresentation.of_equiv (ModuleCat.cokernelIsoRangeQuotient g).symm.toLinearEquiv
  let e : tilde (cokernel g) ≅ cokernel f :=
    PreservesCokernel.iso (tilde.functor R) g ≪≫
      cokernel.mapIso _ _ eE eH (by
        change (tilde.functor R).map g ≫ eH.hom = eE.hom ≫ f
        simp only [g, Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨P, hP⟩ := tilde_exists_finitePresentation (cokernel g)
  let := hP
  exact ⟨P.ofIsIso e.hom, inferInstance⟩

variable {X : Scheme.{u}}

/-- Restrict a presentation from the over-site of an open to a smaller
open subscheme, through the actual equivalence of the two sites. -/
def presentationRestrictFromOver (E : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (P : (E.over V).Presentation) : (E.restrict U.ι).Presentation := by
  let f := X.homOfLE h
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) := inferInstance
  let F := (Scheme.Modules.overEquiv V).functor ⋙ Scheme.Modules.restrictFunctor f
  let e : SheafOfModules.overFunctor X.ringCatSheaf V ⋙ F ≅
      Scheme.Modules.restrictFunctor U.ι :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv V) _ ≪≫
      (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [f])
  exact (P.map F (Scheme.Modules.restrictUnitIso _).symm).ofIsIso (e.app E).hom

/-- The restriction construction retains the finite generator and relation types. -/
theorem presentationRestrictFromOver_isFinite (E : X.Modules)
    {U V : X.Opens} (h : U ≤ V) (P : (E.over V).Presentation) [P.IsFinite] :
    (presentationRestrictFromOver E h P).IsFinite := by
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

/-- Two finitely presented sheaves have simultaneous finite global
presentations on one affine open cover. -/
theorem exists_common_affineOpenCover_finitePresentation
    (E H : X.Modules) [E.IsFinitePresentation] [H.IsFinitePresentation] :
    ∃ (𝒰 : Scheme.AffineOpenCover.{u} X), ∀ i,
      (∃ (P : (E.restrict (𝒰.f i)).Presentation), P.IsFinite) ∧
      (∃ (P : (H.restrict (𝒰.f i)).Presentation), P.IsFinite) := by
  obtain ⟨qE, hE⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData E
  obtain ⟨qH, hH⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData H
  let := hE
  let := hH
  have h (x : X) : ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      (∃ i, U ≤ qE.X i) ∧ (∃ j, U ≤ qH.X j) := by
    obtain ⟨i, hi⟩ := ((Opens.coversTop_iff X qE.X).mp qE.coversTop).exists_mem x
    obtain ⟨j, hj⟩ := ((Opens.coversTop_iff X qH.X).mp qH.coversTop).exists_mem x
    obtain ⟨U, hU, hx, hsub⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ qE.X i ⊓ qH.X j from ⟨hi, hj⟩)
    exact ⟨U, hU, hx, ⟨i, le_trans hsub inf_le_left⟩,
      ⟨j, le_trans hsub inf_le_right⟩⟩
  choose U haff hx hE' hH' using h
  choose i hi using hE'
  choose j hj using hH'
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover U hU haff, fun x ↦ ?_⟩
  have restrictPresentation (M : X.Modules) (V : X.Opens) (hle : U x ≤ V)
      (P : (M.over V).Presentation) [P.IsFinite] :
      ∃ (P : (M.restrict (haff x).fromSpec).Presentation), P.IsFinite := by
    let P₀ := presentationRestrictFromOver M hle P
    let : P₀.IsFinite := presentationRestrictFromOver_isFinite M hle P
    let P₁ := Scheme.Modules.presentationRestrict (haff x).isoSpec.inv P₀
    have : P₁.IsFinite := by
      constructor
      · constructor
        change Finite P₀.generators.I
        infer_instance
      · constructor
        change Finite P₀.relations.I
        infer_instance
    exact ⟨P₁.ofIsIso ((Scheme.Modules.restrictFunctorComp _ _).app M).inv,
      inferInstance⟩
  exact ⟨restrictPresentation E _ (hi x) (qE.presentation (i x)),
    restrictPresentation H _ (hj x) (qH.presentation (j x))⟩

variable {Y : Scheme.{u}}

/-- A presentation on an open immersion gives a presentation on the over-site
of its actual open image. -/
def openImmersionOverPresentation (E : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (P : (E.restrict f).Presentation) : (E.over f.opensRange).Presentation := by
  let U := f.opensRange
  have h : Set.range f = Set.range U.ι := by simp [U]
  let e : Y ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq f U.ι h
  have he : e.inv ≫ f = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac f U.ι h
  let F := Scheme.Modules.restrictFunctor e.inv
  have : PreservesColimitsOfSize.{u, u} F :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor e.inv))
  let eU : E.restrict U.ι ≅ F.obj (E.restrict f) :=
    ((Scheme.Modules.restrictFunctorCongr he).symm.app E) ≪≫
      (Scheme.Modules.restrictFunctorComp e.inv f).app E
  let P₁ := (P.map F (Scheme.Modules.restrictUnitIso e.inv).symm).ofIsIso eU.inv
  let Q := Scheme.Modules.overEquiv U
  let eOver : E.over U ≅ Q.inverse.obj (E.restrict U.ι) :=
    Q.unitIso.app (E.over U) ≪≫
      Q.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app E)
  exact (P₁.map Q.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso
    eOver.inv

/-- Passing to the actual open image preserves finiteness of a presentation. -/
theorem openImmersionOverPresentation_isFinite (E : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (P : (E.restrict f).Presentation) [P.IsFinite] :
    (openImmersionOverPresentation E f P).IsFinite := by
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

/-- Finite presentations on an affine open cover give finite presentation
of the actual sheaf, by constructing its quasicoherent presentation data. -/
theorem sheaf_isFinitePresentation_of_affineCover (E : X.Modules)
    (𝒰 : Scheme.AffineOpenCover.{u} X)
    (h : ∀ i, ∃ (P : (E.restrict (𝒰.f i)).Presentation), P.IsFinite) :
    E.IsFinitePresentation := by
  choose P hP using h
  have hU : IsOpenCover (fun i ↦ (𝒰.f i).opensRange) := by
    apply top_unique
    intro x _
    apply Opens.mem_iSup.mpr
    obtain ⟨y, hy⟩ := 𝒰.covers x
    exact ⟨𝒰.idx x, y, hy⟩
  let q : SheafOfModules.QuasicoherentData (R := X.ringCatSheaf) E :=
    { I := 𝒰.I₀
      X := fun i ↦ (𝒰.f i).opensRange
      coversTop := (Opens.coversTop_iff X _).mpr hU
      presentation := fun i ↦ openImmersionOverPresentation E (𝒰.f i) (P i) }
  have : q.IsFinitePresentation := by
    constructor
    intro i
    let := hP i
    exact openImmersionOverPresentation_isFinite E (𝒰.f i) (P i)
  exact SheafOfModules.IsFinitePresentation.mk (M := E) ⟨q, this⟩

/-- The actual cokernel of a morphism between finitely presented scheme
module sheaves is finitely presented. -/
theorem sheaf_cokernel_isFinitePresentation {E H : X.Modules} (f : E ⟶ H)
    [E.IsFinitePresentation] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  obtain ⟨𝒰, h⟩ := exists_common_affineOpenCover_finitePresentation E H
  apply sheaf_isFinitePresentation_of_affineCover (cokernel f) 𝒰
  intro i
  obtain ⟨⟨PE, hPE⟩, ⟨PH, hPH⟩⟩ := h i
  let := hPE
  let := hPH
  let F := Scheme.Modules.restrictFunctor (𝒰.f i)
  have : PreservesColimitsOfSize.{u, u} F :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.restrictFunctor (𝒰.f i)))
  obtain ⟨P, hP⟩ := affineCokernel_exists_finitePresentation (F.map f) PE PH
  let := hP
  exact ⟨P.ofIsIso (PreservesCokernel.iso F f).inv, inferInstance⟩

/-- On an integral scheme with regular local rings of dimension at most
one, a cokernel with torsion-free stalks is locally free when its source
and target are finitely presented. Finite presentation of the cokernel
is derived, rather than supplied separately. -/
theorem sheaf_cokernel_isLocallyFree_of_regular_stalks [IsIntegral X]
    {E H : X.Modules} (f : E ⟶ H)
    [E.IsFinitePresentation] [H.IsFinitePresentation]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (htf : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x)
      ((cokernel f).presheaf.stalk x)) :
    (cokernel f).IsLocallyFree := by
  let := sheaf_cokernel_isFinitePresentation f
  exact sheaf_isLocallyFree_of_regular_stalks (cokernel f) hreg hdim htf

end Normalizer
