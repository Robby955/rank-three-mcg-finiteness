import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation

/-! Finite module presentations give finite presentations of actual affine sheaves.

The sheaf property is mathlib's `SheafOfModules.IsFinitePresentation`, built
from finite generators and relations on an actual cover. No affine-section
finite-presentation assertion is assumed in this construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

open CategoryTheory Limits AlgebraicGeometry
open TopologicalSpace

universe u

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {E : SheafOfModules.{u} R}

/-- An actual finite global presentation supplies finite local presentations
by restriction to the trivial cover. -/
theorem sheafPresentation_isFinitePresentation (P : E.Presentation) [P.IsFinite] :
    E.IsFinitePresentation := by
  refine SheafOfModules.IsFinitePresentation.mk (M := E) ⟨P.quasicoherentData, ?_⟩
  constructor
  intro i
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)

/-- Tilde retains finite generators and finite relations in the actual global
sheaf presentation supplied by a module presentation. -/
theorem presentationTilde_isFinite (s : Finset M)
    (hs : Submodule.span A (s : Set M) = ⊤)
    (t : Finset (s →₀ A))
    (ht : Submodule.span A (t : Set (s →₀ A)) =
      LinearMap.ker (Finsupp.linearCombination A ((↑) : s → M))) :
    (presentationTilde M (s : Set M) hs (t : Set (s →₀ A)) ht).IsFinite := by
  constructor
  · constructor
    change Finite s
    infer_instance
  · constructor
    change Finite t
    infer_instance

/-- A finitely presented module gives a finitely presented actual sheaf of
modules on its affine spectrum. -/
theorem tilde_isFinitePresentation [Module.FinitePresentation A M] :
    (tilde M).IsFinitePresentation := by
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := A) (M := M)
  let P := presentationTilde M (s : Set M) hs (t : Set (s →₀ A)) ht
  let : P.IsFinite := presentationTilde_isFinite M s hs t ht
  exact sheafPresentation_isFinitePresentation P

/-- A finite global presentation of an actual affine sheaf gives a finitely
presented module of global sections. The proof reconstructs a finite module
cokernel and its sheaf isomorphism; it does not assume that global sections
preserve arbitrary sheaf cokernels. -/
theorem affinePresentation_sections_finitePresentation (E : (Spec A).Modules)
    (P : E.Presentation) [P.IsFinite] :
    Module.FinitePresentation A ((moduleSpecΓFunctor (R := A)).obj E) := by
  let g : ModuleCat.of A (P.relations.I →₀ A) ⟶
      ModuleCat.of A (P.generators.I →₀ A) :=
    (tilde.functor A).preimage <| (tildeFinsupp _).hom ≫ P.relations.π ≫
      kernel.ι _ ≫ (tildeFinsupp _).inv
  let e : cokernel ((tilde.functor A).map g) ≅
      cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor A).map_preimage]
    simp
  let eSheaf : tilde (cokernel g) ≅ E :=
    PreservesCokernel.iso (tilde.functor A) g ≪≫ e ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit
  let eModule : cokernel g ≅ (moduleSpecΓFunctor (R := A)).obj E :=
    tilde.isoTop (cokernel g) ≪≫ (moduleSpecΓFunctor (R := A)).mapIso eSheaf
  have hquot : Module.FinitePresentation A
      ((P.generators.I →₀ A) ⧸ LinearMap.range g.hom) := by
    apply Module.finitePresentation_of_surjective (LinearMap.range g.hom).mkQ
      (LinearMap.range g.hom).mkQ_surjective
    rw [Submodule.ker_mkQ]
    exact Submodule.fg_range g.hom
  let := hquot
  let : Module.FinitePresentation A ↑(cokernel g) :=
    Module.FinitePresentation.of_equiv (ModuleCat.cokernelIsoRangeQuotient g).symm.toLinearEquiv
  exact Module.FinitePresentation.of_equiv eModule.toLinearEquiv

/-- A finitely presented actual module sheaf admits an affine open cover
whose restrictions have actual finite global presentations. Finiteness is
retained when refining the defining presentation cover and identifying each
affine open with its spectrum. -/
theorem exists_affineOpenCover_finitePresentation {Y : Scheme.{u}}
    (E : Y.Modules) [E.IsFinitePresentation] :
    ∃ (𝒰 : Scheme.AffineOpenCover.{u} Y),
      ∀ i, ∃ (P : (E.restrict (𝒰.f i)).Presentation), P.IsFinite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData E
  let := hq
  choose κ hsub heq using fun i ↦ Opens.isBasis_iff_cover.mp Y.isBasis_affineOpens (q.X i)
  let U : (Σ (i : q.I), κ i) → Y.Opens := fun j ↦ j.2
  have hU : IsOpenCover U := by
    have cov := q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover, iSup_sigma, ← cov]
    refine iSup_congr fun i ↦ ?_
    rw [heq i, sSup_eq_iSup']
  have hU' : ∀ i, IsAffineOpen (U i) := fun j ↦ hsub _ j.2.2
  refine ⟨Scheme.AffineOpenCover.ofIsOpenCover U hU hU', fun i ↦ ?_⟩
  let f := Y.homOfLE (U := i.2) (V := q.X i.1) (by simp [heq, le_sSup])
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) := inferInstance
  let F := (Scheme.Modules.overEquiv (q.X i.1)).functor ⋙ Scheme.Modules.restrictFunctor f
  let e : SheafOfModules.overFunctor Y.ringCatSheaf _ ⋙ F ≅
      Scheme.Modules.restrictFunctor (Scheme.Opens.ι i.2.1) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
      (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (by simp [f]))
  let P₀ := (q.presentation i.1).map F (Scheme.Modules.restrictUnitIso _).symm
  have : P₀.IsFinite := by
    constructor
    · constructor
      change Finite (q.presentation i.1).generators.I
      infer_instance
    · constructor
      change Finite (q.presentation i.1).relations.I
      infer_instance
  let P₁ := SheafOfModules.Presentation.ofIsIso (e.app E).hom P₀
  have : P₁.IsFinite := inferInstance
  let P₂ := Scheme.Modules.presentationRestrict (hU' i).isoSpec.inv P₁
  have : P₂.IsFinite := by
    constructor
    · constructor
      change Finite P₁.generators.I
      infer_instance
    · constructor
      change Finite P₁.relations.I
      infer_instance
  exact ⟨SheafOfModules.Presentation.ofIsIso
    ((Scheme.Modules.restrictFunctorComp _ _).app E).inv P₂, inferInstance⟩

end Normalizer
