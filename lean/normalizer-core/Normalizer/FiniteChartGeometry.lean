import Normalizer.ProjectiveCoordinates
import Normalizer.CurveProjectiveLine
import Mathlib.RingTheory.Localization.Module

/-! Actual principal-open and localization geometry for chart modules of
morphisms to the projective line. No normality or cohomology finiteness
is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (k : Type u) [CommRing k]

/-- The coordinate ratio as an actual section of a projective-line chart. -/
def projectiveLineChartRatio (i : Fin 2) : Γ(projectiveLine k, projectiveLineChart k i) :=
  (projectiveLineChartSectionsEquiv k i).symm (projectiveChartCoordinate k i)

/-- The invertibility locus of the actual chart ratio is exactly the chart overlap. -/
theorem projectiveLineChartRatio_basicOpen (i : Fin 2) :
    (projectiveLine k).basicOpen (projectiveLineChartRatio k i) = projectiveLineOverlap k := by
  let G := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let e := projectiveLineChartIsoSpec k i
  let a := Proj.awayι G (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)
  have he : e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (projectiveChartCoordinate k i) =
      (projectiveLineChart k i).ι ⁻¹ᵁ
        (projectiveLine k).basicOpen (projectiveLineChartRatio k i) := by
    change (Proj.basicOpenToSpec G (MvPolynomial.X i)) ⁻¹ᵁ _ = _
    rw [Proj.basicOpenToSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  have hpre : a ⁻¹ᵁ (projectiveLine k).basicOpen (projectiveLineChartRatio k i) =
      PrimeSpectrum.basicOpen (projectiveChartCoordinate k i) := by
    have h := congrArg (fun W => e.inv ⁻¹ᵁ W) he
    simpa only [← Scheme.Hom.comp_preimage, e, Iso.inv_hom_id,
      Scheme.Hom.id_preimage, projectiveLineChartIsoSpec, a, Proj.awayι, G, projectiveLineChart] using h.symm
  have hother : a ⁻¹ᵁ projectiveLineChart k i.rev =
      PrimeSpectrum.basicOpen (projectiveChartCoordinate k i) := by
    simpa [a, G, projectiveLineChart, projectiveChartCoordinate, Away.isLocalizationElem, pow_one] using
      Proj.awayι_preimage_basicOpen G (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X k i.rev) (by decide : 0 < 1)
  have h := congrArg (fun W => a ''ᵁ W) (hpre.trans hother.symm)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.image_preimage_eq_opensRange_inf] at h
  have hr : a.opensRange = projectiveLineChart k i := Proj.opensRange_awayι ..
  rw [hr, inf_eq_right.mpr (Scheme.basicOpen_le _ _)] at h
  rw [h, projectiveLineOverlap_eq_inf]
  fin_cases i <;> simp [inf_comm]

variable {k} {X : Scheme.{u}}

/-- The actual inverse image of the projective overlap. -/
def finiteMapOverlap (f : X ⟶ projectiveLine k) : X.Opens :=
  f ⁻¹ᵁ projectiveLineOverlap k

/-- The inverse-image overlap lies in either actual inverse-image chart. -/
theorem finiteMapOverlap_le (f : X ⟶ projectiveLine k) (i : Fin 2) :
    finiteMapOverlap f ≤ f ⁻¹ᵁ projectiveLineChart k i :=
  f.preimage_mono (projectiveLineOverlap_le k i)

/-- The pulled-back overlap is the principal open of the pulled-back coordinate ratio. -/
theorem finiteMapOverlap_eq_basicOpen (f : X ⟶ projectiveLine k) (i : Fin 2) :
    finiteMapOverlap f = X.basicOpen (f.app (projectiveLineChart k i) (projectiveLineChartRatio k i)) := by
  rw [finiteMapOverlap, ← projectiveLineChartRatio_basicOpen k i, Scheme.preimage_basicOpen]

/-- The actual ring restriction from an inverse-image chart to the overlap. -/
def finiteMapChartRestriction (f : X ⟶ projectiveLine k) (i : Fin 2) :
    Γ(X, f ⁻¹ᵁ projectiveLineChart k i) →+* Γ(X, finiteMapOverlap f) :=
  (X.presheaf.map (homOfLE (finiteMapOverlap_le f i)).op).hom

/-- For an affine morphism, actual overlap restriction is localization at the actual chart ratio. -/
theorem finiteMapChartRestriction_isLocalization (f : X ⟶ projectiveLine k)
    [IsAffineHom f] (i : Fin 2) :
    letI := (finiteMapChartRestriction f i).toAlgebra
    IsLocalization.Away
      (f.app (projectiveLineChart k i) (projectiveLineChartRatio k i)) Γ(X, finiteMapOverlap f) := by
  exact ((projectiveLineChart_isAffine k i).preimage f).isLocalization_of_eq_basicOpen _
    (homOfLE (finiteMapOverlap_le f i)) (finiteMapOverlap_eq_basicOpen f i)

end Normalizer
