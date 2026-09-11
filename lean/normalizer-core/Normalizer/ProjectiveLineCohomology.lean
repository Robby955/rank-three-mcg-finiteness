import Normalizer.ProjectiveCoordinates
import Normalizer.TwoAffineSections
import Normalizer.LocallyFreeTransport

/-! The actual first cohomology of the structure sheaf of the projective line.
The proof uses its actual two-chart restriction maps, with no supplied
vanishing or finite-dimensionality hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry
universe u

/-- Every Laurent polynomial is a difference of polynomials in the two opposite coordinates. -/
theorem laurentPolynomial_twoChart_difference (k : Type u) [CommRing k]
    (z : LaurentPolynomial k) :
    ∃ p q : Polynomial k,
      Polynomial.toLaurent p - LaurentPolynomial.invert (Polynomial.toLaurent q) = z := by
  refine z.induction_on' ?_ fun n a => ?_
  · rintro z w ⟨p, q, hpq⟩ ⟨r, s, hrs⟩
    refine ⟨p + r, q + s, ?_⟩
    simp only [map_add]
    rw [add_sub_add_comm, hpq, hrs]
  · rcases n with n | n
    · exact ⟨Polynomial.C a * Polynomial.X ^ n, 0, by simp⟩
    · refine ⟨0, -(Polynomial.C a * Polynomial.X ^ (n + 1)), ?_⟩
      simp [Int.negSucc_eq]

/-- Every actual overlap section is a difference of sections from the two actual charts. -/
theorem projectiveLineOverlap_sections_difference (k : Type u) [CommRing k]
    (z : Γ(projectiveLine k, projectiveLineOverlap k)) :
    ∃ s : Γ(projectiveLine k, projectiveLineChart k 0),
    ∃ t : Γ(projectiveLine k, projectiveLineChart k 1),
      (projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k 0)).op s -
        (projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k 1)).op t = z := by
  obtain ⟨p, q, hpq⟩ := laurentPolynomial_twoChart_difference k
    (projectiveLineOverlapSectionsLaurentEquiv k z)
  refine ⟨(projectiveLineChartSectionsPolynomialEquiv k 0).symm p,
    (projectiveLineChartSectionsPolynomialEquiv k 1).symm q, ?_⟩
  apply (projectiveLineOverlapSectionsLaurentEquiv k).injective
  rw [map_sub, projectiveLineSections_restrict_zero, projectiveLineSections_restrict_one,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact hpq

/-- The actual structure sheaf is locally free of rank one, via the one-generator free sheaf. -/
theorem schemeUnit_isLocallyFree (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsLocallyFree :=
  isLocallyFree_of_iso (E := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})
    (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))

/-- The standard two-chart cover expressed as a binary union. -/
theorem projectiveLineChart_sup (k : Type u) [CommRing k] :
    projectiveLineChart k 0 ⊔ projectiveLineChart k 1 = ⊤ := by
  apply top_unique
  rw [← projectiveLineChart_cover k]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The first cohomology of the actual structure sheaf of the actual Proj projective line vanishes. -/
theorem projectiveLine_unit_H1_subsingleton (k : Type u) [Field k] :
    Subsingleton (Sheaf.H ((schemeModulesToAbelianSheaves (projectiveLine k)).obj
      (SheafOfModules.unit (projectiveLine k).ringCatSheaf)) 1) := by
  let X := projectiveLine k
  let F := SheafOfModules.unit X.ringCatSheaf
  have : F.IsLocallyFree := schemeUnit_isLocallyFree X
  let U := projectiveLineChart k 0
  let V := projectiveLineChart k 1
  let p := projectiveLineToSpec k
  have hc := projectiveLineChart_sup k
  have hz : ∀ z : Γ(F, U ⊓ V), twoOpenSectionδ p U V hc F z = 0 := by
    intro z
    apply (twoOpenSectionδ_eq_zero_iff p U V hc F z).mpr
    have h : ∀ (W : (projectiveLine k).Opens) (h₀ : W ≤ U) (h₁ : W ≤ V),
        W = projectiveLineOverlap k → ∀ z : Γ(projectiveLine k, W),
        ∃ s : Γ(projectiveLine k, U), ∃ t : Γ(projectiveLine k, V),
          (projectiveLine k).presheaf.map (homOfLE h₀).op s -
            (projectiveLine k).presheaf.map (homOfLE h₁).op t = z := by
      intro W h₀ h₁ hW
      subst W
      exact projectiveLineOverlap_sections_difference k
    exact h _ inf_le_left inf_le_right (projectiveLineOverlap_eq_inf k).symm z
  have hs := twoOpenSectionδ_surjective p U V hc F
    (projectiveLineChart_isAffine k 0) (projectiveLineChart_isAffine k 1)
  refine ⟨fun a b => ?_⟩
  obtain ⟨s, rfl⟩ := hs a
  obtain ⟨t, rfl⟩ := hs b
  rw [hz, hz]

/-- Actual structure-sheaf H¹ on the projective line is finite over the structure field. -/
theorem projectiveLine_unit_H1_finite (k : Type u) [Field k] :
    letI := schemeModuleCohomologyModule (projectiveLineToSpec k)
      (SheafOfModules.unit (projectiveLine k).ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves (projectiveLine k)).obj
      (SheafOfModules.unit (projectiveLine k).ringCatSheaf)) 1) := by
  let := schemeModuleCohomologyModule (projectiveLineToSpec k)
    (SheafOfModules.unit (projectiveLine k).ringCatSheaf) 1
  have := projectiveLine_unit_H1_subsingleton k
  infer_instance

end Normalizer
