import Normalizer.ProjectiveLine
import Mathlib.Algebra.Polynomial.Laurent

/-! Polynomial coordinates on the actual homogeneous-localization charts
of the projective line. The coordinate is the ratio of the other variable
to the variable inverted on the chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (k : Type u) [CommRing k]

/-- The actual ratio X_rev(i)/X_i in the standard homogeneous-localization chart. -/
def projectiveChartCoordinate (i : Fin 2) :
    Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) :=
  Away.mk _ (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X i.rev)
    (by simpa using MvPolynomial.isHomogeneous_X k i.rev)

/-- Polynomial evaluation at the actual chart ratio, with actual constant coefficients. -/
def projectiveChartFromPolynomial (i : Fin 2) :
    Polynomial k →+* Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) :=
  Polynomial.eval₂RingHom
    ((fromZeroRingHom _ _).comp (projectiveLineZeroConstants k)) (projectiveChartCoordinate k i)

/-- Dehomogenization of the homogeneous polynomial ring on the chosen chart. -/
def projectiveChartPolynomialEval (i : Fin 2) : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

/-- The actual chart maps to polynomials by setting its denominator coordinate to one. -/
def projectiveChartToPolynomial (i : Fin 2) :
    Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) →+* Polynomial k :=
  (Localization.awayLift (projectiveChartPolynomialEval k i) (MvPolynomial.X i)
    (by simp [projectiveChartPolynomialEval])).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X i)))

/-- A homogeneous fraction p/X_i^n dehomogenizes to p with X_i set to one. -/
theorem projectiveChartToPolynomial_mk (i : Fin 2) (n : ℕ) (p : MvPolynomial (Fin 2) k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k (n • 1)) :
    projectiveChartToPolynomial k i (Away.mk _ (MvPolynomial.isHomogeneous_X k i) n p hp) =
      projectiveChartPolynomialEval k i p := by
  unfold projectiveChartToPolynomial
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ 1
    (by simp [projectiveChartPolynomialEval]) n]
  simp

/-- The actual coordinate ratio is sent to the polynomial variable. -/
theorem projectiveChartToPolynomial_coordinate (i : Fin 2) :
    projectiveChartToPolynomial k i (projectiveChartCoordinate k i) = Polynomial.X := by
  rw [projectiveChartCoordinate, projectiveChartToPolynomial_mk]
  fin_cases i <;> simp [projectiveChartPolynomialEval]

/-- The composite chart evaluation fixes every coefficient polynomial. -/
theorem projectiveChartToPolynomial_from_C (i : Fin 2) (a : k) :
    projectiveChartToPolynomial k i (projectiveChartFromPolynomial k i (Polynomial.C a)) =
      Polynomial.C a := by
  simp only [projectiveChartFromPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  change projectiveChartToPolynomial k i
    (Away.mk _ (MvPolynomial.isHomogeneous_X k i) 0 (MvPolynomial.C a)
      (MvPolynomial.isHomogeneous_C (Fin 2) a)) = _
  rw [projectiveChartToPolynomial_mk]
  simp [projectiveChartPolynomialEval]

/-- Dehomogenization is a left inverse of evaluation at the actual chart ratio. -/
theorem projectiveChartToPolynomial_leftInverse (i : Fin 2) :
    Function.LeftInverse (projectiveChartToPolynomial k i) (projectiveChartFromPolynomial k i) := by
  have h : (projectiveChartToPolynomial k i).comp (projectiveChartFromPolynomial k i) =
      RingHom.id (Polynomial k) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact projectiveChartToPolynomial_from_C k i a
    · simpa [projectiveChartFromPolynomial] using projectiveChartToPolynomial_coordinate k i
  exact fun p => congrArg (fun f : Polynomial k →+* Polynomial k => f p) h

/-- Every homogeneous monomial fraction on the chart is a power of its actual ratio. -/
theorem projectiveChart_monomial_fraction (i : Fin 2) (n : ℕ) (a : Fin 2 → ℕ)
    (ha : ∑ j, a j • (1 : ℕ) = n • 1) :
    Away.mk (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.isHomogeneous_X k i) n (∏ j, MvPolynomial.X j ^ a j)
      (ha ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun j _ => MvPolynomial.isHomogeneous_X k j) =
      projectiveChartCoordinate k i ^ a i.rev := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_pow, projectiveChartCoordinate,
    Localization.mk_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  have hn : a 0 + a 1 = n := by simpa [Fin.sum_univ_two] using ha
  subst n
  fin_cases i <;>
    simp [Fin.prod_univ_two, pow_add] <;> ring

/-- The actual chart ratio generates every homogeneous-localization element as a polynomial. -/
theorem projectiveChartFromPolynomial_surjective (i : Fin 2) :
    Function.Surjective (projectiveChartFromPolynomial k i) := by
  let G := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let H := Away G (MvPolynomial.X i)
  let S : Submodule (G 0) H :=
    { carrier := Set.range (projectiveChartFromPolynomial k i)
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        exact ⟨p + q, map_add _ p q⟩
      smul_mem' := by
        rintro a _ ⟨p, rfl⟩
        refine ⟨Polynomial.C ((projectiveLineZeroEquiv k).symm a) * p, ?_⟩
        rw [map_mul]
        simp only [projectiveChartFromPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          RingHom.comp_apply]
        change fromZeroRingHom G _ ((projectiveLineZeroEquiv k)
          ((projectiveLineZeroEquiv k).symm a)) * _ =
            fromZeroRingHom G _ a * _
        rw [RingEquiv.apply_symm_apply] }
  have hs : S = ⊤ := by
    apply top_unique
    rw [← Away.span_mk_prod_pow_eq_top (MvPolynomial.isHomogeneous_X k i)
      MvPolynomial.X (projectiveLine_adjoin_variables k) (fun _ => (1 : ℕ))
      (fun j => MvPolynomial.isHomogeneous_X k j)]
    apply Submodule.span_le.mpr
    rintro z ⟨n, a, ha, rfl⟩
    change ∃ p, projectiveChartFromPolynomial k i p = _
    refine ⟨Polynomial.X ^ a i.rev, ?_⟩
    rw [projectiveChart_monomial_fraction k i n a ha]
    simp [projectiveChartFromPolynomial]
  intro z
  exact (show z ∈ S from hs ▸ Submodule.mem_top)

/-- Dehomogenization is bijective on the actual chart ring. -/
theorem projectiveChartToPolynomial_bijective (i : Fin 2) :
    Function.Bijective (projectiveChartToPolynomial k i) := by
  have hl := projectiveChartToPolynomial_leftInverse k i
  constructor
  · intro x y h
    obtain ⟨p, rfl⟩ := projectiveChartFromPolynomial_surjective k i x
    obtain ⟨q, rfl⟩ := projectiveChartFromPolynomial_surjective k i y
    rw [hl p, hl q] at h
    exact congrArg (projectiveChartFromPolynomial k i) h
  · exact fun p => ⟨projectiveChartFromPolynomial k i p, hl p⟩

/-- The explicit polynomial coordinate isomorphism on either actual standard chart. -/
def projectiveChartPolynomialEquiv (i : Fin 2) :
    Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) ≃+* Polynomial k :=
  RingEquiv.ofBijective (projectiveChartToPolynomial k i) (projectiveChartToPolynomial_bijective k i)

/-- The actual homogeneous localization on the intersection of the standard charts. -/
abbrev projectiveOverlapRing :=
  Away (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

/-- The product defining the overlap can be ordered from either chart. -/
theorem projectiveOverlap_product (i : Fin 2) :
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) =
      MvPolynomial.X i * MvPolynomial.X i.rev := by
  fin_cases i <;> simp [mul_comm]

/-- The actual homogeneous-localization restriction from either chart to the overlap. -/
def projectiveChartToOverlap (i : Fin 2) :
    Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) →+*
      projectiveOverlapRing k :=
  awayMap _ (MvPolynomial.isHomogeneous_X k i.rev) (projectiveOverlap_product k i)

/-- The overlap is the localization of either actual chart at its coordinate ratio. -/
theorem projectiveOverlap_isLocalization (i : Fin 2) :
    letI := (projectiveChartToOverlap k i).toAlgebra
    IsLocalization.Away (projectiveChartCoordinate k i) (projectiveOverlapRing k) := by
  simpa [projectiveChartCoordinate, Away.isLocalizationElem, pow_one] using
    Away.isLocalization_mul (MvPolynomial.isHomogeneous_X k i)
      (MvPolynomial.isHomogeneous_X k i.rev) (projectiveOverlap_product k i) (by decide : 1 ≠ 0)

/-- The chart coordinate isomorphism sends the inverted powers to powers of the polynomial variable. -/
theorem projectiveChartPolynomialEquiv_powers (i : Fin 2) :
    (Submonoid.powers (projectiveChartCoordinate k i)).map
      (projectiveChartPolynomialEquiv k i).toMonoidHom =
        Submonoid.powers (Polynomial.X : Polynomial k) := by
  rw [Submonoid.map_powers]
  congr 1
  exact projectiveChartToPolynomial_coordinate k i

/-- The overlap is the actual Laurent polynomial ring, oriented by X_1/X_0. -/
def projectiveOverlapLaurentEquiv : projectiveOverlapRing k ≃+* LaurentPolynomial k :=
  letI := (projectiveChartToOverlap k 0).toAlgebra
  letI := projectiveOverlap_isLocalization k 0
  IsLocalization.ringEquivOfRingEquiv _ _ (projectiveChartPolynomialEquiv k 0)
    (projectiveChartPolynomialEquiv_powers k 0)

/-- Restriction from the first chart is the usual inclusion of polynomials into Laurent polynomials. -/
theorem projectiveOverlapLaurentEquiv_restrict_zero
    (x : Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (0 : Fin 2))) :
    projectiveOverlapLaurentEquiv k (projectiveChartToOverlap k 0 x) =
      Polynomial.toLaurent (projectiveChartPolynomialEquiv k 0 x) := by
  let := (projectiveChartToOverlap k 0).toAlgebra
  let := projectiveOverlap_isLocalization k 0
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

/-- The two actual chart ratios multiply to one after restriction to their overlap. -/
theorem projectiveOverlap_coordinate_mul :
    projectiveChartToOverlap k 0 (projectiveChartCoordinate k 0) *
      projectiveChartToOverlap k 1 (projectiveChartCoordinate k 1) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, projectiveChartToOverlap,
    projectiveChartCoordinate, awayMap_mk, Away.val_mk, HomogeneousLocalization.val_one]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- The second chart coordinate restricts to the inverse Laurent variable. -/
theorem projectiveOverlapLaurentEquiv_coordinate_one :
    projectiveOverlapLaurentEquiv k
      (projectiveChartToOverlap k 1 (projectiveChartCoordinate k 1)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (projectiveOverlapLaurentEquiv k) (projectiveOverlap_coordinate_mul k)
  rw [map_mul, map_one, projectiveOverlapLaurentEquiv_restrict_zero] at h
  change Polynomial.toLaurent (projectiveChartToPolynomial k 0 (projectiveChartCoordinate k 0)) * _ = 1 at h
  rw [projectiveChartToPolynomial_coordinate, Polynomial.toLaurent_X] at h
  let z := projectiveOverlapLaurentEquiv k
    (projectiveChartToOverlap k 1 (projectiveChartCoordinate k 1))
  change z = _
  calc
    z = LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 * z) := by
      rw [← mul_assoc, ← LaurentPolynomial.T_add]
      simp
    _ = LaurentPolynomial.T (-1) := by rw [h, mul_one]

/-- Both chart restrictions agree on their actual constant coefficients. -/
theorem projectiveChartToOverlap_from_C (i : Fin 2) (a : k) :
    projectiveChartToOverlap k i (projectiveChartFromPolynomial k i (Polynomial.C a)) =
      fromZeroRingHom _ _ (projectiveLineZeroConstants k a) := by
  simp only [projectiveChartFromPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.comp_apply, projectiveChartToOverlap, awayMap_fromZeroRingHom]

/-- Restricting a polynomial from the second chart replaces its variable by the inverse Laurent variable. -/
theorem projectiveOverlapLaurentEquiv_from_one (p : Polynomial k) :
    projectiveOverlapLaurentEquiv k
      (projectiveChartToOverlap k 1 (projectiveChartFromPolynomial k 1 p)) =
        LaurentPolynomial.invert (Polynomial.toLaurent p) := by
  have h : (projectiveOverlapLaurentEquiv k).toRingHom.comp
      ((projectiveChartToOverlap k 1).comp (projectiveChartFromPolynomial k 1)) =
        LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      change projectiveOverlapLaurentEquiv k
        (projectiveChartToOverlap k 1 (projectiveChartFromPolynomial k 1 (Polynomial.C a))) = _
      rw [projectiveChartToOverlap_from_C, ← projectiveChartToOverlap_from_C k 0 a,
        projectiveOverlapLaurentEquiv_restrict_zero]
      change Polynomial.toLaurent
        (projectiveChartToPolynomial k 0 (projectiveChartFromPolynomial k 0 (Polynomial.C a))) = _
      rw [projectiveChartToPolynomial_from_C]
      simp
    · simpa [projectiveChartFromPolynomial] using projectiveOverlapLaurentEquiv_coordinate_one k
  exact congrArg (fun f : Polynomial k →+* LaurentPolynomial k => f p) h

/-- Restriction from the second actual chart is polynomial inclusion followed by Laurent inversion. -/
theorem projectiveOverlapLaurentEquiv_restrict_one
    (x : Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X (1 : Fin 2))) :
    projectiveOverlapLaurentEquiv k (projectiveChartToOverlap k 1 x) =
      LaurentPolynomial.invert (Polynomial.toLaurent (projectiveChartPolynomialEquiv k 1 x)) := by
  obtain ⟨p, rfl⟩ := projectiveChartFromPolynomial_surjective k 1 x
  change _ = LaurentPolynomial.invert (Polynomial.toLaurent
    (projectiveChartToPolynomial k 1 (projectiveChartFromPolynomial k 1 p)))
  rw [projectiveChartToPolynomial_leftInverse]
  exact projectiveOverlapLaurentEquiv_from_one k p

/-- The actual open underlying the Laurent overlap. -/
def projectiveLineOverlap : (projectiveLine k).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

/-- The Laurent overlap open is the intersection of the two standard chart opens. -/
theorem projectiveLineOverlap_eq_inf :
    projectiveLineOverlap k = projectiveLineChart k 0 ⊓ projectiveLineChart k 1 :=
  Proj.basicOpen_mul _ _ _

/-- The actual overlap inclusion into either standard chart. -/
theorem projectiveLineOverlap_le (i : Fin 2) :
    projectiveLineOverlap k ≤ projectiveLineChart k i :=
  Proj.basicOpen_mono _ _ _ ⟨_, projectiveOverlap_product k i⟩

/-- The actual chart sections are the homogeneous-localization ring. -/
def projectiveLineChartSectionsEquiv (i : Fin 2) :
    Γ(projectiveLine k, projectiveLineChart k i) ≃+*
      Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) :=
  (Iso.commRingCatIsoToRingEquiv
    (Proj.basicOpenIsoAway _ _ (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1))).symm

/-- The actual overlap sections are the homogeneous localization at X_0 X_1. -/
def projectiveLineOverlapSectionsEquiv :
    Γ(projectiveLine k, projectiveLineOverlap k) ≃+* projectiveOverlapRing k :=
  (Iso.commRingCatIsoToRingEquiv (Proj.basicOpenIsoAway _ _
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2))) (by decide : 0 < 1 + 1))).symm

/-- Actual sheaf restriction agrees with the homogeneous-localization restriction map. -/
theorem projectiveLineSections_restrict (i : Fin 2)
    (s : Γ(projectiveLine k, projectiveLineChart k i)) :
    projectiveLineOverlapSectionsEquiv k
      ((projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k i)).op s) =
        projectiveChartToOverlap k i (projectiveLineChartSectionsEquiv k i s) := by
  apply (projectiveLineOverlapSectionsEquiv k).symm.injective
  rw [RingEquiv.symm_apply_apply]
  have h := congrArg (fun f : CommRingCat.of
      (Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i)) ⟶
        Γ(projectiveLine k, projectiveLineOverlap k) =>
          f (projectiveLineChartSectionsEquiv k i s))
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.isHomogeneous_X k i.rev) (projectiveOverlap_product k i))
  change (projectiveLineOverlapSectionsEquiv k).symm
    (projectiveChartToOverlap k i (projectiveLineChartSectionsEquiv k i s)) =
      (projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k i)).op
        ((projectiveLineChartSectionsEquiv k i).symm (projectiveLineChartSectionsEquiv k i s)) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h.symm

/-- Polynomial coordinates on the actual section ring of either chart. -/
def projectiveLineChartSectionsPolynomialEquiv (i : Fin 2) :
    Γ(projectiveLine k, projectiveLineChart k i) ≃+* Polynomial k :=
  (projectiveLineChartSectionsEquiv k i).trans (projectiveChartPolynomialEquiv k i)

/-- Laurent coordinates on the actual section ring of the chart intersection. -/
def projectiveLineOverlapSectionsLaurentEquiv :
    Γ(projectiveLine k, projectiveLineOverlap k) ≃+* LaurentPolynomial k :=
  (projectiveLineOverlapSectionsEquiv k).trans (projectiveOverlapLaurentEquiv k)

/-- In actual section coordinates, the first restriction is the usual polynomial inclusion. -/
theorem projectiveLineSections_restrict_zero
    (s : Γ(projectiveLine k, projectiveLineChart k 0)) :
    projectiveLineOverlapSectionsLaurentEquiv k
      ((projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k 0)).op s) =
        Polynomial.toLaurent (projectiveLineChartSectionsPolynomialEquiv k 0 s) := by
  change projectiveOverlapLaurentEquiv k (projectiveLineOverlapSectionsEquiv k _) = _
  rw [projectiveLineSections_restrict, projectiveOverlapLaurentEquiv_restrict_zero]
  rfl

/-- In actual section coordinates, the second restriction inverts the Laurent variable. -/
theorem projectiveLineSections_restrict_one
    (s : Γ(projectiveLine k, projectiveLineChart k 1)) :
    projectiveLineOverlapSectionsLaurentEquiv k
      ((projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k 1)).op s) =
        LaurentPolynomial.invert
          (Polynomial.toLaurent (projectiveLineChartSectionsPolynomialEquiv k 1 s)) := by
  change projectiveOverlapLaurentEquiv k (projectiveLineOverlapSectionsEquiv k _) = _
  rw [projectiveLineSections_restrict, projectiveOverlapLaurentEquiv_restrict_one]
  rfl

end Normalizer
