import Normalizer.EtaleRegularity
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Smooth.Flat

/-! Regular local rings of smooth algebras over fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

/-- Prime localizations of an étale algebra over a regular ring are regular.
The algebra map between the localizations is the actual local map. -/
theorem regularLocal_localization_of_etale
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p := q.under R
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq]
    infer_instance
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime p) (Localization.AtPrime q)
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R (Localization.AtPrime p)
      (Localization.AtPrime q)
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).mpr inferInstance
  exact regularLocal_of_flat_unramified (Localization.AtPrime p) (Localization.AtPrime q)

/-- Every prime localization of a smooth algebra over a field is a regular
local ring. Smoothness is used on a genuine affine neighborhood, which is
étale over a finite polynomial algebra; no finite presentation of the prime
localization itself is assumed. -/
theorem regularLocal_localization_of_smooth
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (p : Ideal A) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hfp, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let := hAlg
  let := hTower
  let := hEtale
  let B := Localization.Away f
  let q : Ideal B := p.map (algebraMap A B)
  have hdisj : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp
  have : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B p
      inferInstance hdisj
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    regularLocal_localization_of_etale (MvPolynomial (Fin n) k) B q
  have hunder : q.under A = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) B
      inferInstance hdisj
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hunder] using
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime q) (q.under A))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime p)).toRingEquiv

end Normalizer
