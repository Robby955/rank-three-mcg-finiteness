import Normalizer.AffinePrincipalLocalization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Degree-one denominator clearing on finite principal affine covers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u

variable {R : CommRingCat.{u}}

/-- Restriction in an R-module sheaf, retained as an R-linear map. -/
abbrev affineModuleRestrict
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R))
    {U V : Opens (PrimeSpectrum.Top R)} (h : V ≤ U) :=
  (F.obj.map (homOfLE h).op).hom

@[simp]
theorem affineModuleRestrict_comp
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R))
    {U V W : Opens (PrimeSpectrum.Top R)} (h : W ≤ V) (k : V ≤ U)
    (x : F.obj.obj (op U)) :
    affineModuleRestrict F h (affineModuleRestrict F k x) =
      affineModuleRestrict F (h.trans k) x := by
  change (F.obj.map (homOfLE k).op ≫ F.obj.map (homOfLE h).op) x = _
  rw [← F.obj.map_comp, ← op_comp]
  rfl

/-- Every degree-one cocycle on a finite principal affine cover of a localizing
module sheaf is a coboundary. The sections and restrictions are those of the
actual sheaf; no Čech exactness premise is used. -/
theorem localizingSheaf_cechOne_eq_coboundary
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R)) (hF : IsLocalizing F)
    {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, F.obj.obj (op (PrimeSpectrum.basicOpen (f i) ⊓
      PrimeSpectrum.basicOpen (f j))))
    (hc : ∀ i k j,
      affineModuleRestrict F (inf_le_inf_right _ inf_le_left) (c i j) -
        affineModuleRestrict F (inf_le_inf_right _ inf_le_right) (c k j) =
      affineModuleRestrict F (inf_le_left :
        (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f k)) ⊓
          PrimeSpectrum.basicOpen (f j) ≤ _) (c i k)) :
    ∃ b : ∀ i, F.obj.obj (op (PrimeSpectrum.basicOpen (f i))),
      ∀ i k, affineModuleRestrict F inf_le_left (b i) -
        affineModuleRestrict F inf_le_right (b k) = c i k := by
  classical
  let U := fun i => PrimeSpectrum.basicOpen (f i)
  have hsurj (i j : ι) : ∃ (n : ℕ) (t : F.obj.obj (op (U i))),
      f j ^ n • c i j = affineModuleRestrict F inf_le_left t := by
    have := localizingSheaf_principalRestriction F hF (f i) (f j)
    exact IsLocalizedModule.Away.surj _ (f j) (c i j)
  choose n t₀ ht₀ using hsurj
  let N := ⨆ p : ι × ι, n p.1 p.2
  have hn (i j : ι) : n i j ≤ N := le_ciSup (Finite.bddAbove_range (fun p : ι × ι => n p.1 p.2)) (i, j)
  let t (i j : ι) := f j ^ (N - n i j) • t₀ i j
  have ht (i j : ι) : affineModuleRestrict F inf_le_left (t i j) =
      f j ^ N • c i j := by
    dsimp only [t]
    rw [map_smul, ← ht₀, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hn i j)]
  let d (i k j : ι) : F.obj.obj (op (U i ⊓ U k)) :=
    affineModuleRestrict F inf_le_left (t i j) -
      affineModuleRestrict F inf_le_right (t k j) - f j ^ N • c i k
  have hd (i k j : ι) : affineModuleRestrict F
      (inf_le_left : (U i ⊓ U k) ⊓ U j ≤ U i ⊓ U k) (d i k j) = 0 := by
    have hti := congrArg
      (affineModuleRestrict F (inf_le_inf_right (U j)
        (inf_le_left : U i ⊓ U k ≤ U i))) (ht i j)
    have htk := congrArg
      (affineModuleRestrict F (inf_le_inf_right (U j)
        (inf_le_right : U i ⊓ U k ≤ U k))) (ht k j)
    simp only [map_smul] at hti htk
    rw [affineModuleRestrict_comp (R := R) F] at hti htk
    dsimp only [d]
    simp only [map_sub, map_smul, affineModuleRestrict_comp]
    rw [hti, htk, ← smul_sub, hc i k j, sub_self]
  have hkill (i k j : ι) : ∃ m : ℕ, f j ^ m • d i k j = 0 := by
    have : IsLocalizedModule.Away (f j)
        (affineModuleRestrict F
          (inf_le_left : (U i ⊓ U k) ⊓ U j ≤ U i ⊓ U k)) := by
      dsimp only [U]
      rw [← PrimeSpectrum.basicOpen_mul]
      exact localizingSheaf_principalRestriction F hF (f i * f k) (f j)
    obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f j)
      (f := affineModuleRestrict F
        (inf_le_left : (U i ⊓ U k) ⊓ U j ≤ U i ⊓ U k))
      (y := 0) (by simpa using hd i k j)
    exact ⟨m, by simpa using hm⟩
  choose m hm using hkill
  let K := ⨆ p : ι × ι × ι, m p.1 p.2.1 p.2.2
  have hK (i k j : ι) : f j ^ K • d i k j = 0 := by
    have hle : m i k j ≤ K := le_ciSup (Finite.bddAbove_range (fun p : ι × ι × ι => m p.1 p.2.1 p.2.2)) (i, k, j)
    have heq : K = (K - m i k j) + m i k j := (Nat.sub_add_cancel hle).symm
    rw [heq, pow_add, mul_smul, hm, smul_zero]
  let t' (i j : ι) := f j ^ K • t i j
  have ht' (i k j : ι) :
      affineModuleRestrict F inf_le_left (t' i j) -
        affineModuleRestrict F inf_le_right (t' k j) =
      f j ^ (N + K) • c i k := by
    have hh := hK i k j
    dsimp only [d] at hh
    dsimp only [t']
    simp only [map_smul]
    rw [← smul_sub]
    rw [smul_sub, sub_eq_zero] at hh
    rw [hh, ← mul_smul, ← pow_add, Nat.add_comm K N]
  have hpow : Ideal.span (Set.range fun j => f j ^ (N + K)) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def] using Ideal.span_pow_eq_top (Set.range f) hf (N + K)
  obtain ⟨a, ha⟩ : ∃ a : ι → R, ∑ j, a j • f j ^ (N + K) = 1 :=
    (Submodule.mem_span_range_iff_exists_fun R).mp (by change (1 : R) ∈ Ideal.span (Set.range fun j => f j ^ (N + K)); rw [hpow]; trivial)
  refine ⟨fun i => ∑ j, a j • t' i j, fun i k => ?_⟩
  simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  calc
    _ = ∑ j, (a j * f j ^ (N + K)) • c i k := by
      apply Finset.sum_congr rfl
      intro j _
      exact (congrArg (fun z => a j • z) (ht' i k j)).trans
        (mul_smul (a j) (f j ^ (N + K)) (c i k)).symm
    _ = (∑ j, a j • f j ^ (N + K)) • c i k := (Finset.sum_smul ..).symm
    _ = c i k := by rw [ha, one_smul]

/-- The finite-principal-cover degree-one coboundary theorem for the actual
associated sheaf of any module over any commutative ring. -/
theorem tilde_cechOne_eq_coboundary (M : ModuleCat.{u} R)
    {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, (modulesSpecToSheaf.obj (tilde M)).obj.obj
      (op (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j))))
    (hc : ∀ i k j,
      affineModuleRestrict _ (inf_le_inf_right _ inf_le_left) (c i j) -
        affineModuleRestrict _ (inf_le_inf_right _ inf_le_right) (c k j) =
      affineModuleRestrict _ (inf_le_left :
        (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f k)) ⊓
          PrimeSpectrum.basicOpen (f j) ≤ _) (c i k)) :
    ∃ b : ∀ i, (modulesSpecToSheaf.obj (tilde M)).obj.obj
        (op (PrimeSpectrum.basicOpen (f i))),
      ∀ i k, affineModuleRestrict _ inf_le_left (b i) -
        affineModuleRestrict _ inf_le_right (b k) = c i k :=
  localizingSheaf_cechOne_eq_coboundary _ (isLocalizing_tilde M) f hf c hc

end Normalizer
