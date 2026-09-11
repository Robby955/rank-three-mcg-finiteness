import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Away

/-! Localization of actual associated-sheaf restrictions between principal opens.
These are the denominator-clearing inputs for the affine degree-one proof. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u

/-- If M -> N localizes at a and M -> P localizes at a*b, then the
compatible map N -> P localizes at b. -/
theorem localizedModuleAway_cancel_left
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (a b : R) (f : M →ₗ[R] N) (g : M →ₗ[R] P) (h : N →ₗ[R] P)
    [IsLocalizedModule.Away a f] [IsLocalizedModule.Away (a * b) g]
    (hc : h.comp f = g) : IsLocalizedModule.Away b h := by
  have haN := IsLocalizedModule.Away.isUnit_algebraMap f a
  have habP := IsLocalizedModule.Away.isUnit_algebraMap g (a * b)
  rw [map_mul, (Algebra.commute_algebraMap_left a
    (algebraMap R (Module.End R P) b)).isUnit_mul_iff] at habP
  refine IsLocalizedModule.Away.mk_of_addCommGroup habP.2 ?_ ?_
  · intro x
    obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj g (a * b) x
    have han : IsUnit (algebraMap R (Module.End R N) (a ^ n)) := by
      simpa only [map_pow] using haN.pow n
    obtain ⟨t, ht⟩ := ((Module.End.isUnit_iff _).mp han).surjective (f m)
    refine ⟨n, t, ?_⟩
    have han' : IsUnit (algebraMap R (Module.End R P) (a ^ n)) := by
      simpa only [map_pow] using habP.1.pow n
    apply ((Module.End.isUnit_iff _).mp han').injective
    change a ^ n • (b ^ n • x) = a ^ n • h t
    change a ^ n • t = f m at ht
    rw [← h.map_smul, ht, ← LinearMap.comp_apply, LinearMap.congr_fun hc,
      ← mul_smul, ← mul_pow, hm]
  · intro x hx
    obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj f a x
    have hg : g m = 0 := by
      rw [← LinearMap.congr_fun hc, LinearMap.comp_apply, ← hm, h.map_smul, hx, smul_zero]
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (a * b)
      (f := g) (y := 0) (by simpa using hg)
    simp only [smul_zero] at hk
    refine ⟨k, ?_⟩
    have hank : IsUnit (algebraMap R (Module.End R N) (a ^ (n + k))) := by
      simpa only [map_pow] using haN.pow (n + k)
    apply ((Module.End.isUnit_iff _).mp hank).injective
    change a ^ (n + k) • (b ^ k • x) = a ^ (n + k) • (0 : N)
    rw [smul_zero]
    calc
      a ^ (n + k) • (b ^ k • x) = (a * b) ^ k • (a ^ n • x) := by
        simp only [← mul_smul, pow_add, mul_pow]
        congr 1
        ring
      _ = f ((a * b) ^ k • m) := by rw [hm, f.map_smul]
      _ = 0 := by rw [hk, map_zero]

variable {R : CommRingCat.{u}}

/-- For a localizing module sheaf on Spec R, restriction from D(a) to
D(a) intersect D(b) is the actual module localization away from b. -/
theorem localizingSheaf_principalRestriction
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R))
    (hF : IsLocalizing F) (a b : R) :
    IsLocalizedModule.Away b
      (F.obj.map (homOfLE
        (inf_le_left : PrimeSpectrum.basicOpen a ⊓ PrimeSpectrum.basicOpen b ≤
          PrimeSpectrum.basicOpen a)).op).hom := by
  let f := (F.obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom
  let g := (F.obj.map (PrimeSpectrum.basicOpen a ⊓ PrimeSpectrum.basicOpen b).leTop.op).hom
  have : IsLocalizedModule.Away a f := hF a
  have : IsLocalizedModule.Away (a * b) g := by
    dsimp only [g]
    rw [← PrimeSpectrum.basicOpen_mul]
    exact hF (a * b)
  apply localizedModuleAway_cancel_left a b f g
  change (F.obj.map (PrimeSpectrum.basicOpen a).leTop.op ≫
    F.obj.map (homOfLE inf_le_left).op).hom = _
  rw [← F.obj.map_comp, ← op_comp]
  rfl

/-- Actual associated sheaves have the principal-open localization property;
no additional localization or quasi-coherence premise is supplied. -/
theorem tilde_principalRestriction (M : ModuleCat.{u} R) (a b : R) :
    IsLocalizedModule.Away b
      ((modulesSpecToSheaf.obj (tilde M)).obj.map (homOfLE
        (inf_le_left : PrimeSpectrum.basicOpen a ⊓ PrimeSpectrum.basicOpen b ≤
          PrimeSpectrum.basicOpen a)).op).hom :=
  localizingSheaf_principalRestriction _ (isLocalizing_tilde M) a b

end Normalizer
