import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Linear dimension loss in the universal-extension argument. All maps and
dimension bounds are explicit hypotheses. Their geometric construction is a
separate obligation; the integers here do not define a curve or a divisor. -/

namespace Normalizer
variable {F V W H T : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W]
  [AddCommGroup H] [Module F H] [FiniteDimensional F H]
  [AddCommGroup T] [Module F T]

/-- An injective extension boundary loses at most the kernel dimension of
the next map. This is the rank estimate behind both degree cases. -/
theorem extension_dimension_loss (A : V →ₗ[F] W) (e : W →ₗ[F] H)
    (s : H →ₗ[F] T) (he : Function.Injective e)
    (hzero : s.comp (e.comp A) = 0) :
    Module.finrank F V ≤ Module.finrank F A.ker + Module.finrank F s.ker := by
  have hker : (e.comp A).ker = A.ker := by
    ext v
    change e (A v) = 0 ↔ A v = 0
    rw [← e.map_zero, he.eq_iff]
  have hrange : (e.comp A).range ≤ s.ker := LinearMap.range_le_ker_iff.mpr hzero
  have hdim := Submodule.finrank_mono hrange
  have hnull := (e.comp A).finrank_range_add_finrank_ker
  rw [hker] at hnull
  omega

/-- The cancellation of the degree term: dim V ≥ g+d−1−h and
dim ker s ≤ d−1 imply dim ker A ≥ g−h. -/
theorem extension_kernel_lower_bound (A : V →ₗ[F] W) (e : W →ₗ[F] H)
    (s : H →ₗ[F] T) (he : Function.Injective e)
    (hzero : s.comp (e.comp A) = 0) (g d h : ℕ) (hd : 1 ≤ d)
    (hsource : g + d - 1 ≤ Module.finrank F V + h)
    (hdivisor : Module.finrank F s.ker ≤ d - 1) :
    g - h ≤ Module.finrank F A.ker := by
  have := extension_dimension_loss A e s he hzero
  omega

/-- The genus-five degree-two branch supplies at least four directions. -/
theorem degree_two_kernel_four (A : V →ₗ[F] W) (e : W →ₗ[F] H)
    (s : H →ₗ[F] T) (he : Function.Injective e)
    (hzero : s.comp (e.comp A) = 0)
    (hsource : 5 ≤ Module.finrank F V)
    (hdivisor : Module.finrank F s.ker ≤ 1) :
    4 ≤ Module.finrank F A.ker := by
  have := extension_dimension_loss A e s he hzero
  omega

end Normalizer
