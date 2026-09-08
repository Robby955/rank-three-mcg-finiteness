import Normalizer.Boundary
import Normalizer.Quotients
import Normalizer.ExtensionDimension

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]

/-- The quotient bracket in the proved coordinate presentation. Its agreement
with matrix commutators is `sem_projection_bracket`. -/
noncomputable def semQuotientBracket (x y : SemQuotient F) : SemQuotient F :=
  semQuotientEquiv.symm (semBracket (semQuotientEquiv x) (semQuotientEquiv y))

/-- Agreement with matrix commutators is `nil_projection_bracket`. -/
noncomputable def nilQuotientBracket (x y : NilQuotient F) : NilQuotient F :=
  nilQuotientEquiv.symm (nilBracket (nilQuotientEquiv x) (nilQuotientEquiv y))

noncomputable def nilCharacter (x : NilQuotient F) : F := nilQuotientEquiv x 0

theorem sem_quotient_no_three (U : Submodule F (SemQuotient F))
    (hlaw : BoundaryLaw U semQuotientBracket (fun _ => 0)) : Module.finrank F U < 3 := by
  let e := semQuotientEquiv (F := F)
  have h : BoundaryLaw (U.map e.toLinearMap) semBracket (fun _ => 0) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have hh := congrArg e (hlaw a ha b hb)
    simpa [e, semQuotientBracket, map_sub, map_smul] using hh
  have hdim := sem_no_three (U.map e.toLinearMap) h
  rwa [e.finrank_map_eq U] at hdim

theorem nil_quotient_no_three (U : Submodule F (NilQuotient F))
    (hlaw : BoundaryLaw U nilQuotientBracket nilCharacter) : Module.finrank F U < 3 := by
  let e := nilQuotientEquiv (F := F)
  have h : BoundaryLaw (U.map e.toLinearMap) nilBracket (fun v => v 0) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have hh := congrArg e (hlaw a ha b hb)
    simpa [e, nilQuotientBracket, nilCharacter, map_sub, map_smul] using hh
  have hdim := nil_no_three (U.map e.toLinearMap) h
  rwa [e.finrank_map_eq U] at hdim

/-- Algebraic boundary obstruction in the semisimple quotient. -/
theorem sem_injective_boundary_obstruction {W : Type*} [AddCommGroup W] [Module F W]
    (boundary : SemQuotient F →ₗ[F] W) (hinj : Function.Injective boundary)
    (U : Submodule F (SemQuotient F))
    (h : ∀ x ∈ U, ∀ y ∈ U, boundary (semQuotientBracket x y) = 0) :
    Module.finrank F U < 3 := by
  apply sem_quotient_no_three
  intro x hx y hy
  apply quotient_boundary_law boundary hinj x y _ 0 0
  simpa using h x hx y hy

/-- Algebraic boundary obstruction in the minimal-nilpotent quotient. -/
theorem nil_injective_boundary_obstruction {W : Type*} [AddCommGroup W] [Module F W]
    (boundary : NilQuotient F →ₗ[F] W) (hinj : Function.Injective boundary)
    (U : Submodule F (NilQuotient F))
    (h : ∀ x ∈ U, ∀ y ∈ U,
      boundary (nilQuotientBracket x y) =
        nilCharacter x • boundary y - nilCharacter y • boundary x) :
    Module.finrank F U < 3 := by
  apply nil_quotient_no_three
  intro x hx y hy
  exact quotient_boundary_law boundary hinj x y _ _ _ (h x hx y hy)

/-- The two eigenvalues required in the manuscript cannot both be one. -/
theorem nil_eigenvalue_conflict (c : F) :
    ¬ ((1 + 3 * c) / 2 = 1 ∧ (1 - 3 * c) / 2 = 1) := by
  rintro ⟨h1, h2⟩
  have h : (1 : F) = 0 := by linear_combination -h1 - h2
  exact one_ne_zero h

section ExtensionApplication
variable {V W H T : Type*}
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W]
  [AddCommGroup H] [Module F H] [FiniteDimensional F H]
  [AddCommGroup T] [Module F T]

/-- The extension estimate excludes an injective realization of its kernel
inside the semisimple normalizer quotient obeying the boundary law. -/
theorem sem_extension_obstruction (A : V →ₗ[F] W) (e : W →ₗ[F] H)
    (s : H →ₗ[F] T) (he : Function.Injective e)
    (hzero : s.comp (e.comp A) = 0) (g d h : ℕ) (hd : 1 ≤ d)
    (hsource : g + d - 1 ≤ Module.finrank F V + h)
    (hdivisor : Module.finrank F s.ker ≤ d - 1) (hthree : 3 ≤ g - h)
    (J : A.ker →ₗ[F] SemQuotient F) (hJ : Function.Injective J)
    (hlaw : BoundaryLaw J.range semQuotientBracket (fun _ => 0)) : False := by
  have hlo := extension_kernel_lower_bound A e s he hzero g d h hd hsource hdivisor
  have hhi := sem_quotient_no_three J.range hlaw
  rw [LinearMap.finrank_range_of_inj hJ] at hhi
  omega

/-- The same extension estimate excludes the minimal-nilpotent quotient. -/
theorem nil_extension_obstruction (A : V →ₗ[F] W) (e : W →ₗ[F] H)
    (s : H →ₗ[F] T) (he : Function.Injective e)
    (hzero : s.comp (e.comp A) = 0) (g d h : ℕ) (hd : 1 ≤ d)
    (hsource : g + d - 1 ≤ Module.finrank F V + h)
    (hdivisor : Module.finrank F s.ker ≤ d - 1) (hthree : 3 ≤ g - h)
    (J : A.ker →ₗ[F] NilQuotient F) (hJ : Function.Injective J)
    (hlaw : BoundaryLaw J.range nilQuotientBracket nilCharacter) : False := by
  have hlo := extension_kernel_lower_bound A e s he hzero g d h hd hsource hdivisor
  have hhi := nil_quotient_no_three J.range hlaw
  rw [LinearMap.finrank_range_of_inj hJ] at hhi
  omega

end ExtensionApplication

end Normalizer
