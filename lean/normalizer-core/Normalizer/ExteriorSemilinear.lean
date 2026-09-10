import Mathlib.LinearAlgebra.ExteriorPower.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

universe u v w z

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module S N]

/-- Exterior powers carry the map induced by a coefficient-changing linear map. -/
noncomputable def exteriorSemilinearMap (n : ℕ) (σ : R →+* S)
    (f : M →ₛₗ[σ] N) : (⋀[R]^n M) →ₛₗ[σ] (⋀[S]^n N) := by
  letI := Module.compHom (⋀[S]^n N) σ
  let a : M [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { toFun := fun v => exteriorPower.ιMulti S n (f ∘ v)
      map_update_add' := by
        intro _ v i x y
        simp only [Function.comp_update, map_add]
        exact (exteriorPower.ιMulti S n).map_update_add (f ∘ v) i (f x) (f y)
      map_update_smul' := by
        intro _ v i r x
        simp only [Function.comp_update, f.map_smulₛₗ]
        exact (exteriorPower.ιMulti S n).map_update_smul (f ∘ v) i (σ r) (f x)
      map_eq_zero_of_eq' := by
        intro v i j h hij
        exact (exteriorPower.ιMulti S n).map_eq_zero_of_eq (f ∘ v)
          (congrArg f h) hij }
  let g := exteriorPower.alternatingMapLinearEquiv a
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := g.map_smul }

@[simp]
theorem exteriorSemilinearMap_ιMulti (n : ℕ) (σ : R →+* S)
    (f : M →ₛₗ[σ] N) (v : Fin n → M) :
    exteriorSemilinearMap n σ f (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (f ∘ v) := by
  let := Module.compHom (⋀[S]^n N) σ
  unfold exteriorSemilinearMap
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- Pure wedges determine a semilinear map out of an exterior power. -/
theorem exteriorSemilinearMap_ext (n : ℕ) (σ : R →+* S)
    {f g : (⋀[R]^n M) →ₛₗ[σ] N}
    (h : ∀ v : Fin n → M, f (exteriorPower.ιMulti R n v) =
      g (exteriorPower.ιMulti R n v)) : f = g := by
  let := Module.compHom N σ
  let f' : (⋀[R]^n M) →ₗ[R] N :=
    { toFun := f, map_add' := f.map_add, map_smul' := f.map_smulₛₗ }
  let g' : (⋀[R]^n M) →ₗ[R] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := g.map_smulₛₗ }
  have heq : f' = g' := exteriorPower.linearMap_ext (by ext v; exact h v)
  exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun heq x)

@[simp]
theorem exteriorSemilinearMap_id (n : ℕ) :
    exteriorSemilinearMap n (RingHom.id R) (LinearMap.id : M →ₗ[R] M) =
      LinearMap.id := by
  apply exteriorSemilinearMap_ext
  intro v
  simp

/-- Exterior maps respect composition of maps and coefficient homomorphisms. -/
theorem exteriorSemilinearMap_comp
    {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    (n : ℕ) (σ : R →+* S) (τ : S →+* T) (υ : R →+* T)
    [RingHomCompTriple σ τ υ]
    (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) :
    exteriorSemilinearMap n υ (g.comp f) =
      (exteriorSemilinearMap n τ g).comp (exteriorSemilinearMap n σ f) := by
  apply exteriorSemilinearMap_ext
  intro v
  simp [Function.comp_def]

end Normalizer
