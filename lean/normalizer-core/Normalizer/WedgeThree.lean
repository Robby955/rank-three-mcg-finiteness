import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# Two-fold exterior products in dimension three

The linear algebra behind the rank-two section estimate uses the actual
second exterior power. The curve degree estimates and construction of the
line subsheaf from two sections remain separate geometric inputs.
-/

namespace Normalizer

set_option backward.isDefEq.respectTransparency false

open Module

variable {F A T : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup T] [Module F T]

/-- The actual two-fold exterior product. -/
noncomputable def wedgeTwo (u v : A) : ⋀[F]^2 A :=
  exteriorPower.ιMulti F 2 ![u, v]

private theorem wedgeTwo_add_left (u v w : A) :
    wedgeTwo (F := F) (u + v) w = wedgeTwo u w + wedgeTwo v w :=
  (exteriorPower.ιMulti F 2).map_vecCons_add _ _ _

private theorem wedgeTwo_smul_left (a : F) (u v : A) :
    wedgeTwo (F := F) (a • u) v = a • wedgeTwo u v :=
  (exteriorPower.ιMulti F 2).map_vecCons_smul _ _ _

private theorem wedgeTwo_self (u : A) : wedgeTwo (F := F) u u = 0 := by
  apply (exteriorPower.ιMulti F 2).map_eq_zero_of_eq _ (i := 0) (j := 1)
  · rfl
  · decide

private theorem wedgeTwo_swap (u v : A) :
    wedgeTwo (F := F) u v = -wedgeTwo v u := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti F 2 ![u,v] = -ExteriorAlgebra.ιMulti F 2 ![v,u]
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, Fin.isValue, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

private theorem wedgeTwo_add_right (u v w : A) :
    wedgeTwo (F := F) u (v + w) = wedgeTwo u v + wedgeTwo u w := by
  rw [wedgeTwo_swap, wedgeTwo_add_left, neg_add, ← wedgeTwo_swap, ← wedgeTwo_swap]

private theorem wedgeTwo_smul_right (a : F) (u v : A) :
    wedgeTwo (F := F) u (a • v) = a • wedgeTwo u v := by
  rw [wedgeTwo_swap, wedgeTwo_smul_left, wedgeTwo_swap v u, smul_neg, neg_neg]

private theorem wedgeTwo_zero_left (v : A) : wedgeTwo (F := F) 0 v = 0 := by
  simpa using wedgeTwo_smul_left (0 : F) v v

private theorem wedgeTwo_zero_right (v : A) : wedgeTwo (F := F) v 0 = 0 := by
  rw [wedgeTwo_swap, wedgeTwo_zero_left, neg_zero]

private theorem wedgeTwo_basis_expansion (b : Basis (Fin 3) F A) (z : ⋀[F]^2 A) :
    ∃ a c d : F, z = a • wedgeTwo (b 0) (b 1) +
      c • wedgeTwo (b 0) (b 2) + d • wedgeTwo (b 1) (b 2) := by
  classical
  let P := fun z : ⋀[F]^2 A => ∃ a c d : F,
    z = a • wedgeTwo (b 0) (b 1) + c • wedgeTwo (b 0) (b 2) +
      d • wedgeTwo (b 1) (b 2)
  have hgen : ∀ i j : Fin 3, P (wedgeTwo (b i) (b j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, 0, 0, by simp [wedgeTwo_self]⟩
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · refine ⟨-1, 0, 0, ?_⟩
      simp only [zero_smul, add_zero]
      exact (wedgeTwo_swap (F := F) (b 1) (b 0)).trans (neg_one_smul F _).symm
    · exact ⟨0, 0, 0, by simp [wedgeTwo_self]⟩
    · exact ⟨0, 0, 1, by simp⟩
    · refine ⟨0, -1, 0, ?_⟩
      simp only [zero_smul, zero_add, add_zero]
      exact (wedgeTwo_swap (F := F) (b 2) (b 0)).trans (neg_one_smul F _).symm
    · refine ⟨0, 0, -1, ?_⟩
      simp only [zero_smul, zero_add, add_zero]
      exact (wedgeTwo_swap (F := F) (b 2) (b 1)).trans (neg_one_smul F _).symm
    · exact ⟨0, 0, 0, by simp [wedgeTwo_self]⟩
  have hz : z ∈ Submodule.span F (exteriorPower.ιMulti F 2 ''
      {v : Fin 2 → A | Set.range v ⊆ Set.range b}) := by
    rw [exteriorPower.ιMulti_span_of_span F 2 A b.span_eq]
    exact Submodule.mem_top
  change P z
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, hv, rfl⟩ := hz
      obtain ⟨i, hi⟩ := hv (Set.mem_range_self (0 : Fin 2))
      obtain ⟨j, hj⟩ := hv (Set.mem_range_self (1 : Fin 2))
      have heq : v = ![b i, b j] := by
        ext k
        fin_cases k
        · exact hi.symm
        · exact hj.symm
      rw [heq]
      exact hgen i j
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, c, d, rfl⟩ := hx
      obtain ⟨a', c', d', rfl⟩ := hy
      exact ⟨a + a', c + c', d + d', by module⟩
  | smul a x _ hx =>
      obtain ⟨c, d, e, rfl⟩ := hx
      exact ⟨a * c, a * d, a * e, by module⟩

/-- Every bivector in a three-dimensional space is a single exterior product.
The statement includes the zero bivector and works over any field. -/
theorem wedgeTwo_surjective_of_basis_three (b : Basis (Fin 3) F A)
    (z : ⋀[F]^2 A) : ∃ u v : A, z = wedgeTwo u v := by
  obtain ⟨a, c, d, rfl⟩ := wedgeTwo_basis_expansion b z
  by_cases ha : a = 0
  · refine ⟨c • b 0 + d • b 1, b 2, ?_⟩
    simp [ha, wedgeTwo_add_left, wedgeTwo_smul_left]
  · refine ⟨b 0 + (-d / a) • b 2, a • b 1 + c • b 2, ?_⟩
    simp [wedgeTwo_add_left, wedgeTwo_add_right, wedgeTwo_smul_left,
      wedgeTwo_smul_right, wedgeTwo_self, wedgeTwo_swap (b 2) (b 1),
      smul_add, smul_smul, smul_neg]
    have hcancel : a * (-d / a) = -d := by field_simp
    rw [hcancel, neg_smul, neg_neg]
    module

/-- In dimension three, a map with zero kernel on exterior products is injective. -/
theorem exteriorTwo_injective_of_basis_three (b : Basis (Fin 3) F A)
    (f : (⋀[F]^2 A) →ₗ[F] T)
    (hf : ∀ u v : A, f (wedgeTwo u v) = 0 → wedgeTwo (F := F) u v = 0) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨u, v, rfl⟩ := wedgeTwo_surjective_of_basis_three b z
  exact hf u v hz

/-- Basis-free form of decomposability for a space of dimension three. -/
theorem wedgeTwo_surjective_of_finrank_three [FiniteDimensional F A]
    (hA : finrank F A = 3) (z : ⋀[F]^2 A) : ∃ u v : A, z = wedgeTwo u v :=
  wedgeTwo_surjective_of_basis_three (finBasisOfFinrankEq F A hA) z

/-- Basis-free injectivity criterion for the second exterior power in dimension three. -/
theorem exteriorTwo_injective_of_finrank_three [FiniteDimensional F A]
    (hA : finrank F A = 3) (f : (⋀[F]^2 A) →ₗ[F] T)
    (hf : ∀ u v : A, f (wedgeTwo u v) = 0 → wedgeTwo (F := F) u v = 0) :
    Function.Injective f :=
  exteriorTwo_injective_of_basis_three (finBasisOfFinrankEq F A hA) f hf

/-- If no nonzero exterior product is killed, the target has dimension at least three. -/
theorem exteriorTwo_target_finrank_ge_three [FiniteDimensional F A] [FiniteDimensional F T]
    (hA : finrank F A = 3) (f : (⋀[F]^2 A) →ₗ[F] T)
    (hf : ∀ u v : A, f (wedgeTwo u v) = 0 → wedgeTwo (F := F) u v = 0) :
    3 ≤ finrank F T := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (exteriorTwo_injective_of_finrank_three hA f hf)
  simpa [exteriorPower.finrank_eq, hA] using h

/-- A map from the second exterior power of a three-dimensional space to a
space of dimension at most two kills the wedge of an independent pair. -/
theorem exists_independent_pair_in_wedge_kernel
    [FiniteDimensional F A] [FiniteDimensional F T]
    (hA : finrank F A = 3) (hT : finrank F T ≤ 2) (f : (⋀[F]^2 A) →ₗ[F] T) :
    ∃ u v : A, LinearIndependent F ![u, v] ∧ f (wedgeTwo u v) = 0 := by
  classical
  by_contra h
  have hf : ∀ u v : A, f (wedgeTwo u v) = 0 → wedgeTwo (F := F) u v = 0 := by
    intro u v huv
    by_contra hne
    have hli : LinearIndependent F ![u, v] := by
      by_contra hdep
      exact hne ((exteriorPower.ιMulti F 2).map_linearDependent ![u, v] hdep)
    exact h ⟨u, v, hli, huv⟩
  have hdim := exteriorTwo_target_finrank_ge_three hA f hf
  omega

end Normalizer
