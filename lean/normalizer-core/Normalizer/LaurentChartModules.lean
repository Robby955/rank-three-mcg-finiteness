import Normalizer.LaurentCechFinite
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A localization-to-Laurent span argument for actual chart modules.
The denominator and scalar-compatibility hypotheses are module identities,
separate from the cohomology application. -/
noncomputable section
namespace Normalizer
open LaurentPolynomial
open scoped LaurentPolynomial
universe u v w
variable (k : Type u) [CommRing k]
  {R : Type v} [CommRing R] {A : Type w} [AddCommGroup A] [Module R A]
  {B : Type*} [AddCommGroup B] [Module k B] [Module k[T;T⁻¹] B]
  [IsScalarTower k k[T;T⁻¹] B]
  (γ : R →+* k[T;T⁻¹]) (φ : A →ₛₗ[γ] B)

omit [Module k B] [IsScalarTower k k[T;T⁻¹] B] in
/-- Images of chart generators span every restricted chart section over the Laurent ring. -/
theorem laurentChart_image_mem_span {ι : Type*} (v : ι → A)
    (hv : Submodule.span R (Set.range v) = ⊤) (a : A) :
    φ a ∈ Submodule.span k[T;T⁻¹] (Set.range (φ ∘ v)) := by
  have ha : a ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_range_self i)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [φ.map_smulₛₗ] using Submodule.smul_mem _ (γ r) ih

omit [Module k B] [IsScalarTower k k[T;T⁻¹] B] in
/-- Clearing a Laurent-power denominator proves the images of chart generators span the whole overlap. -/
theorem laurentChart_span_eq_top {ι : Type*} (v : ι → A)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (hdenom : ∀ z : B, ∃ n : ℤ, ∃ a : A, (T n : k[T;T⁻¹]) • z = φ a) :
    Submodule.span k[T;T⁻¹] (Set.range (φ ∘ v)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro z
  obtain ⟨n, a, ha⟩ := hdenom z
  have hm := Submodule.smul_mem
    (Submodule.span k[T;T⁻¹] (Set.range (φ ∘ v))) (T (-n))
      (laurentChart_image_mem_span k γ φ v hv a)
  rw [← ha, ← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul] at hm
  exact hm

/-- A chart restriction image is exactly the coefficient span of its generator translates,
when the chart scalars have the stated polynomial coordinate. -/
theorem laurentChart_range_eq_span {ι : Type*} (v : ι → A)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (e : R ≃+* Polynomial k) (d : ℤ)
    (hγ : ∀ r, γ r = Polynomial.eval₂RingHom C (T d) (e r)) :
    Set.range φ = (laurentSpan k (φ ∘ v) (Set.range (fun n : ℕ => (n : ℤ) * d)) : Set B) := by
  let N := laurentSpan k (φ ∘ v) (Set.range (fun n : ℕ => (n : ℤ) * d))
  have hscalar (r : R) (i : ι) : (γ r) • φ (v i) ∈ N := by
    rw [hγ]
    generalize e r = p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add, add_smul] using Submodule.add_mem N hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
      rw [T_pow, mul_smul, C_eq_algebraMap, algebraMap_smul]
      exact N.smul_mem a (laurentSpan_generator k (φ ∘ v) _ i _ ⟨n, rfl⟩)
  have himage (a : A) : φ a ∈ N := by
    have ha : a ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
    have hall : ∀ r : R, φ (r • a) ∈ N := by
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact fun r => by rw [φ.map_smulₛₗ]; exact hscalar r i
      | zero => intro r; simp
      | add x y hx hy ihx ihy =>
        intro r
        rw [smul_add, map_add]
        exact N.add_mem (ihx r) (ihy r)
      | smul s x hx ih => intro r; rw [smul_smul]; exact ih (r * s)
    simpa using hall 1
  have hC (a : k) : γ (e.symm (Polynomial.C a)) = C a := by
    rw [hγ, e.apply_symm_apply]
    simp
  have hX (n : ℕ) : γ (e.symm (Polynomial.X ^ n)) = T ((n : ℤ) * d) := by
    rw [hγ, e.apply_symm_apply]
    simp [T_pow]
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact himage a
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, m, ⟨n, rfl⟩, rfl⟩ := hx
      exact ⟨e.symm (Polynomial.X ^ n) • v i, by rw [φ.map_smulₛₗ, hX]; rfl⟩
    | zero => exact ⟨0, φ.map_zero⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, rfl⟩ := ihx
      obtain ⟨b, rfl⟩ := ihy
      exact ⟨a + b, φ.map_add a b⟩
    | smul c x hx ih =>
      obtain ⟨a, rfl⟩ := ih
      exact ⟨e.symm (Polynomial.C c) • a, by rw [φ.map_smulₛₗ, hC, C_eq_algebraMap, algebraMap_smul]⟩

/-- A surjective coefficient-linear boundary killed by the two Laurent tails has finite target. -/
theorem laurentChart_boundary_finite {ι κ : Type*} [Finite ι]
    (v : ι → B) (w : κ → B)
    (hv : Submodule.span k[T;T⁻¹] (Set.range v) = ⊤)
    (hw : Submodule.span k[T;T⁻¹] (Set.range w) = ⊤)
    {H : Type*} [AddCommGroup H] [Module k H] (δ : B →ₗ[k] H)
    (hδ : Function.Surjective δ)
    (hpos : laurentSpan k v (Set.Ici 0) ≤ δ.ker)
    (hneg : laurentSpan k w (Set.Iic 0) ≤ δ.ker) : Module.Finite k H := by
  let N := laurentSpan k v (Set.Ici 0) ⊔ laurentSpan k w (Set.Iic 0)
  have := laurent_twoChart_quotient_finite k v hv w hw
  let q := N.liftQ δ (sup_le hpos hneg)
  exact Module.Finite.of_surjective q (fun h => by
    obtain ⟨z, rfl⟩ := hδ h
    exact ⟨N.mkQ z, rfl⟩)

end Normalizer
