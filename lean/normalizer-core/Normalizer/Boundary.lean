import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

/-! The algebra of the Čech boundary calculation. No curve or cohomology
construction is postulated here: the passage from representatives to classes
is an explicit linear map, with its compatibility hypotheses exposed. -/
namespace Normalizer

variable {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]

/-- Overlap expansion for arbitrary sections in an abelian ideal. The
differences need not be constant scalar multiples of a common generator. -/
theorem abelian_overlap_difference (X Y a b : L) (lx ly : F)
    (hx : ⁅X, b⁆ = lx • b) (hy : ⁅Y, a⁆ = ly • a) (hab : ⁅a, b⁆ = 0) :
    ⁅X + a, Y + b⁆ - ⁅X, Y⁆ = lx • b - ly • a := by
  have haY : ⁅a, Y⁆ = -(ly • a) := by rw [← lie_skew, hy]
  simp only [add_lie, lie_add, hx, haY, hab]
  abel

/-- Expansion on one overlap, with the manuscript convention `Xj - Xi`. -/
theorem cech_commutator_difference (Xi Yi m : L) (a b lx ly : F)
    (hx : ⁅Xi, m⁆ = lx • m) (hy : ⁅Yi, m⁆ = ly • m) :
    ⁅Xi + a • m, Yi + b • m⁆ - ⁅Xi, Yi⁆ =
      lx • (b • m) - ly • (a • m) := by
  have hm : ⁅m, Yi⁆ = -(ly • m) := by rw [← lie_skew, hy]
  simp only [add_lie, lie_add, lie_smul, smul_lie, lie_self, smul_zero,
    add_zero, hx, hm, smul_neg]
  simp only [smul_comm b lx, smul_comm a ly]
  abel

/-- Applying a linear class map to overlap representatives proves the
boundary identity. `Z` is the submodule of valid cocycles. The three
representative equalities are hypotheses, not definitions of a geometric boundary map. -/
theorem boundary_cocycle {I V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (boundary : V →ₗ[F] W) (Z : Submodule F (I → L)) (classMap : Z →ₗ[F] W)
    (x y bracketXY : V) (Xi Yi m : I → L) (a b : I → F) (lx ly : F)
    (hx : ∀ i, ⁅Xi i, m i⁆ = lx • m i)
    (hy : ∀ i, ⁅Yi i, m i⁆ = ly • m i)
    (ha : (fun i => a i • m i) ∈ Z) (hb : (fun i => b i • m i) ∈ Z)
    (hc : (fun i => ⁅Xi i + a i • m i, Yi i + b i • m i⁆ - ⁅Xi i, Yi i⁆) ∈ Z)
    (repX : boundary x = classMap ⟨(fun i => a i • m i), ha⟩)
    (repY : boundary y = classMap ⟨(fun i => b i • m i), hb⟩)
    (repBracket : boundary bracketXY = classMap ⟨(fun i =>
      ⁅Xi i + a i • m i, Yi i + b i • m i⁆ - ⁅Xi i, Yi i⁆), hc⟩) :
    boundary bracketXY = lx • boundary y - ly • boundary x := by
  rw [repBracket, repX, repY]
  have h : (⟨(fun i => ⁅Xi i + a i • m i, Yi i + b i • m i⁆ - ⁅Xi i, Yi i⁆), hc⟩ : Z) =
      lx • ⟨(fun i => b i • m i), hb⟩ - ly • ⟨(fun i => a i • m i), ha⟩ := by
    apply Subtype.ext
    funext i
    exact cech_commutator_difference (Xi i) (Yi i) (m i) (a i) (b i) lx ly
      (hx i) (hy i)
  rw [h, map_sub, map_smul, map_smul]

/-- Injectivity on the whole ambient section space gives the quotient law. -/
theorem quotient_boundary_law {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (boundary : V →ₗ[F] W) (hinj : Function.Injective boundary)
    (x y bracketXY : V) (lx ly : F)
    (h : boundary bracketXY = lx • boundary y - ly • boundary x) :
    bracketXY = lx • y - ly • x := by
  apply hinj
  simpa only [map_sub, map_smul] using h

end Normalizer
