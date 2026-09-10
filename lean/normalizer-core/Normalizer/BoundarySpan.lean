import Normalizer.Obstruction
import Mathlib.LinearAlgebra.BilinearMap

/-! Extension of the boundary law from generators to their full scalar span. -/

namespace Normalizer

/-- For a bilinear bracket and linear character, the boundary law on all
pairs of generators implies the law on their entire span. -/
theorem boundaryLaw_span {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (B : V →ₗ[F] V →ₗ[F] V) (chi : V →ₗ[F] F) (S : Set V)
    (h : ∀ x ∈ S, ∀ y ∈ S, B x y = chi x • y - chi y • x) :
    BoundaryLaw (Submodule.span F S) (fun x y ↦ B x y) chi := by
  let A : V →ₗ[F] V →ₗ[F] V := (LinearMap.lsmul F V).comp chi
  let D := B - A + A.flip
  have hD : ∀ x ∈ S, ∀ y ∈ S, D x y = 0 := by
    intro x hx y hy
    change B x y - chi x • y + chi y • x = 0
    rw [h x hx y hy]
    abel
  have hyD : ∀ x ∈ S, ∀ y ∈ Submodule.span F S, D x y = 0 := by
    intro x hx y hy
    exact (D x).eqOn_span (g := 0) (fun z hz ↦ hD x hx z hz) hy
  intro x hx y hy
  have hxy : D x y = 0 :=
    (D.flip y).eqOn_span (g := 0) (fun z hz ↦ hyD z hz y hy) hx
  change B x y - chi x • y + chi y • x = 0 at hxy
  apply sub_eq_zero.mp
  calc
    B x y - (chi x • y - chi y • x) = B x y - chi x • y + chi y • x := by abel
    _ = 0 := hxy

/-- A boundary law carried by a semilinear evaluation map extends to the
span over the larger field. Bracket and character compatibility are
explicit hypotheses on that map, not an injectivity assumption. -/
theorem boundaryLaw_span_image
    {k F V W : Type*} [Field k] [Field F] [Algebra k F]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module F W]
    (f : V →ₛₗ[algebraMap k F] W)
    (b : V → V → V) (l : V → k)
    (B : W →ₗ[F] W →ₗ[F] W) (chi : W →ₗ[F] F) (U : Submodule k V)
    (hlaw : BoundaryLaw U b l)
    (hb : ∀ x ∈ U, ∀ y ∈ U, B (f x) (f y) = f (b x y))
    (hchi : ∀ x ∈ U, chi (f x) = algebraMap k F (l x)) :
    BoundaryLaw (Submodule.span F (f '' (U : Set V))) (fun x y ↦ B x y) chi := by
  apply boundaryLaw_span
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [hb x hx y hy, hlaw x hx y hy, map_sub, f.map_smulₛₗ, f.map_smulₛₗ,
    hchi x hx, hchi y hy]

end Normalizer
