import Normalizer.Boundary
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! The boundary law for actual homology connecting maps. The hypotheses
specify cochain lifts and their differentials, not values of the boundary.
Constructing these cochains from sheaves on a curve is outside this module. -/

namespace Normalizer
open CategoryTheory CategoryTheory.Limits

universe u v
variable {F : Type u} {I : Type*} [Field F] {c : ComplexShape I}
  {S : ShortComplex (HomologicalComplex (ModuleCat.{max u v} F) c)}

/-- The connecting boundary of a class with a closed middle lift is zero. -/
theorem connecting_eq_zero_of_closed_lift (hS : S.ShortExact)
    (i j : I) (hij : c.Rel i j) (x : S.X₃.cycles i) (X : S.X₂.X i)
    (hlift : (S.g.f i).hom X = (S.X₃.iCycles i).hom x)
    (hclosed : (S.X₂.d i j).hom X = 0) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom x) = 0 := by
  have hx : (S.X₃.d i j).hom ((S.X₃.iCycles i).hom x) = 0 := by
    have hz := S.X₃.iCycles_d i j
    exact congrArg (fun f => f.hom x) hz
  have hrep := hS.δ_apply i j hij ((S.X₃.iCycles i).hom x) hx X hlift
    0 (by simpa using hclosed.symm) (c.next j) rfl
  have hcycle : S.X₃.cyclesMk ((S.X₃.iCycles i).hom x) j (c.next_eq' hij) hx = x := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles i)).mp inferInstance
    exact S.X₃.i_cyclesMk _ _ _ _
  have hzero : S.X₁.cyclesMk 0 (c.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j X 0 (by simpa using hclosed.symm) _) = 0 := by
    apply (ModuleCat.mono_iff_injective (S.X₁.iCycles j)).mp inferInstance
    simpa using S.X₁.i_cyclesMk 0 (c.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j X 0 (by simpa using hclosed.symm) _)
  rw [hcycle, hzero] at hrep
  exact hrep.trans (map_zero _)

/-- A differential identity on middle lifts implies the boundary law for
mathlib's connecting map. No boundary-representative identity is assumed. -/
theorem connecting_boundary_law (hS : S.ShortExact)
    (i j : I) (hij : c.Rel i j) (x y z : S.X₃.cycles i)
    (X Y Z : S.X₂.X i) (lx ly : F)
    (hx : (S.g.f i).hom X = (S.X₃.iCycles i).hom x)
    (hy : (S.g.f i).hom Y = (S.X₃.iCycles i).hom y)
    (hz : (S.g.f i).hom Z = (S.X₃.iCycles i).hom z)
    (hd : (S.X₂.d i j).hom Z =
      lx • (S.X₂.d i j).hom Y - ly • (S.X₂.d i j).hom X) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom z) =
      lx • (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom y) -
      ly • (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom x) := by
  have hlift : (S.g.f i).hom (Z - lx • Y + ly • X) =
      (S.X₃.iCycles i).hom (z - lx • y + ly • x) := by
    simp only [map_add, map_sub, map_smul, hx, hy, hz]
  have hclosed : (S.X₂.d i j).hom (Z - lx • Y + ly • X) = 0 := by
    simp only [map_add, map_sub, map_smul, hd]
    abel
  have he := connecting_eq_zero_of_closed_lift (S := S) hS i j hij
    (z - lx • y + ly • x) (Z - lx • Y + ly • X) hlift hclosed
  simp only [map_add, map_sub, map_smul] at he
  apply sub_eq_zero.mp
  convert he using 1
  abel

/-- The local Lie calculation implies the law for the actual homology
boundary. An injective overlap map identifies the three differentials;
the three boundary values are all derived from exactness. -/
theorem connecting_boundary_law_of_overlaps
    {J L : Type*} [LieRing L] [LieAlgebra F L]
    (hS : S.ShortExact) (i j : I) (hij : c.Rel i j)
    (x y z : S.X₃.cycles i) (X Y Z : S.X₂.X i) (lx ly : F)
    (hx : (S.g.f i).hom X = (S.X₃.iCycles i).hom x)
    (hy : (S.g.f i).hom Y = (S.X₃.iCycles i).hom y)
    (hz : (S.g.f i).hom Z = (S.X₃.iCycles i).hom z)
    (overlap : S.X₂.X j →ₗ[F] (J → L)) (hinj : Function.Injective overlap)
    (Xi Yi a b : J → L)
    (hactionX : ∀ t, ⁅Xi t, b t⁆ = lx • b t)
    (hactionY : ∀ t, ⁅Yi t, a t⁆ = ly • a t)
    (habelian : ∀ t, ⁅a t, b t⁆ = 0)
    (hdX : overlap ((S.X₂.d i j).hom X) = a)
    (hdY : overlap ((S.X₂.d i j).hom Y) = b)
    (hdZ : overlap ((S.X₂.d i j).hom Z) = fun t =>
      ⁅Xi t + a t, Yi t + b t⁆ - ⁅Xi t, Yi t⁆) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom z) =
      lx • (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom y) -
      ly • (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom x) := by
  apply connecting_boundary_law (S := S) hS i j hij x y z X Y Z lx ly hx hy hz
  apply hinj
  rw [map_sub, map_smul, map_smul, hdX, hdY, hdZ]
  funext t
  exact abelian_overlap_difference (Xi t) (Yi t) (a t) (b t) lx ly
    (hactionX t) (hactionY t) (habelian t)

end Normalizer
