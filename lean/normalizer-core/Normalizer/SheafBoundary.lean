import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Tactic.Abel
import Normalizer.Boundary

/-! Descent of the boundary law by actual sheaf gluing. The global image of
the middle sheaf is assumed zero. This follows from vanishing global middle
sections, or from injectivity and exactness of a geometric boundary. No
sheaf-cohomology comparison or existence of local normalizer lifts is assumed
implicitly: the local lifts and their overlap identity are explicit inputs. -/

namespace Normalizer
open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u
variable {F : Type u} [Field F] {X : TopCat.{u}}
  (E G : TopCat.Sheaf (ModuleCat.{u} F) X)

/-- Vanishing of the actual global-section module makes every global
image map zero. This is the hypothesis used in the genus-five applications. -/
theorem sheaf_global_map_zero_of_vanishing
    (q : E.obj ⟶ G.obj) (hvanish : Subsingleton (E.obj.obj (op ⊤))) :
    (q.app (op ⊤)).hom = 0 := by
  ext t
  have ht : t = 0 := hvanish.elim t 0
  simp [ht]

/-- Corrected local lifts glue in E. If global E-sections have zero image
in G, the required linear relation holds between global G-sections. -/
theorem sheaf_boundary_law_of_overlaps
    (q : E.obj ⟶ G.obj) (hq : (q.app (op ⊤)).hom = 0)
    {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
    (x y z : G.obj.obj (op ⊤)) (lx ly : F)
    (Xi Yi Zi : ∀ i, E.obj.obj (op (U i)))
    (hx : ∀ i, (q.app (op (U i))).hom (Xi i) =
      (G.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom x)
    (hy : ∀ i, (q.app (op (U i))).hom (Yi i) =
      (G.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom y)
    (hz : ∀ i, (q.app (op (U i))).hom (Zi i) =
      (G.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom z)
    (hoverlap : ∀ i j,
      (E.obj.map (infLERight (U i) (U j)).op).hom (Zi j) -
        (E.obj.map (infLELeft (U i) (U j)).op).hom (Zi i) =
      lx • ((E.obj.map (infLERight (U i) (U j)).op).hom (Yi j) -
        (E.obj.map (infLELeft (U i) (U j)).op).hom (Yi i)) -
      ly • ((E.obj.map (infLERight (U i) (U j)).op).hom (Xi j) -
        (E.obj.map (infLELeft (U i) (U j)).op).hom (Xi i))) :
    z = lx • y - ly • x := by
  let corrected := fun i => Zi i - lx • Yi i + ly • Xi i
  have hc : TopCat.Presheaf.IsCompatible E.obj U corrected := by
    intro i j
    change (E.obj.map (infLELeft (U i) (U j)).op).hom (corrected i) =
      (E.obj.map (infLERight (U i) (U j)).op).hom (corrected j)
    dsimp [corrected]
    simp only [map_add, map_sub, map_smul]
    have h := hoverlap i j
    simp only [smul_sub] at h
    apply sub_eq_zero.mp
    have he := sub_eq_zero.mpr h
    convert congrArg Neg.neg he using 1 <;> abel
  obtain ⟨t, ht, _⟩ := E.existsUnique_gluing' U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) corrected hc
  have hqt : (q.app (op ⊤)).hom t = 0 := by rw [hq]; rfl
  apply G.eq_of_locally_eq' U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
  intro i
  have hn := congrArg (fun f => f.hom t)
    (q.naturality (homOfLE (show U i ≤ ⊤ from le_top)).op)
  change (q.app (op (U i))).hom
      ((E.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom t) =
    (G.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom
      ((q.app (op ⊤)).hom t) at hn
  rw [ht i, hqt, map_zero] at hn
  dsimp [corrected] at hn
  simp only [map_add, map_sub, map_smul, hx, hy, hz] at hn
  simp only [map_sub, map_smul]
  apply sub_eq_zero.mp
  convert hn using 1
  abel

end Normalizer
