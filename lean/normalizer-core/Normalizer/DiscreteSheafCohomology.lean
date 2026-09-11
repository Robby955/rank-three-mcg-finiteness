import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual abelian sheaf cohomology vanishes in positive degrees on a discrete space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits TopologicalSpace Opposite

universe u
variable {X : TopCat.{u}}

private theorem empty_section_eq (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a b : F.obj.obj (op ⊥)) : a = b := by
  apply F.eq_of_locally_eq' (fun _ : PEmpty.{u+1} => ⊥) ⊥ (fun i => PEmpty.elim i)
    (by simp) a b
  intro i
  exact PEmpty.elim i

/-- An epimorphism of actual abelian sheaves on a discrete space is surjective on
actual global sections. The lifts are glued from singleton open sets. -/
theorem discreteSheaf_epi_globalSections_surjective [DiscreteTopology X]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op ⊤)) := by
  classical
  intro s
  let U : X → Opens X := fun x => ⟨{x}, isOpen_discrete _⟩
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, rfl⟩
  have hf : CategoryTheory.Sheaf.IsLocallySurjective f :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).mpr inferInstance
  have hlift : ∀ x, ∃ a : F.obj.obj (op (U x)),
      f.hom.app (op (U x)) a = G.obj.map (homOfLE le_top).op s := by
    intro x
    obtain ⟨V, i, ⟨a, ha⟩, hx⟩ := hf.imageSieve_mem s x (by trivial)
    have hUV : U x ≤ V := by
      intro y hy
      have : y = x := hy
      simpa [this] using hx
    refine ⟨F.obj.map (homOfLE hUV).op a, ?_⟩
    rw [NatTrans.naturality_apply]
    rw [ha, ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    rfl
  choose a ha using hlift
  have hc : TopCat.Presheaf.IsCompatible F.obj U a := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · have hempty : U x ⊓ U y = ⊥ := by
        ext z
        change (z ∈ ({x} : Set X) ∧ z ∈ ({y} : Set X)) ↔ False
        rw [iff_false]
        rintro ⟨hx, hy⟩
        exact hxy (hx.symm.trans hy)
      have hsub : Subsingleton (F.obj.obj (op (U x ⊓ U y))) := by
        rw [hempty]
        exact ⟨empty_section_eq F⟩
      exact hsub.elim _ _
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
    hcover a hc
  refine ⟨t, ?_⟩
  apply G.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcover
  intro x
  rw [← NatTrans.naturality_apply, ht, ha]

/-- The actual constant integer sheaf is projective on a discrete space. -/
theorem discreteSheaf_constantInteger_projective [DiscreteTopology X] :
    Projective ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  constructor
  intro F G f g hg
  have : Epi g := hg
  let z : CategoryTheory.Sheaf.H G 0 := Abelian.Ext.addEquiv₀.symm f
  obtain ⟨t, ht⟩ := discreteSheaf_epi_globalSections_surjective g
    (CategoryTheory.Sheaf.H.equiv₀ G isTerminalTop z)
  let w := (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm t
  refine ⟨Abelian.Ext.addEquiv₀ w, ?_⟩
  have hw : CategoryTheory.Sheaf.H.map g 0 w = z := by
    apply (CategoryTheory.Sheaf.H.equiv₀ G isTerminalTop).injective
    rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
    simpa [w] using ht
  rw [← CategoryTheory.Sheaf.H.addEquiv₀_map, hw]
  exact Abelian.Ext.addEquiv₀.apply_symm_apply f

/-- Positive-degree cohomology of any actual abelian sheaf on a discrete space
vanishes. This uses no reducedness or finiteness assumption on a scheme. -/
theorem discreteSheaf_positiveCohomology_subsingleton [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  have hproj := discreteSheaf_constantInteger_projective (X := X)
  exact @Abelian.Ext.subsingleton_of_projective _ _ _ _ _ F hproj n

end Normalizer
