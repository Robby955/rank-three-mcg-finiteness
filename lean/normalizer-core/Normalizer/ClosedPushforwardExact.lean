import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact

/-! Direct image of actual abelian sheaves along a closed embedding is exact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)

private theorem section_eq_of_empty (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (hU : U = ⊥) (a b : F.obj.obj (op U)) : a = b := by
  subst U
  apply F.eq_of_locally_eq' (fun _ : PEmpty.{u+1} => ⊥) ⊥ (fun i => PEmpty.elim i)
    (by simp) a b
  intro i
  exact PEmpty.elim i

/-- Actual abelian-sheaf direct image is additive for every continuous map. -/
theorem abelianSheafPushforward_additive :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  ⟨by intros; rfl⟩

include hf

/-- Direct image along an actual closed embedding preserves epimorphisms of
abelian sheaves. The proof uses local lifts, not surjectivity on fixed opens. -/
theorem closedPushforward_map_epi
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G) [Epi g] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat f).map g) := by
  classical
  apply (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} _).mp
  have hg : CategoryTheory.Sheaf.IsLocallySurjective g :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} g).mpr inferInstance
  constructor
  intro U s y hy
  by_cases himage : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := himage
    obtain ⟨V, i, ⟨a, ha⟩, hx⟩ := hg.imageSieve_mem s x hy
    obtain ⟨W, hW, hpre⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp V.isOpen
    let O : Opens Y := ⟨W ∩ U, hW.inter U.isOpen⟩
    have hOU : O ≤ U := fun _ h => h.2
    have hOV : (Opens.map f).obj O ≤ V := by
      intro z hz
      change f z ∈ W ∩ U at hz
      change z ∈ (V : Set X)
      rw [← hpre]
      exact hz.1
    refine ⟨O, homOfLE hOU, ?_, ?_⟩
    · refine ⟨F.obj.map (homOfLE hOV).op a, ?_⟩
      change g.hom.app (op ((Opens.map f).obj O))
        (F.obj.map (homOfLE hOV).op a) =
        G.obj.map ((Opens.map f).map (homOfLE hOU)).op s
      rw [NatTrans.naturality_apply, ha, ← ConcreteCategory.comp_apply,
        ← G.obj.map_comp]
      rfl
    · change f x ∈ W ∩ U
      exact ⟨by change x ∈ f ⁻¹' W; rwa [hpre], hy⟩
  · let O : Opens Y := ⟨U \ Set.range f, U.isOpen.inter hf.isClosed_range.isOpen_compl⟩
    have hOU : O ≤ U := fun _ h => h.1
    have hempty : (Opens.map f).obj O = ⊥ := by
      ext x
      change (f x ∈ U ∧ f x ∉ Set.range f) ↔ False
      simp
    refine ⟨O, homOfLE hOU, ⟨0, ?_⟩, hy, himage⟩
    exact section_eq_of_empty G _ hempty _ _

/-- Epimorphism preservation for the actual closed direct-image functor. -/
theorem closedPushforward_preservesEpimorphisms :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms where
  preserves g _ := closedPushforward_map_epi f hf g

/-- Closed direct image preserves homology, hence exactness of actual short complexes. -/
theorem closedPushforward_preservesHomology :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology := by
  have := closedPushforward_preservesEpimorphisms f hf
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Closed direct image of actual abelian sheaves preserves finite colimits. -/
theorem closedPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  have := closedPushforward_preservesHomology f hf
  have := abelianSheafPushforward_additive f
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end Normalizer
