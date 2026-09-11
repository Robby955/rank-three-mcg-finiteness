import Normalizer.ClosedSubschemeModules
import Normalizer.SectionZeroIdealAffine
import Normalizer.SheafCokernelComparison

/-! The actual scalar cokernel for the zero scheme of a line-sheaf map.
The stalk exactness is constructed from the actual affine defining ideals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits
universe u v
variable {X : Scheme.{u}} {L : X.Modules}
  (φ : L ⟶ SheafOfModules.unit X.ringCatSheaf)
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ i, QuasiCompact (U i).ι]
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))
  (hU : iSup U = ⊤)

/-- The original line map followed by restriction to its actual zero
scheme vanishes on every actual stalk. -/
theorem schemeSectionZeroQuotient_stalk_comp (x : X) (a : L.presheaf.stalk x) :
    schemeModuleStalkMap (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)) x
      (schemeModuleStalkMap φ x a) = 0 := by
  obtain ⟨W, hxW, a, rfl⟩ := L.presheaf.exists_germ_eq a
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := W ⊓ U i) ⟨hxW, hxi⟩
  have hVW' : V ≤ W := hVW.trans inf_le_left
  have hVi : V ≤ U i := hVW.trans inf_le_right
  rw [← L.presheaf.germ_res_apply (homOfLE hVW') x hxV a,
    schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
  have hz := (schemeSectionZeroSchemeι_app_eq_zero_iff φ U e hU i ⟨V, hV⟩ hVi
    (φ.val.app (op V) (L.presheaf.map (homOfLE hVW').op a))).mpr ⟨_, rfl⟩
  change (closedSubschemeStructureSheaf (schemeSectionZeroIdeal φ U e hU)).presheaf.germ
    V x hxV ((schemeSectionZeroSchemeι φ U e hU).app V
      (φ.val.app (op V) (L.presheaf.map (homOfLE hVW').op a))) = 0
  rw [hz, map_zero]

/-- The original line map vanishes under the actual closed-subscheme
structure quotient as a morphism of sheaves. -/
theorem schemeSectionZeroQuotient_comp :
    φ ≫ closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU) = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro a
  let Q : X.Modules := closedSubschemeStructureSheaf (schemeSectionZeroIdeal φ U e hU)
  change (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)).val.app (op W)
    (φ.app W a) = (0 : Γ(Q, W))
  apply TopCat.Presheaf.section_ext ⟨Q.presheaf, Q.isSheaf⟩ W _ 0
  intro x hxW
  have h := schemeSectionZeroQuotient_stalk_comp φ U e hU x (L.presheaf.germ W x hxW a)
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ] at h
  change Q.presheaf.germ W x hxW
    ((closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)).val.app (op W)
      (φ.app W a)) = 0 at h
  simpa only [map_zero] using h

/-- Every actual stalk element killed by the closed-subscheme quotient
comes from the original line sheaf. Affine refinement proves the lift. -/
theorem schemeSectionZeroQuotient_stalk_exact (x : X)
    (b : (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x)
    (hb : schemeModuleStalkMap
      (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)) x b = 0) :
    ∃ a : L.presheaf.stalk x, schemeModuleStalkMap φ x a = b := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q : X.Modules := closedSubschemeStructureSheaf (schemeSectionZeroIdeal φ U e hU)
  let q : O ⟶ Q := closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)
  obtain ⟨W, hxW, r, rfl⟩ := O.presheaf.exists_germ_eq b
  have hg : Q.presheaf.germ W x hxW (q.val.app (op W) r) = Q.presheaf.germ W x hxW 0 := by
    change schemeModuleStalkMap q x (O.presheaf.germ W x hxW r) = 0 at hb
    rw [schemeModuleStalkMap_germ] at hb
    change Q.presheaf.germ W x hxW (q.val.app (op W) r) = 0 at hb
    simpa only [map_zero] using hb
  obtain ⟨T, hxT, j, k, he⟩ := Q.presheaf.germ_eq x hxW hxW _ _ hg
  have hqT : q.val.app (op T) (O.presheaf.map j.op r) = 0 := by
    have hn := PresheafOfModules.naturality_apply q.val j.op r
    change q.val.app (op T) (O.presheaf.map j.op r) =
      Q.presheaf.map j.op (q.val.app (op W) r) at hn
    exact hn.trans (by simpa only [map_zero] using he)
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  obtain ⟨V, hV, hxV, hVT⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := T ⊓ U i) ⟨hxT, hxi⟩
  have hVT' : V ≤ T := hVT.trans inf_le_left
  have hVi : V ≤ U i := hVT.trans inf_le_right
  let rV := O.presheaf.map (homOfLE hVT').op (O.presheaf.map j.op r)
  have hqV : q.val.app (op V) rV = 0 := by
    have hn := PresheafOfModules.naturality_apply q.val (homOfLE hVT').op (O.presheaf.map j.op r)
    exact hn.trans (by rw [hqT, map_zero])
  obtain ⟨a, ha⟩ := (schemeSectionZeroSchemeι_app_eq_zero_iff φ U e hU i
    ⟨V, hV⟩ hVi rV).mp hqV
  refine ⟨L.presheaf.germ V x hxV a, ?_⟩
  rw [schemeModuleStalkMap_germ]
  change O.presheaf.germ V x hxV (φ.val.app (op V) a) = _
  rw [ha]
  exact (O.presheaf.germ_res_apply (homOfLE hVT') x hxV _).trans
    (O.presheaf.germ_res_apply j x hxT r)

/-- The kernel of the actual zero-scheme quotient on every stalk is the
image of the original line map, with no exactness hypothesis supplied. -/
theorem schemeSectionZeroQuotient_stalk_ker_eq_range (x : X) :
    LinearMap.ker (schemeModuleStalkMap
      (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)) x) =
      LinearMap.range (schemeModuleStalkMap φ x) := by
  ext b
  constructor
  · exact schemeSectionZeroQuotient_stalk_exact φ U e hU x b
  · rintro ⟨a, rfl⟩
    exact schemeSectionZeroQuotient_stalk_comp φ U e hU x a

/-- The actual cokernel of a line map is the pushed-forward structure
module of its actual zero scheme. No integrality or monicity is required. -/
def schemeSectionZeroCokernelIso :
    cokernel φ ≅ closedSubschemeStructureSheaf (schemeSectionZeroIdeal φ U e hU) :=
  sheafCokernelComparisonIso φ _ (schemeSectionZeroQuotient_comp φ U e hU)
    (closedSubschemeStructureMap_stalk_surjective _)
    (schemeSectionZeroQuotient_stalk_ker_eq_range φ U e hU)

/-- The actual cokernel isomorphism preserves the canonical quotient map. -/
theorem schemeSectionZeroCokernelIso_π_hom :
    cokernel.π φ ≫ (schemeSectionZeroCokernelIso φ U e hU).hom =
      closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU) :=
  sheafCokernelComparisonIso_π_hom φ _ (schemeSectionZeroQuotient_comp φ U e hU)
    (closedSubschemeStructureMap_stalk_surjective _)
    (schemeSectionZeroQuotient_stalk_ker_eq_range φ U e hU)

end Normalizer
