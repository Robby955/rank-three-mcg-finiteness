import Normalizer.SectionZeroScheme

/-! Actual ideal-sheaf data are determined by restrictions to an open cover.
Consequently the zero ideal is independent of its genuine finite chart cover. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits
universe u v w
variable {X : Scheme.{u}}

/-- Ideal-sheaf data agreeing on an actual open cover agree globally.
No finiteness or quasi-compactness assumption is needed for uniqueness. -/
theorem idealSheaf_eq_of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (I J : X.IdealSheafData)
    (h : ∀ i, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  let A : (Σ i, (U i).toScheme.affineOpens) → X.affineOpens := fun a =>
    ⟨(U a.1).ι ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion (U a.1).ι⟩
  have hA : ⨆ a, (A a).1 = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge hx)
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top (U i).toScheme).ge
        (show (⟨x, hi⟩ : (U i).toScheme) ∈ (⊤ : (U i).toScheme.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, V⟩, ⟨⟨x, hi⟩, hV, rfl⟩⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A hA
  intro a
  have ha := congrArg (fun K : (U a.1).toScheme.IdealSheafData => K.ideal a.2) (h a.1)
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.Opens.ι_appIso, Iso.refl_inv] at ha
  change (I.ideal (A a)).comap (RingHom.id _) =
    (J.ideal (A a)).comap (RingHom.id _) at ha
  simpa only [Ideal.comap_id] using ha

variable {L : X.Modules} (φ : L ⟶ SheafOfModules.unit X.ringCatSheaf)
  {ι : Type v} {κ : Type w}
  (U : ι → X.Opens) (V : κ → X.Opens)
  (eU : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))
  (eV : ∀ j, (SheafOfModules.unit X.ringCatSheaf).over (V j) ≅ L.over (V j))

/-- Two genuine finite line-chart covers give exactly the same global
zero ideal for the same original sheaf map. -/
theorem schemeSectionZeroIdeal_cover_independent
    [Finite ι] [∀ i, QuasiCompact (U i).ι]
    [Finite κ] [∀ j, QuasiCompact (V j).ι]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) :
    schemeSectionZeroIdeal φ U eU hU = schemeSectionZeroIdeal φ V eV hV := by
  apply idealSheaf_eq_of_openCover (fun p : ι × κ => U p.1 ⊓ V p.2)
  · apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge hx)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hV.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  · intro p
    let eW := schemeLineChartRestrict (inf_le_left : U p.1 ⊓ V p.2 ≤ U p.1) (eU p.1)
    have hleft : (U p.1 ⊓ V p.2).ι =
        X.homOfLE (inf_le_left : U p.1 ⊓ V p.2 ≤ U p.1) ≫ (U p.1).ι := by simp
    have hright : (U p.1 ⊓ V p.2).ι =
        X.homOfLE (inf_le_right : U p.1 ⊓ V p.2 ≤ V p.2) ≫ (V p.2).ι := by simp
    conv_lhs => rw [hleft]
    conv_rhs => rw [hright]
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      schemeSectionZeroIdeal_comap, schemeSectionZeroIdeal_comap,
      schemeSectionImageIdealOn_comap φ eW (eU p.1) inf_le_left,
      schemeSectionImageIdealOn_comap φ eW (eV p.2) inf_le_right]

/-- The actual closed zero subscheme is independent of the finite genuine
line-chart cover used to construct it. -/
theorem schemeSectionZeroScheme_cover_independent
    [Finite ι] [∀ i, QuasiCompact (U i).ι]
    [Finite κ] [∀ j, QuasiCompact (V j).ι]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) :
    schemeSectionZeroScheme φ U eU hU = schemeSectionZeroScheme φ V eV hV :=
  congrArg Scheme.IdealSheafData.subscheme
    (schemeSectionZeroIdeal_cover_independent φ U V eU eV hU hV)

/-- The canonical identification of the two constructed zero schemes. -/
def schemeSectionZeroSchemeCoverIso
    [Finite ι] [∀ i, QuasiCompact (U i).ι]
    [Finite κ] [∀ j, QuasiCompact (V j).ι]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) :
    schemeSectionZeroScheme φ U eU hU ≅ schemeSectionZeroScheme φ V eV hV :=
  eqToIso (schemeSectionZeroScheme_cover_independent φ U V eU eV hU hV)

private theorem subscheme_eqToIso_hom_ι (I J : X.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  subst J
  simp

/-- Cover independence preserves the actual closed immersion into the
original scheme, not merely the abstract isomorphism type of its source. -/
theorem schemeSectionZeroSchemeCoverIso_hom_ι
    [Finite ι] [∀ i, QuasiCompact (U i).ι]
    [Finite κ] [∀ j, QuasiCompact (V j).ι]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) :
    (schemeSectionZeroSchemeCoverIso φ U V eU eV hU hV).hom ≫
      schemeSectionZeroSchemeι φ V eV hV = schemeSectionZeroSchemeι φ U eU hU :=
  subscheme_eqToIso_hom_ι _ _ (schemeSectionZeroIdeal_cover_independent φ U V eU eV hU hV)

end Normalizer
