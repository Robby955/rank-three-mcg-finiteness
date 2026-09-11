import Normalizer.SectionZeroScheme

/-! The actual global zero ideal agrees with sectionwise image ideals on
affine subopens of its genuine line-chart cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u v
variable {X : Scheme.{u}} {L : X.Modules}
  (φ : L ⟶ SheafOfModules.unit X.ringCatSheaf)
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ i, QuasiCompact (U i).ι]
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))
  (hU : iSup U = ⊤)

/-- On an affine open of a genuine chart, the glued ideal is exactly the
actual sectionwise image of the original module-sheaf morphism. -/
theorem schemeSectionZeroIdeal_ideal_image (i : ι) (V : (U i).toScheme.affineOpens) :
    (schemeSectionZeroIdeal φ U e hU).ideal
      ⟨(U i).ι ''ᵁ V.1, V.2.image_of_isOpenImmersion (U i).ι⟩ =
        schemeSectionImageIdeal φ ((U i).ι ''ᵁ V.1) := by
  have h := congrArg (fun I ↦ I.ideal V) (schemeSectionZeroIdeal_comap φ U e hU i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso] at h
  change Ideal.comap (RingHom.id _) _ = schemeSectionImageIdeal φ ((U i).ι ''ᵁ V.1) at h
  simpa only [Ideal.comap_id] using h

/-- On every actual affine subopen of a chosen genuine chart, the global
zero ideal is the image of the actual section map. -/
theorem schemeSectionZeroIdeal_ideal_of_le (i : ι) (V : X.affineOpens)
    (hV : V.1 ≤ U i) :
    (schemeSectionZeroIdeal φ U e hU).ideal V = schemeSectionImageIdeal φ V.1 := by
  let W : (U i).toScheme.affineOpens :=
    ⟨(U i).ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion (U i).ι (by simpa using hV)⟩
  have himg : (U i).ι ''ᵁ W.1 = V.1 := by
    change (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V.1) = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  have h := schemeSectionZeroIdeal_ideal_image φ U e hU i W
  have heq : (⟨(U i).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion (U i).ι⟩ : X.affineOpens) = V :=
    Subtype.ext himg
  exact Eq.mp (congrArg (fun Q : X.affineOpens ↦
    (schemeSectionZeroIdeal φ U e hU).ideal Q = schemeSectionImageIdeal φ Q.1) heq) h

/-- The kernel of the actual zero-subscheme ring map is exactly the
sectionwise image ideal on affine subopens of genuine charts. -/
theorem schemeSectionZeroSchemeι_app_ker (i : ι) (V : X.affineOpens)
    (hV : V.1 ≤ U i) :
    RingHom.ker ((schemeSectionZeroSchemeι φ U e hU).app V.1).hom =
      schemeSectionImageIdeal φ V.1 := by
  change RingHom.ker ((schemeSectionZeroIdeal φ U e hU).subschemeι.app V.1).hom = _
  rw [Scheme.IdealSheafData.ker_subschemeι_app,
    schemeSectionZeroIdeal_ideal_of_le φ U e hU i V hV]

/-- A scalar restricts to zero on the actual zero subscheme exactly when
it is the image of an actual section of the source line sheaf. -/
theorem schemeSectionZeroSchemeι_app_eq_zero_iff (i : ι) (V : X.affineOpens)
    (hV : V.1 ≤ U i) (a : Γ(X, V.1)) :
    (schemeSectionZeroSchemeι φ U e hU).app V.1 a = 0 ↔
      ∃ s : Γ(L, V.1), φ.val.app (op V.1) s = a := by
  change a ∈ RingHom.ker ((schemeSectionZeroSchemeι φ U e hU).app V.1).hom ↔ _
  rw [schemeSectionZeroSchemeι_app_ker φ U e hU i V hV]
  exact mem_schemeSectionImageIdeal φ V.1 a

end Normalizer
