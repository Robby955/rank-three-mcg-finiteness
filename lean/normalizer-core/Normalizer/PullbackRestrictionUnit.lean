import Normalizer.LineRestrictionUnit

/-! Unit compatibility for the actual pullback/open-restriction square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

private theorem unit_compat_trans
    {C D : Type*} [Category C] [Category D]
    {G₁ G₂ G₃ : D ⥤ C} {A B E : D} {x : C}
    (η₁ : x ⟶ G₁.obj A) (η₂ : x ⟶ G₂.obj B) (η₃ : x ⟶ G₃.obj E)
    (a : A ⟶ B) (b : B ⟶ E) (r : G₁ ⟶ G₂) (t : G₂ ⟶ G₃)
    (h₁ : η₁ ≫ G₁.map a ≫ r.app B = η₂)
    (h₂ : η₂ ≫ G₂.map b ≫ t.app E = η₃) :
    η₁ ≫ G₁.map (a ≫ b) ≫ (r ≫ t).app E = η₃ := by
  rw [Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [← Category.assoc (G₁.map b) (r.app E), r.naturality]
  rw [← h₁] at h₂
  simpa only [Category.assoc] using h₂

/-- The forward pullback-composition comparison transports the composed
actual adjunction unit to the unit for the composite scheme morphism. -/
theorem schemePullbackComp_hom_unit_compatibility {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M ≫
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackComp f g).hom.app M) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((Scheme.Modules.pullback (f ≫ g)).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  rw [(Scheme.Modules.pushforwardComp f g).hom.naturality,
    ← Category.assoc, schemePullbackComp_unit_compatibility, Category.assoc,
    ← Functor.map_comp]
  simp

variable {X D : Scheme.{u}} (i : D ⟶ X) (U : X.Opens)

/-- The canonical pushforward isomorphism around the actual open-restriction square. -/
def schemePushforwardRestrictionSquareIso :
    Scheme.Modules.pushforward (i ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward i ≅
      Scheme.Modules.pushforward (i ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (i ⁻¹ᵁ U).ι i ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι i U).symm ≪≫
      (Scheme.Modules.pushforwardComp (i ∣_ U) U.ι).symm

/-- The canonical pushforward square comparison transports actual sections along the
proved equality of the two inverse-image opens. -/
theorem schemePushforwardRestrictionSquareIso_hom_app
    (M : (i ⁻¹ᵁ U).toScheme.Modules) (W : X.Opens) :
    ((schemePushforwardRestrictionSquareIso i U).hom.app M).app W =
      M.presheaf.map (eqToHom (congrArg (fun f : (i ⁻¹ᵁ U).toScheme ⟶ X ↦ f ⁻¹ᵁ W)
        (morphismRestrict_ι i U))).op := by
  simp only [schemePushforwardRestrictionSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id]

/-- The actual pullback/restriction comparison transports the actual
composite adjunction units around the commuting scheme square. -/
theorem schemePullbackRestrictIso_unit_compatibility (L : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
      (Scheme.Modules.restrictAdjunction (i ⁻¹ᵁ U).ι)).unit.app L ≫
        (Scheme.Modules.pushforward (i ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward i).map
          (schemePullbackRestrictIso i L U).hom ≫
        (schemePushforwardRestrictionSquareIso i U).hom.app
          ((Scheme.Modules.pullback (i ∣_ U)).obj (L.restrict U.ι)) =
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U))).unit.app L := by
  let f := (i ⁻¹ᵁ U).ι
  let j := i ∣_ U
  let u := U.ι
  let P := (Scheme.Modules.pullback i).obj L
  let A₀ := ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
    (Scheme.Modules.restrictAdjunction f)).unit.app L
  let A₁ := ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app L
  let A₂ := (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ i)).unit.app L
  let A₃ := (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ u)).unit.app L
  let A₄ := ((Scheme.Modules.pullbackPushforwardAdjunction u).comp
    (Scheme.Modules.pullbackPushforwardAdjunction j)).unit.app L
  let A₅ := ((Scheme.Modules.restrictAdjunction u).comp
    (Scheme.Modules.pullbackPushforwardAdjunction j)).unit.app L
  let G₀ : (i ⁻¹ᵁ U).toScheme.Modules ⥤ X.Modules := Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward i
  let G₂ : (i ⁻¹ᵁ U).toScheme.Modules ⥤ X.Modules := Scheme.Modules.pushforward (f ≫ i)
  let G₃ : (i ⁻¹ᵁ U).toScheme.Modules ⥤ X.Modules := Scheme.Modules.pushforward (j ≫ u)
  let G₄ : (i ⁻¹ᵁ U).toScheme.Modules ⥤ X.Modules := Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward u
  let a := (Scheme.Modules.restrictFunctorIsoPullback f).hom.app P
  let b := (Scheme.Modules.pullbackComp f i).hom.app L
  let c := (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).hom.app L
  let d := (Scheme.Modules.pullbackComp j u).inv.app L
  let q := (Scheme.Modules.pullback j).map
    ((Scheme.Modules.restrictFunctorIsoPullback u).inv.app L)
  let r := (Scheme.Modules.pushforwardComp f i).hom
  let t := (Scheme.Modules.pushforwardCongr (morphismRestrict_ι i U).symm).hom
  let w := (Scheme.Modules.pushforwardComp j u).inv
  have h₀₁ : A₀ ≫ G₀.map a ≫ (𝟙 G₀ : G₀ ⟶ G₀).app _ = A₁ := by
    dsimp only [A₀, A₁, G₀, a, Functor.comp_map, NatTrans.id_app]
    simp only [Adjunction.comp_unit_app]
    rw [Category.comp_id, Category.assoc, ← Functor.map_comp,
      schemeOpenRestriction_unit_compatibility]
  have h₁₂ : A₁ ≫ G₀.map b ≫ r.app _ = A₂ :=
    schemePullbackComp_hom_unit_compatibility f i L
  have h₂₃ : A₂ ≫ G₂.map c ≫ t.app _ = A₃ :=
    schemePullbackCongr_unit_compatibility (morphismRestrict_ι i U).symm L
  have h₃₄ : A₃ ≫ G₃.map d ≫ w.app _ = A₄ := by
    dsimp only [A₃, A₄, G₃, d, w]
    rw [← Category.assoc, ← schemePullbackComp_unit_compatibility, Category.assoc]
    simp
  have h₄₅ : A₄ ≫ G₄.map q ≫ (𝟙 G₄ : G₄ ⟶ G₄).app _ = A₅ := by
    dsimp only [A₄, A₅, G₄, q, Functor.comp_map, NatTrans.id_app]
    simp only [Adjunction.comp_unit_app]
    rw [Category.comp_id, Category.assoc, ← Functor.map_comp]
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback u).inv.app L)
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn]
    rw [Functor.map_comp, ← Category.assoc, schemeOpenRestriction_inv_unit_compatibility]
  have h₀₂ := unit_compat_trans (G₁ := G₀) (G₂ := G₀) (G₃ := G₂) A₀ A₁ A₂ a b (𝟙 G₀) r h₀₁ h₁₂
  have h₀₃ := unit_compat_trans (G₁ := G₀) (G₂ := G₂) (G₃ := G₃) A₀ A₂ A₃ (a ≫ b) c ((𝟙 G₀) ≫ r) t h₀₂ h₂₃
  have h₀₄ := unit_compat_trans (G₁ := G₀) (G₂ := G₃) (G₃ := G₄) A₀ A₃ A₄ ((a ≫ b) ≫ c) d (((𝟙 G₀) ≫ r) ≫ t) w h₀₃ h₃₄
  have h₀₅ := unit_compat_trans (G₁ := G₀) (G₂ := G₄) (G₃ := G₄) A₀ A₄ A₅ (((a ≫ b) ≫ c) ≫ d) q
    ((((𝟙 G₀) ≫ r) ≫ t) ≫ w) (𝟙 G₄) h₀₄ h₄₅
  simpa only [A₀, A₅, G₀, G₄, a, b, c, d, q, r, t, w, f, j, u, P,
    schemePullbackRestrictIso, schemePushforwardRestrictionSquareIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.comp_obj, Functor.mapIso_hom, Category.id_comp,
    Category.comp_id, Category.assoc] using h₀₅

set_option maxHeartbeats 800000 in
/-- On every actual open of the restricted scheme, the comparison takes the
transported pullback-unit section to the actual local pullback-unit section. -/
theorem schemePullbackRestrictIso_unit_app (L : X.Modules) (W : U.toScheme.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).app (U.ι ''ᵁ W) ≫
      ((Scheme.Modules.pullback i).obj L).presheaf.map
        (eqToHom (image_morphismRestrict_preimage i U W)).op ≫
      (schemePullbackRestrictIso i L U).hom.app ((i ∣_ U) ⁻¹ᵁ W) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U)).unit.app
          (L.restrict U.ι)).app W := by
  have h := congrArg (fun f ↦ f.app (U.ι ''ᵁ W))
    (schemePullbackRestrictIso_unit_compatibility i U L)
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app,
    Functor.comp_map, Scheme.Modules.pushforward_map_app,
    schemePushforwardRestrictionSquareIso_hom_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h
  let B := (Scheme.Modules.pullback (i ∣_ U)).obj (L.restrict U.ι)
  let V₀ := U.ι ⁻¹ᵁ (U.ι ''ᵁ W)
  let g : op V₀ ⟶ op W := (eqToHom (U.ι.preimage_image_eq W).symm).op
  let q := (eqToHom (congrArg (fun f : (i ⁻¹ᵁ U).toScheme ⟶ X ↦
    f ⁻¹ᵁ (U.ι ''ᵁ W)) (morphismRestrict_ι i U))).op
  let gD := ((TopologicalSpace.Opens.map (i ∣_ U).base).map g.unop).op
  have h' := congrArg (fun z ↦ z ≫ B.presheaf.map gD) h
  simp only [Category.assoc] at h'
  have hn := (schemePullbackRestrictIso i L U).hom.mapPresheaf.naturality (q ≫ gD)
  simp only [Scheme.Modules.mapPresheaf_app] at hn
  have hn₂ := ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U)).unit.app
    (L.restrict U.ι)).mapPresheaf.naturality g
  simp only [Scheme.Modules.mapPresheaf_app] at hn₂
  change (L.restrict U.ι).presheaf.map g ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U)).unit.app
        (L.restrict U.ι)).app W =
    ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U)).unit.app
        (L.restrict U.ι)).app V₀ ≫ B.presheaf.map gD at hn₂
  rw [← B.presheaf.map_comp] at h'
  let P := (Scheme.Modules.pullback i).obj L
  let A := ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).app (U.ι ''ᵁ W)
  let R₀ := P.presheaf.map
    (homOfLE ((i ⁻¹ᵁ U).ι.image_preimage_le (i ⁻¹ᵁ (U.ι ''ᵁ W)))).op
  let L₀ := L.presheaf.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ W))).op
  have hp := congrArg (fun z ↦ A ≫ R₀ ≫ z) hn
  have ht := congrArg (fun z ↦ L₀ ≫ z) hn₂.symm
  have hh := hp.trans h'
  have hh' := hh.trans ht
  simp only [← Category.assoc] at hh'
  have hP : R₀ ≫ (P.restrict (i ⁻¹ᵁ U).ι).presheaf.map (q ≫ gD) =
      P.presheaf.map (eqToHom (image_morphismRestrict_preimage i U W)).op := by
    change P.presheaf.map _ ≫ P.presheaf.map
      ((i ⁻¹ᵁ U).ι.opensFunctor.map (q ≫ gD).unop).op = _
    rw [← P.presheaf.map_comp]
    rfl
  have hL : L₀ ≫ (L.restrict U.ι).presheaf.map g = 𝟙 _ := by
    change L.presheaf.map _ ≫ L.presheaf.map (U.ι.opensFunctor.map g.unop).op = 𝟙 _
    rw [← L.presheaf.map_comp]
    exact L.presheaf.map_id _
  have hl := congrArg (fun z ↦ A ≫ z ≫ (schemePullbackRestrictIso i L U).hom.app
    ((i ∣_ U) ⁻¹ᵁ W)) hP
  have hr := congrArg (fun z ↦ z ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction (i ∣_ U)).unit.app
      (L.restrict U.ι)).app W) hL
  simp only [Category.id_comp, Category.assoc] at hl hr hh'
  exact hl.symm.trans (hh'.trans hr)

end Normalizer
