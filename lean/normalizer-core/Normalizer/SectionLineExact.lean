import Normalizer.SectionZeroExact
import Normalizer.SectionHomMono
import Normalizer.LineRestrictionCompatibility
import Normalizer.FiniteLineCharts
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! The actual line restriction sequence at the zero scheme of a specified
section, compared with the scalar zero-scheme sequence in genuine line charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits
universe u v
variable {X : Scheme.{u}}

/-- An actual commutative square of local sheaf maps gives the corresponding
commutative square on the actual stalk, by the germ formulas. -/
theorem schemeLocalStalkMap_square {A B C D : X.Modules} {W : X.Opens}
    (f : A ⟶ B) (g : C ⟶ D)
    (a : A.over W ⟶ C.over W) (b : B.over W ⟶ D.over W)
    (h : f.over W ≫ b = a ≫ g.over W) (x : X) (hx : x ∈ W)
    (z : A.presheaf.stalk x) :
    schemeLocalStalkMap b x hx (schemeModuleStalkMap f x z) =
      schemeModuleStalkMap g x (schemeLocalStalkMap a x hx z) := by
  obtain ⟨V, hVW, hxV, z, rfl⟩ := A.presheaf.exists_le_germ_eq z hx
  rw [schemeModuleStalkMap_germ, schemeLocalStalkMap_germ _ x hx V hVW,
    schemeLocalStalkMap_germ _ x hx V hVW, schemeModuleStalkMap_germ]
  exact congrArg (D.presheaf.germ V x hxV)
    (congrArg (fun q : A.over W ⟶ D.over W =>
      q.val.app (op (Over.mk (homOfLE hVW))) z) h)

variable (L : X.Modules) (s : Γ(L, ⊤))

/-- In the same genuine chart, multiplication by the prescribed section
and dual evaluation have the same scalar expression. -/
theorem schemeSectionHom_dualEvaluation_chart {W : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) :
    (schemeSectionHom L s).over W ≫ e.inv =
      (schemeDualLineFrameIso L e).hom ≫ (schemeSectionDualEvaluation L s).over W := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change e.inv.val.app (op (Over.mk (homOfLE (leOfHom V.unop.hom))))
      ((schemeSectionHom L s).val.app (op V.unop.left) r) =
    schemeSectionDualEvaluationAt L s V.unop.left
      (moduleLineFrameAt (schemeDualSheaf L) (schemeDualLineFrameIso L e)
        V.unop.left (leOfHom V.unop.hom) r)
  rw [schemeSectionHom_coordinate, schemeSectionDualEvaluation_frame,
    schemeDualLineFrameIso_coordinate]
  exact @mul_comm Γ(X, V.unop.left) _ (r : Γ(X, V.unop.left))
    (sectionLocalEquation L s e V.unop.left (leOfHom V.unop.hom))

/-- The actual line-chart square relating section multiplication and dual
evaluation commutes on the ambient stalk. -/
theorem schemeSectionHom_dualEvaluation_stalk {W : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)
    (x : X) (hx : x ∈ W)
    (z : (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x) :
    schemeLocalStalkMap e.inv x hx (schemeModuleStalkMap (schemeSectionHom L s) x z) =
      schemeModuleStalkMap (schemeSectionDualEvaluation L s) x
        (schemeLocalStalkMap (schemeDualLineFrameIso L e).hom x hx z) :=
  schemeLocalStalkMap_square _ _ _ _ (schemeSectionHom_dualEvaluation_chart L s e) x hx z

variable {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ i, QuasiCompact (U i).ι]
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))
  (hU : iSup U = ⊤)

/-- The actual restriction of the line bundle to its section's zero scheme,
pushed forward to the ambient scheme. -/
def schemeSectionLineRestrictionSheaf : X.Modules :=
  (Scheme.Modules.pushforward (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
    U (fun i => schemeDualLineFrameIso L (e i)) hU)).obj
      ((Scheme.Modules.pullback (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
        U (fun i => schemeDualLineFrameIso L (e i)) hU)).obj L)

/-- The actual restriction map is the unit of the pullback-pushforward
adjunction for the actual zero-scheme closed immersion. -/
def schemeSectionLineRestrictionMap : L ⟶ schemeSectionLineRestrictionSheaf L s U e hU :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i => schemeDualLineFrameIso L (e i)) hU)).unit.app L

private theorem sectionLine_stalk_conditions
    {R : X.Modules} (q : L ⟶ R) {W : X.Opens}
    (fW : (SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)
    (cW : R.over W ≅ (closedSubschemeStructureSheaf
      (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
        (fun i => schemeDualLineFrameIso L (e i)) hU)).over W)
    (hcW : q.over W ≫ cW.hom = fW.inv ≫
      (closedSubschemeStructureMap (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s)
        U (fun i => schemeDualLineFrameIso L (e i)) hU)).over W)
    (x : X) (hxW : x ∈ W) :
    Function.Surjective (schemeModuleStalkMap q x) ∧
    (∀ a, schemeModuleStalkMap q x (schemeModuleStalkMap (schemeSectionHom L s) x a) = 0) ∧
    (∀ b, schemeModuleStalkMap q x b = 0 →
      ∃ a, schemeModuleStalkMap (schemeSectionHom L s) x a = b) := by
  let α := schemeLocalStalkEquiv (schemeDualLineFrameIso L fW) x hxW
  let β := schemeLocalStalkEquiv fW.symm x hxW
  let γ := schemeLocalStalkEquiv cW x hxW
  let I := schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
    (fun i => schemeDualLineFrameIso L (e i)) hU
  let q₀ := closedSubschemeStructureMap I
  have hleft (a) : β (schemeModuleStalkMap (schemeSectionHom L s) x a) =
      schemeModuleStalkMap (schemeSectionDualEvaluation L s) x (α a) :=
    schemeSectionHom_dualEvaluation_stalk L s fW x hxW a
  have hright (b) : γ (schemeModuleStalkMap q x b) = schemeModuleStalkMap q₀ x (β b) :=
    schemeLocalStalkMap_square q q₀ fW.inv cW.hom hcW x hxW b
  constructor
  · intro z
    obtain ⟨b, hb⟩ := closedSubschemeStructureMap_stalk_surjective I x (γ z)
    refine ⟨β.symm b, γ.injective ?_⟩
    rw [hright, LinearEquiv.apply_symm_apply, hb]
  constructor
  · intro a
    apply γ.injective
    rw [hright, hleft, map_zero]
    exact schemeSectionZeroQuotient_stalk_comp (schemeSectionDualEvaluation L s)
      U (fun i => schemeDualLineFrameIso L (e i)) hU x (α a)
  · intro b hb
    have hb' : schemeModuleStalkMap q₀ x (β b) = 0 := by
      rw [← hright, hb, map_zero]
    obtain ⟨a, ha⟩ := schemeSectionZeroQuotient_stalk_exact (schemeSectionDualEvaluation L s)
      U (fun i => schemeDualLineFrameIso L (e i)) hU x (β b) hb'
    refine ⟨α.symm a, β.injective ?_⟩
    rw [hleft, LinearEquiv.apply_symm_apply, ha]

/-- The actual restriction map has the scalar quotient expression in
any genuine line chart, by the proved adjunction compatibility. -/
theorem schemeSectionLineRestriction_chart {W : X.Opens}
    (fW : (SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) :
    (schemeSectionLineRestrictionMap L s U e hU).over W ≫
      (schemeLineRestrictionComparison
        (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
          (fun i => schemeDualLineFrameIso L (e i)) hU) L W fW).hom =
      fW.inv ≫ (closedSubschemeStructureMap
        (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
          (fun i => schemeDualLineFrameIso L (e i)) hU)).over W := by
  apply (cancel_epi fW.hom).mp
  simpa only [schemeSectionLineRestrictionMap, closedSubschemeStructureMap,
    schemeSectionZeroSchemeι, SheafOfModules.Hom.over,
    Category.assoc, Iso.hom_inv_id_assoc] using
    (schemeLineRestrictionComparison_unit_compatibility
      (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
        (fun i => schemeDualLineFrameIso L (e i)) hU) L W fW)

private theorem sectionLine_actual_stalk_conditions (x : X) :
    Function.Surjective (schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x) ∧
    (∀ a, schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x
      (schemeModuleStalkMap (schemeSectionHom L s) x a) = 0) ∧
    (∀ b, schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x b = 0 →
      ∃ a, schemeModuleStalkMap (schemeSectionHom L s) x a = b) := by
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact sectionLine_stalk_conditions L s U e hU (schemeSectionLineRestrictionMap L s U e hU)
    (e i) (schemeLineRestrictionComparison
      (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
        (fun i => schemeDualLineFrameIso L (e i)) hU) L (U i) (e i))
    (schemeSectionLineRestriction_chart L s U e hU (e i)) x hi

/-- Restriction of the line sheaf to the actual zero scheme is surjective
on each actual stalk. -/
theorem schemeSectionLineRestriction_stalk_surjective (x : X) :
    Function.Surjective (schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x) :=
  (sectionLine_actual_stalk_conditions L s U e hU x).1

/-- Section multiplication followed by actual zero-scheme restriction
vanishes on every actual stalk. -/
theorem schemeSectionLineRestriction_stalk_comp (x : X) (a) :
    schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x
      (schemeModuleStalkMap (schemeSectionHom L s) x a) = 0 :=
  (sectionLine_actual_stalk_conditions L s U e hU x).2.1 a

/-- The actual kernel of line restriction on a stalk is exactly the image
of multiplication by the specified section. -/
theorem schemeSectionLineRestriction_stalk_ker_eq_range (x : X) :
    LinearMap.ker (schemeModuleStalkMap (schemeSectionLineRestrictionMap L s U e hU) x) =
      LinearMap.range (schemeModuleStalkMap (schemeSectionHom L s) x) := by
  ext b
  constructor
  · exact (sectionLine_actual_stalk_conditions L s U e hU x).2.2 b
  · rintro ⟨a, rfl⟩
    exact schemeSectionLineRestriction_stalk_comp L s U e hU x a

/-- The specified section vanishes after actual restriction to its zero
scheme as a morphism of sheaves, not merely after a chosen scalar identification. -/
theorem schemeSectionLineRestriction_comp :
    schemeSectionHom L s ≫ schemeSectionLineRestrictionMap L s U e hU = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let Q := schemeSectionLineRestrictionSheaf L s U e hU
  change (schemeSectionLineRestrictionMap L s U e hU).val.app V
    ((schemeSectionHom L s).val.app V a) = (0 : Γ(Q, V.unop))
  apply TopCat.Presheaf.section_ext ⟨Q.presheaf, Q.isSheaf⟩ V.unop _ 0
  intro x hx
  have h := schemeSectionLineRestriction_stalk_comp L s U e hU x
    ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ V.unop x hx a)
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ] at h
  change Q.presheaf.germ V.unop x hx
    ((schemeSectionLineRestrictionMap L s U e hU).val.app V
      ((schemeSectionHom L s).val.app V a)) = 0 at h
  simpa only [map_zero] using h

/-- The actual cokernel of section multiplication is the actual
pushforward of the line bundle restricted to its zero scheme. -/
def schemeSectionLineCokernelIso :
    cokernel (schemeSectionHom L s) ≅ schemeSectionLineRestrictionSheaf L s U e hU :=
  sheafCokernelComparisonIso _ _ (schemeSectionLineRestriction_comp L s U e hU)
    (schemeSectionLineRestriction_stalk_surjective L s U e hU)
    (schemeSectionLineRestriction_stalk_ker_eq_range L s U e hU)

/-- The cokernel comparison preserves the canonical quotient map and
the actual adjunction restriction map. -/
theorem schemeSectionLineCokernelIso_π_hom :
    cokernel.π (schemeSectionHom L s) ≫ (schemeSectionLineCokernelIso L s U e hU).hom =
      schemeSectionLineRestrictionMap L s U e hU :=
  sheafCokernelComparisonIso_π_hom _ _ (schemeSectionLineRestriction_comp L s U e hU)
    (schemeSectionLineRestriction_stalk_surjective L s U e hU)
    (schemeSectionLineRestriction_stalk_ker_eq_range L s U e hU)

/-- The actual zero-scheme restriction map is an epimorphism of sheaves. -/
theorem schemeSectionLineRestriction_epi : Epi (schemeSectionLineRestrictionMap L s U e hU) := by
  rw [← schemeSectionLineCokernelIso_π_hom L s U e hU]
  infer_instance

/-- The actual section-multiplication and zero-scheme restriction complex. -/
def schemeSectionLineComplex : ShortComplex X.Modules :=
  ShortComplex.mk (schemeSectionHom L s) (schemeSectionLineRestrictionMap L s U e hU)
    (schemeSectionLineRestriction_comp L s U e hU)

/-- The actual line restriction sequence is exact even without a
nonzero-section or integrality hypothesis. -/
theorem schemeSectionLineComplex_exact : (schemeSectionLineComplex L s U e hU).Exact := by
  let a : ShortComplex.cokernelSequence (schemeSectionHom L s) ≅
      schemeSectionLineComplex L s U e hU :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (schemeSectionLineCokernelIso L s U e hU)
      (by simp [schemeSectionLineComplex])
      (by simpa [schemeSectionLineComplex] using
        (schemeSectionLineCokernelIso_π_hom L s U e hU).symm)
  exact ShortComplex.exact_of_iso a (ShortComplex.cokernelSequence_exact _)

/-- A nonzero line section on an integral scheme gives the actual short
exact sequence `0 → O_X → L → i_*i^*L → 0` for its constructed zero scheme. -/
theorem schemeSectionLineComplex_shortExact [IsIntegral X] (hs : s ≠ 0) :
    (schemeSectionLineComplex L s U e hU).ShortExact := by
  have hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨e i⟩⟩
  let : Mono (schemeSectionHom L s) := schemeSectionHom_mono L s hs hcharts
  exact ShortComplex.ShortExact.mk' (schemeSectionLineComplex_exact L s U e hU)
    (show Mono (schemeSectionLineComplex L s U e hU).f from by
      change Mono (schemeSectionHom L s)
      infer_instance)
    (schemeSectionLineRestriction_epi L s U e hU)

/-- The specified determinant section produces the actual line restriction
short exact sequence when its chosen generic germs are independent. -/
theorem schemeDeterminantLineComplex_shortExact [IsIntegral X]
    (H : X.Modules) (n : ℕ) (t : Fin n → Γ(H, ⊤))
    {I : Type u} [Fintype I] (j : I ≃ Fin n)
    (hframes : ∀ i, (schemeTrivialBundle X I).over (U i) ≅ H.over (U i))
    (ht : LinearIndependent X.functionField
      (fun a => H.presheaf.germ ⊤ (genericPoint X) (by trivial) (t a))) :
    (schemeSectionLineComplex (schemeExteriorSheaf H n) (schemeExteriorGlobalSection H n t)
      U (fun i => bundleTopExteriorSheafIsoOver j (hframes i)) hU).ShortExact :=
  schemeSectionLineComplex_shortExact _ _ U _ hU
    (schemeExteriorGlobalSection_ne_zero H n t ht)

/-- On an integral proper scheme over a field, pointwise genuine line
charts suffice: the finite quasi-compact cover and the actual line restriction
short exact sequence are constructed. No dimension hypothesis is needed. -/
theorem properScheme_exists_sectionLine_shortExact [IsIntegral X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hs : s ≠ 0)
    (hlocal : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)) :
    ∃ (t : Finset X) (V : t → X.Opens) (hV : iSup V = ⊤)
      (hQC : ∀ a, QuasiCompact (V a).ι)
      (eV : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (V a) ≅ L.over (V a)),
      let := hQC
      (schemeSectionLineComplex L s V eV hV).ShortExact := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨t, V, hV, hQC, ⟨eV⟩⟩ := exists_finite_quasiCompact_lineCharts L hlocal
  refine ⟨t, V, hV, hQC, eV, ?_⟩
  let := hQC
  exact schemeSectionLineComplex_shortExact L s V eV hV hs

end Normalizer
