import Normalizer.CurveClosedSubscheme
import Normalizer.FiniteZeroDimensional
import Normalizer.SectionZeroSupport
import Normalizer.DeterminantZeroDivisor
import Normalizer.FiniteLineCharts
import Normalizer.FiniteSchemeSections
import Normalizer.SectionZeroLocus
import Normalizer.LineGenericInjection

/-! The actual zero scheme of a generically nonzero section on a finite-type
integral curve is finite over the field. The section and zero scheme are the
specified constructions from the preceding modules. -/

noncomputable section
namespace Normalizer
open CategoryTheory AlgebraicGeometry
universe u v

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]

/-- A closed subscheme omitting the generic point of a finite-type
integral curve is finite over the base field. -/
theorem closedSubscheme_isFinite_of_genericPoint_not_mem
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (i : Y ⟶ X) [IsClosedImmersion i] (hdim : topologicalKrullDim X ≤ 1)
    (hgeneric : genericPoint X ∉ Set.range i) : IsFinite (i ≫ p) :=
  scheme_isFinite_of_dim_le_zero (i ≫ p)
    (closedSubscheme_dimension_nonpos i hdim hgeneric)

variable (L : X.Modules) (s : Γ(L, ⊤))
  (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
  {ι : Type v} [Finite ι] (U : ι → X.Opens)
  [∀ i, QuasiCompact (U i).ι] (hU : iSup U = ⊤)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

include hs in
/-- The actual zero scheme of the specified section has dimension at most
zero. Its generic-point exclusion is derived from the specified section. -/
theorem schemeSectionZeroScheme_dimension_nonpos (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim (schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU) ≤ 0 := by
  have := schemeSectionZeroScheme_isClosedImmersion (schemeSectionDualEvaluation L s)
    U (fun i ↦ schemeDualLineFrameIso L (e i)) hU
  exact closedSubscheme_dimension_nonpos _ hdim
    (schemeSectionZeroScheme_genericPoint_not_mem_range L s hs U hU e)

include hs in
/-- The actual section zero scheme, with all of its nilpotent structure,
is finite over the base field on a finite-type integral curve. -/
theorem schemeSectionZeroScheme_isFinite
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsFinite (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p) := by
  have := schemeSectionZeroScheme_isClosedImmersion (schemeSectionDualEvaluation L s)
    U (fun i ↦ schemeDualLineFrameIso L (e i)) hU
  exact closedSubscheme_isFinite_of_genericPoint_not_mem p _ hdim
    (schemeSectionZeroScheme_genericPoint_not_mem_range L s hs U hU e)

include hs in
/-- In particular, the actual specified section zero scheme on a proper
integral curve is finite over the base field. -/
theorem properCurve_sectionZeroScheme_isFinite
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1) :
    IsFinite (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p) :=
  schemeSectionZeroScheme_isFinite L s hs U hU e p hdim

include hs in
/-- The actual global functions on the constructed zero scheme are
finite-dimensional under the action of the actual structure morphism. -/
theorem schemeSectionZeroScheme_globalFunctions_finiteDimensional
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    let pD := schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p
    let := schemeGlobalFunctionsAlgebra pD
    FiniteDimensional k Γ(schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU, ⊤) := by
  have := schemeSectionZeroScheme_isFinite L s hs U hU e p hdim
  exact finiteScheme_globalFunctions_finiteDimensional _

include hs in
/-- The actual zero-scheme function dimension vanishes exactly when
the constructed zero scheme is empty. This is not a line-bundle degree formula. -/
theorem schemeSectionZeroScheme_globalFunctions_finrank_eq_zero_iff
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    let pD := schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p
    let := schemeGlobalFunctionsAlgebra pD
    Module.finrank k Γ(schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU, ⊤) = 0 ↔
        IsEmpty (schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
          U (fun i ↦ schemeDualLineFrameIso L (e i)) hU) := by
  have := schemeSectionZeroScheme_isFinite L s hs U hU e p hdim
  exact finiteScheme_globalFunctions_finrank_eq_zero_iff _

include hs in
/-- A zero of the specified nonzero section gives a positive-dimensional
actual zero-scheme function space. No line-bundle degree is introduced. -/
theorem schemeSectionZeroScheme_globalFunctions_pos_of_zero
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) (i : ι)
    (V : X.Opens) (h : V ≤ U i) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e i) V h))) :
    let pD := schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p
    let := schemeGlobalFunctionsAlgebra pD
    0 < Module.finrank k Γ(schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU, ⊤) := by
  have := schemeSectionZeroScheme_isFinite L s hs U hU e p hdim
  have := schemeSectionZeroScheme_nonempty_of_nonunit L s U hU e i V h x hx hz
  exact finiteScheme_globalFunctions_finrank_pos _

include hs in
/-- On a proper integral curve, genuine pointwise line charts suffice:
the finite quasi-compact cover and finite actual zero scheme are constructed. -/
theorem properCurve_exists_finite_sectionZeroScheme
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V)) :
    ∃ (t : Finset X) (V : t → X.Opens) (hV : iSup V = ⊤)
      (hQC : ∀ a, QuasiCompact (V a).ι)
      (eV : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (V a) ≅ L.over (V a)),
      let := hQC
      IsFinite (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
        V (fun a ↦ schemeDualLineFrameIso L (eV a)) hV ≫ p) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨t, V, hV, hQC, ⟨eV⟩⟩ := exists_finite_quasiCompact_lineCharts L hlocal
  refine ⟨t, V, hV, hQC, eV, ?_⟩
  let := hQC
  exact properCurve_sectionZeroScheme_isFinite L s hs V hV eV p hdim

/-- Global nonzeroness suffices for the actual zero scheme to be finite:
the required generic nonzeroness is derived from the given covering charts. -/
theorem schemeSectionZeroScheme_isFinite_of_ne_zero (hs0 : s ≠ 0)
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsFinite (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p) := by
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V) := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨e i⟩⟩
  exact schemeSectionZeroScheme_isFinite L s
    ((lineSheaf_genericGerm_ne_zero_iff L hlocal s).mpr hs0) U hU e p hdim

/-- A zero of a globally nonzero section gives a positive-dimensional
actual zero-scheme function space, with generic nonzeroness derived. -/
theorem schemeSectionZeroScheme_globalFunctions_pos_of_ne_zero (hs0 : s ≠ 0)
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) (i : ι)
    (V : X.Opens) (h : V ≤ U i) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e i) V h))) :
    let pD := schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p
    let := schemeGlobalFunctionsAlgebra pD
    0 < Module.finrank k Γ(schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU, ⊤) := by
  have := schemeSectionZeroScheme_isFinite_of_ne_zero L s U hU e hs0 p hdim
  have := schemeSectionZeroScheme_nonempty_of_nonunit L s U hU e i V h x hx hz
  exact finiteScheme_globalFunctions_finrank_pos _

/-- A nonzero global section and genuine pointwise line charts on a proper
integral curve construct a finite cover and an actual finite zero scheme. -/
theorem properCurve_exists_finite_sectionZeroScheme_of_ne_zero (hs0 : s ≠ 0)
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V)) :
    ∃ (t : Finset X) (V : t → X.Opens) (hV : iSup V = ⊤)
      (hQC : ∀ a, QuasiCompact (V a).ι)
      (eV : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (V a) ≅ L.over (V a)),
      let := hQC
      IsFinite (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
        V (fun a ↦ schemeDualLineFrameIso L (eV a)) hV ≫ p) :=
  properCurve_exists_finite_sectionZeroScheme L s
    ((lineSheaf_genericGerm_ne_zero_iff L hlocal s).mpr hs0) p hdim hlocal

variable (H : X.Modules) (n : ℕ) (sH : Fin n → Γ(H, ⊤))
  {I : Type u} [Fintype I] (j : I ≃ Fin n)
  (eH : ∀ i, (schemeTrivialBundle X I).over (U i) ≅ H.over (U i))

/-- The actual determinant zero scheme is finite over the field; its
generic nonzeroness and line charts are derived from the specified family
and genuine rank-n charts. -/
theorem schemeDeterminantZeroScheme_isFinite
    (hsH : LinearIndependent X.functionField
      (fun a ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (sH a)))
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsFinite ((schemeDeterminantZeroIdeal H n sH j U eH hU).subschemeι ≫ p) :=
  schemeSectionZeroScheme_isFinite _ _
    (schemeExteriorGlobalSection_generic_ne_zero H n sH hsH)
    U hU (fun i ↦ bundleTopExteriorSheafIsoOver j (eH i)) p hdim

/-- A zero of the actual specified determinant gives positive dimension
of the global functions on its actual finite zero scheme. The comparison
with the established line-bundle degree remains a separate theorem. -/
theorem schemeDeterminantZeroScheme_globalFunctions_pos_of_zero
    (hsH : LinearIndependent X.functionField
      (fun a ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (sH a)))
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) (i : ι)
    (V : X.Opens) (h : V ≤ U i) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx
      (sectionLocalEquation (schemeExteriorSheaf H n) (schemeExteriorGlobalSection H n sH)
        (bundleTopExteriorSheafIsoOver j (eH i)) V h))) :
    let pD := (schemeDeterminantZeroIdeal H n sH j U eH hU).subschemeι ≫ p
    let := schemeGlobalFunctionsAlgebra pD
    0 < Module.finrank k Γ((schemeDeterminantZeroIdeal H n sH j U eH hU).subscheme, ⊤) :=
  schemeSectionZeroScheme_globalFunctions_pos_of_zero _ _
    (schemeExteriorGlobalSection_generic_ne_zero H n sH hsH)
    U hU (fun a ↦ bundleTopExteriorSheafIsoOver j (eH a)) p hdim i V h x hx hz

end Normalizer
