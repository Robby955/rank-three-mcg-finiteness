import Normalizer.SectionZeroCokernel
import Normalizer.SectionEvaluationMono
import Normalizer.LineGenericInjection
import Normalizer.DeterminantGenericNonzero
import Normalizer.ExteriorLineTrivialization
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The actual scalar exact sequence of a zero subscheme. For a nonzero
line section on an integral scheme this gives `0 → L∨ → O_X → i_*O_D → 0`.
All maps are the original evaluation and closed-subscheme structure maps. -/

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

/-- The actual line map and actual closed-subscheme structure quotient,
with their zero composite already proved on actual stalks. -/
def schemeSectionZeroComplex : ShortComplex X.Modules :=
  ShortComplex.mk φ (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU))
    (schemeSectionZeroQuotient_comp φ U e hU)

/-- The actual closed-subscheme quotient is an epimorphism, because the
constructed cokernel isomorphism identifies it with the cokernel projection. -/
theorem schemeSectionZeroQuotient_epi :
    Epi (closedSubschemeStructureMap (schemeSectionZeroIdeal φ U e hU)) := by
  rw [← schemeSectionZeroCokernelIso_π_hom φ U e hU]
  infer_instance

/-- The actual zero-scheme scalar complex is exact for every line map,
including maps that are not monic. -/
theorem schemeSectionZeroComplex_exact :
    (schemeSectionZeroComplex φ U e hU).Exact := by
  let a : ShortComplex.cokernelSequence φ ≅ schemeSectionZeroComplex φ U e hU :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (schemeSectionZeroCokernelIso φ U e hU)
      (by simp [schemeSectionZeroComplex])
      (by simpa [schemeSectionZeroComplex] using
        (schemeSectionZeroCokernelIso_π_hom φ U e hU).symm)
  exact ShortComplex.exact_of_iso a (ShortComplex.cokernelSequence_exact φ)

/-- For a monic line map, its actual zero-scheme scalar sequence is short exact. -/
theorem schemeSectionZeroComplex_shortExact [Mono φ] :
    (schemeSectionZeroComplex φ U e hU).ShortExact where
  exact := schemeSectionZeroComplex_exact φ U e hU
  mono_f := by change Mono φ; infer_instance
  epi_g := schemeSectionZeroQuotient_epi φ U e hU

variable (L) (s : Γ(L, ⊤))

/-- The actual scalar zero-scheme sequence associated to the specified
section uses its genuine dual sheaf and its actual evaluation map. -/
def schemeSectionDualZeroComplex : ShortComplex X.Modules :=
  schemeSectionZeroComplex (schemeSectionDualEvaluation L s) U
    (fun i => schemeDualLineFrameIso L (e i)) hU

/-- A nonzero section in genuine line charts on an integral scheme gives
the actual short exact sequence `0 → L∨ → O_X → i_*O_D → 0`. -/
theorem schemeSectionDualZeroComplex_shortExact [IsIntegral X] (hs : s ≠ 0) :
    (schemeSectionDualZeroComplex L U e hU s).ShortExact := by
  have hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨e i⟩⟩
  let : Mono (schemeSectionDualEvaluation L s) :=
    schemeSectionDualEvaluation_mono L s
      ((lineSheaf_genericGerm_ne_zero_iff L hcharts s).mpr hs) hcharts
  exact schemeSectionZeroComplex_shortExact _ U _ hU

/-- The specified determinant section gives the same actual short exact
sequence when its chosen section germs are independent over the function field. -/
theorem schemeDeterminantDualZeroComplex_shortExact [IsIntegral X]
    (H : X.Modules) (n : ℕ) (t : Fin n → Γ(H, ⊤))
    {I : Type u} [Fintype I] (j : I ≃ Fin n)
    (hframes : ∀ i, (schemeTrivialBundle X I).over (U i) ≅ H.over (U i))
    (ht : LinearIndependent X.functionField
      (fun a => H.presheaf.germ ⊤ (genericPoint X) (by trivial) (t a))) :
    (schemeSectionDualZeroComplex (schemeExteriorSheaf H n) U
      (fun i => bundleTopExteriorSheafIsoOver j (hframes i)) hU
      (schemeExteriorGlobalSection H n t)).ShortExact :=
  schemeSectionDualZeroComplex_shortExact _ U _ hU _
    (schemeExteriorGlobalSection_ne_zero H n t ht)

end Normalizer
