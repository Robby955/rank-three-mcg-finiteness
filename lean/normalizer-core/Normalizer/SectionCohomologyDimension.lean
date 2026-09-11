import Normalizer.SectionCohomologyLinear
import Normalizer.ProperLineSectionsFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite kernels and the exact dimension balance of the actual section
cohomology sequence. The whole H¹ spaces need not be finite-dimensional. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Limits Abelian
universe u v
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of k)) (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤) (hs : s ≠ 0)

local notation "O" => SheafOfModules.unit X.ringCatSheaf
local notation "R" => schemeSectionLineRestrictionSheaf L s U e hU
local notation "T" => schemeModulesToAbelianSheaves X
local notation "H⁰(" M ")" => CategoryTheory.Sheaf.H (CategoryTheory.Functor.obj (schemeModulesToAbelianSheaves X) M) 0
local notation "H¹(" M ")" => CategoryTheory.Sheaf.H (CategoryTheory.Functor.obj (schemeModulesToAbelianSheaves X) M) 1
local notation "d" => schemeSectionLineCohomologyδLinear p L s U e hU hs
local notation "f" => schemeModuleCohomologyMap p (schemeSectionHom L s) 1
local notation "g" => schemeModuleCohomologyMap p (schemeSectionLineRestrictionMap L s U e hU) 0

/-- Exactness at the actual H¹(O_X) identifies the section map's kernel
with the range of the actual connecting map, as base-field submodules. -/
theorem schemeSectionLineH1_ker_eq_rangeδ :
    letI := schemeModuleCohomologyModule p O 1
    letI := schemeModuleCohomologyModule p L 1
    letI := schemeModuleCohomologyModule p R 0
    (f).ker = (d).range := by
  let := schemeModuleCohomologyModule p O 1
  let := schemeModuleCohomologyModule p L 1
  let := schemeModuleCohomologyModule p R 0
  ext x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₁ _
      (schemeSectionLineAbelianComplex_shortExact L s U e hU hs) x hx rfl
  · rintro ⟨z, rfl⟩
    change (z.comp (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass
      (zero_add 1)).comp (Ext.mk₀ ((T).map (schemeSectionHom L s))) (add_zero 1) = 0
    rw [Ext.comp_assoc_of_third_deg_zero]
    exact (congrArg (fun q => z.comp q (zero_add 1))
      (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass_comp).trans
        (by simp only [Ext.comp_zero])

/-- Exactness at the actual quotient H⁰ identifies the connecting map's
kernel with the range of the actual restriction map, over the base field. -/
theorem schemeSectionLineδ_ker_eq_range :
    letI := schemeModuleCohomologyModule p O 1
    letI := schemeModuleCohomologyModule p L 0
    letI := schemeModuleCohomologyModule p R 0
    (d).ker = (g).range := by
  let := schemeModuleCohomologyModule p O 1
  let := schemeModuleCohomologyModule p L 0
  let := schemeModuleCohomologyModule p R 0
  ext x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₃ _
      (schemeSectionLineAbelianComplex_shortExact L s U e hU hs) x rfl hx
  · rintro ⟨z, rfl⟩
    change (z.comp (Ext.mk₀ ((T).map (schemeSectionLineRestrictionMap L s U e hU)))
      (add_zero 0)).comp (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass
        (zero_add 1) = 0
    rw [Ext.comp_assoc_of_second_deg_zero]
    exact (congrArg (fun q => z.comp q (zero_add 1))
      (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).comp_extClass).trans
        (by simp only [Ext.comp_zero])

include hs in
/-- Exactness at actual H⁰(L), as an equality of base-field submodules. -/
theorem schemeSectionLineH0_ker_eq_range :
    letI := schemeModuleCohomologyModule p O 0
    letI := schemeModuleCohomologyModule p L 0
    letI := schemeModuleCohomologyModule p R 0
    (g).ker = (schemeModuleCohomologyMap p (schemeSectionHom L s) 0).range := by
  let := schemeModuleCohomologyModule p O 0
  let := schemeModuleCohomologyModule p L 0
  let := schemeModuleCohomologyModule p R 0
  ext x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₂ _
      (schemeSectionLineAbelianComplex_shortExact L s U e hU hs) x hx
  · rintro ⟨z, rfl⟩
    change (z.comp (Ext.mk₀ ((T).map (schemeSectionHom L s))) (add_zero 0)).comp
      (Ext.mk₀ ((T).map (schemeSectionLineRestrictionMap L s U e hU))) (add_zero 0) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    have := schemeModulesToAbelianSheaves_additive X
    have hz := ((schemeSectionLineComplex L s U e hU).map (T)).zero
    exact (congrArg (fun q => z.comp (Ext.mk₀ q) (add_zero 0)) hz).trans (by simp)

/-- The actual H⁰ of the structure sheaf has dimension one, for the scalar
 action of the actual structure morphism. -/
theorem properScheme_structureH0_finrank [IsAlgClosed k] [UniversallyClosed p] :
    letI := schemeModuleCohomologyModule p O 0
    Module.finrank k (H⁰(O)) = 1 := by
  let := schemeModuleCohomologyModule p O 0
  let := schemeGlobalSectionsModuleOfMorphism p O
  let c : k →ₗ[k] Γ(O, ⊤) :=
    { toFun := schemeConstantMap p
      map_add' := (schemeConstantMap p).map_add
      map_smul' := fun a b => (schemeConstantMap p).map_mul a b }
  let ec := LinearEquiv.ofBijective c (schemeConstantMap_bijective p)
  calc
    Module.finrank k (H⁰(O)) = Module.finrank k Γ(O, ⊤) :=
      (schemeModuleCohomologyEquiv₀ p O).finrank_eq
    _ = Module.finrank k k := ec.finrank_eq.symm
    _ = 1 := Module.finrank_self k

section FiniteType

variable [LocallyOfFiniteType p] [QuasiCompact p] (hdim : topologicalKrullDim X ≤ 1)

local notation "D" => schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU
local notation "iD" => schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU

/-- Actual H⁰ of the line-restriction term is linearly equivalent to functions
on the constructed finite zero scheme, with its complete scheme structure. -/
def schemeSectionLineRestrictionH0FunctionsEquiv :
    letI := schemeModuleCohomologyModule p R 0
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    H⁰(R) ≃ₗ[k] Γ(D, ⊤) := by
  letI := schemeModuleCohomologyModule p R 0
  letI := schemeGlobalSectionsModuleOfMorphism p R
  letI := schemeGlobalSectionsModuleOfMorphism p (cokernel (schemeSectionHom L s))
  letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
  exact (schemeModuleCohomologyEquiv₀ p R).trans
    ((schemeGlobalSectionsIso p (schemeSectionLineCokernelIso L s U e hU)).symm.trans
      (schemeSectionLineCokernelFunctionsEquiv L s U e hU hs p hdim))

include hs hdim in
/-- The actual line-restriction term has finite-dimensional H⁰, derived from
its actual finite zero scheme. -/
theorem schemeSectionLineRestrictionH0_finite :
    letI := schemeModuleCohomologyModule p R 0
    Module.Finite k (H⁰(R)) := by
  let := schemeModuleCohomologyModule p R 0
  let := schemeGlobalFunctionsAlgebra (iD ≫ p)
  have := schemeSectionZeroScheme_isFinite_of_ne_zero L s U hU e hs p hdim
  have := finiteScheme_globalFunctions_finite (iD ≫ p)
  exact Module.Finite.equiv
    (schemeSectionLineRestrictionH0FunctionsEquiv p L s U e hU hs hdim).symm

include U e hU hs hdim in
/-- The actual H¹ section map has a finite-dimensional kernel even before
finiteness of either whole H¹ space has been established. -/
theorem schemeSectionLineH1_kernel_finite :
    letI := schemeModuleCohomologyModule p O 1
    letI := schemeModuleCohomologyModule p L 1
    Module.Finite k (f).ker := by
  let := schemeModuleCohomologyModule p O 1
  let := schemeModuleCohomologyModule p L 1
  let := schemeModuleCohomologyModule p R 0
  have := schemeSectionLineRestrictionH0_finite p L s U e hU hs hdim
  change Module.Finite k (f).ker
  rw [schemeSectionLineH1_ker_eq_rangeδ p L s U e hU hs]
  exact Module.Finite.range d

include U e hU hs hdim in
/-- A nonzero line section on a finite-type integral curve preserves
finiteness of H¹ in both directions. This proves a reduction, not either
absolute finiteness assertion. -/
theorem schemeSectionLineH1_finite_iff :
    letI := schemeModuleCohomologyModule p O 1
    letI := schemeModuleCohomologyModule p L 1
    Module.Finite k (H¹(O)) ↔ Module.Finite k (H¹(L)) := by
  let := schemeModuleCohomologyModule p O 1
  let := schemeModuleCohomologyModule p L 1
  have hf : Function.Surjective f := schemeSectionLine_H1_surjective L s U e hU hs p hdim
  constructor
  · intro h
    have := h
    exact Module.Finite.of_surjective f hf
  · intro h
    have := h
    have := schemeSectionLineH1_kernel_finite p L s U e hU hs hdim
    refine ⟨(⊤ : Submodule k (H¹(O))).fg_of_fg_map_of_fg_inf_ker f ?_ ?_⟩
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact (Submodule.fg_top (f).ker).mp Module.Finite.fg_top

end FiniteType

variable [IsAlgClosed k] [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
local notation "D" => schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU
local notation "iD" => schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU

include hs hdim in
/-- The exact finite-term dimension balance attached to a specified nonzero
line section on a proper integral curve. No whole H¹ space is assumed finite. -/
theorem properCurve_sectionH0_add_H1_kernel_finrank :
    letI := schemeModuleCohomologyModule p L 0
    letI := schemeModuleCohomologyModule p O 1
    letI := schemeModuleCohomologyModule p L 1
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    Module.finrank k (H⁰(L)) + Module.finrank k (f).ker =
      1 + Module.finrank k Γ(D, ⊤) := by
  let := schemeModuleCohomologyModule p O 0
  let := schemeModuleCohomologyModule p L 0
  let := schemeModuleCohomologyModule p R 0
  let := schemeModuleCohomologyModule p O 1
  let := schemeModuleCohomologyModule p L 1
  let := schemeGlobalFunctionsAlgebra (iD ≫ p)
  have hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨e i⟩⟩
  have := properCurve_lineH0_finite_of_lineCharts L p hcharts hdim
  have := schemeSectionLineRestrictionH0_finite p L s U e hU hs hdim
  have hg := (g).finrank_range_add_finrank_ker
  have hd := (d).finrank_range_add_finrank_ker
  rw [schemeSectionLineH0_ker_eq_range p L s U e hU hs] at hg
  have hi : Module.finrank k (schemeModuleCohomologyMap p (schemeSectionHom L s) 0).range =
      Module.finrank k (H⁰(O)) := LinearMap.finrank_range_of_inj
        (schemeSectionLine_H0_injective L s U e hU hs)
  rw [hi, properScheme_structureH0_finrank p] at hg
  rw [schemeSectionLineδ_ker_eq_range p L s U e hU hs,
    ← schemeSectionLineH1_ker_eq_rangeδ p L s U e hU hs] at hd
  have hR := (schemeSectionLineRestrictionH0FunctionsEquiv p L s U e hU hs hdim).finrank_eq
  omega

end Normalizer
