import Normalizer.KernelSaturation
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Module.Torsion.Free

/-! Torsion-free stalks of actual sheaves on integral schemes give torsion-free
section modules. Empty opens are handled by sheaf separatedness, without a
nontriviality or domain assumption on their rings of sections. -/

noncomputable section

namespace Normalizer

open CategoryTheory Opposite AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The existing module structure on the actual stalk of a scheme module,
exposed across the `Scheme.Modules.presheaf` wrapper. -/
@[instance_reducible]
def schemeModuleStalkModule (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  exact inferInstanceAs (Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x))

attribute [instance] schemeModuleStalkModule

/-- Compatibility of actual scheme-module germs with scalar multiplication. -/
theorem schemeModule_germ_smul (F : X.Modules) (x : X) (V : X.Opens)
    (hx : x ∈ V) (r : Γ(X, V)) (s : Γ(F, V)) :
    F.presheaf.germ V x hx (r • s) =
      X.presheaf.germ V x hx r • F.presheaf.germ V x hx s := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  exact PresheafOfModules.germ_smul M x V hx r s

variable [IsIntegral X]

/-- Stalkwise torsion-freeness implies torsion-freeness of sections on every
open of an integral scheme, including the empty open. -/
theorem integralSheaf_sections_isTorsionFree (F : X.Modules)
    (hF : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x))
    (V : X.Opens) : Module.IsTorsionFree Γ(X, V) Γ(F, V) := by
  constructor
  intro r hr s t h
  apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ V s t
  intro x hx
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := hF x
  have hrg : X.presheaf.germ V x hx r ≠ 0 := by
    intro he
    exact hr.ne_zero ((germ_injective_of_isIntegral X x hx) (by simpa using he))
  apply (smul_right_injective (M := F.presheaf.stalk x) hrg)
  have hg := congrArg (F.presheaf.germ V x hx) h
  simpa only [schemeModule_germ_smul] using hg

/-- Torsion-freeness on all opens implies torsion-freeness of every actual
stalk. The proof represents a scalar and section on one neighbourhood and
shrinks an equality of germs to an equality of sections. -/
theorem integralSheaf_stalk_isTorsionFree (F : X.Modules)
    (hF : ∀ V : X.Opens, Module.IsTorsionFree Γ(X, V) Γ(F, V))
    (x : X) : Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r s hrs
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨U, hxU, a, ha⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, hb⟩ := F.presheaf.exists_le_germ_eq s hxU
  let j : V ⟶ U := homOfLE hVU
  let aV : Γ(X, V) := X.presheaf.map j.op a
  have haV : X.presheaf.germ V x hxV aV = r := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha
  have hz : F.presheaf.germ V x hxV (aV • b) = F.presheaf.germ V x hxV 0 := by
    rw [schemeModule_germ_smul, haV, hb]
    simpa using hrs
  obtain ⟨W, hxW, i, i', he⟩ := F.presheaf.germ_eq x hxV hxV (aV • b) 0 hz
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  let := hF W
  have he' : X.presheaf.map i.op aV • F.presheaf.map i.op b = 0 := by
    simpa only [Scheme.Modules.map_smul, map_zero] using he
  have har : X.presheaf.map i.op aV ≠ 0 := by
    intro har
    apply hr
    have harg := congrArg (X.presheaf.germ W x hxW) har
    simpa only [TopCat.Presheaf.germ_res_apply, haV, map_zero] using harg
  have hb0 : F.presheaf.map i.op b = 0 := (smul_eq_zero.mp he').resolve_left har
  have hbg := congrArg (F.presheaf.germ W x hxW) hb0
  simpa only [TopCat.Presheaf.germ_res_apply, hb, map_zero] using hbg

/-- On an actual integral scheme, torsion-freeness of all stalks is equivalent
to torsion-freeness of all section modules. -/
theorem integralSheaf_torsionFree_iff (F : X.Modules) :
    (∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x)) ↔
      ∀ V : X.Opens, Module.IsTorsionFree Γ(X, V) Γ(F, V) :=
  ⟨fun h V => integralSheaf_sections_isTorsionFree F h V,
    fun h x => integralSheaf_stalk_isTorsionFree F h x⟩

/-- On an actual integral scheme, the quotient by a sheaf kernel has
torsion-free stalks whenever the target has torsion-free stalks. The quotient
is the actual sheaf cokernel; no surjectivity on sections is asserted. -/
theorem integralSheaf_kernelCokernel_stalk_isTorsionFree
    {E H : X.Modules} (f : E ⟶ H)
    (hH : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (H.presheaf.stalk x))
    (x : X) : Module.IsTorsionFree (X.presheaf.stalk x)
      ((Limits.cokernel (Limits.kernel.ι f)).presheaf.stalk x) := by
  apply integralSheaf_stalk_isTorsionFree
  intro V
  let : Module.IsTorsionFree (X.ringCatSheaf.obj.obj (op V)) (H.val.obj (op V)) :=
    integralSheaf_sections_isTorsionFree H hH V
  exact kernelCokernel_sections_isTorsionFree
    (show (E : SheafOfModules X.ringCatSheaf) ⟶ H from f) (op V)

end Normalizer
