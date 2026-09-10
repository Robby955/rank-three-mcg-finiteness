import Normalizer.LocalFrameStalk
import Normalizer.GlobalSectionFrame
import Normalizer.ModuleHomLine

/-! Local equations of a specified section in genuine line-bundle charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

variable {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))
  {U : X.Opens} (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)

/-- The actual local equation of the specified global section in a genuine
line-bundle chart, evaluated on any smaller open. -/
def sectionLocalEquation (V : X.Opens) (h : V ≤ U) : Γ(X, V) :=
  e.inv.val.app (op (Over.mk (homOfLE h)))
    (L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)

/-- The local equations are compatible with the actual restriction maps. -/
theorem sectionLocalEquation_restrict {V W : X.Opens} (h : W ≤ V) (k : V ≤ U) :
    X.presheaf.map (homOfLE h).op (sectionLocalEquation L s e V k) =
      sectionLocalEquation L s e W (h.trans k) := by
  let i : Over.mk (homOfLE (h.trans k)) ⟶ Over.mk (homOfLE k) :=
    Over.homMk (homOfLE h)
  have hn := PresheafOfModules.naturality_apply e.inv.val i.op
    (L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)
  change e.inv.val.app (op (Over.mk (homOfLE (h.trans k))))
      (L.presheaf.map (homOfLE h).op
        (L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)) = _ at hn
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hn
  exact hn.symm

/-- The chart carries its actual scalar equation back to the specified section. -/
theorem sectionLocalEquation_chart (V : X.Opens) (h : V ≤ U) :
    e.hom.val.app (op (Over.mk (homOfLE h))) (sectionLocalEquation L s e V h) =
      L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
  exact ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE h)))).mapIso e).toLinearEquiv.apply_symm_apply _

/-- The actual section is its local equation times the actual chart frame. -/
theorem sectionLocalEquation_smul_frame (V : X.Opens) (h : V ≤ U) :
    sectionLocalEquation L s e V h •
      e.hom.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X, V)) =
      L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
  rw [← map_smul]
  simpa only [smul_eq_mul, mul_one] using sectionLocalEquation_chart L s e V h

/-- The actual scalar transition from a second line chart to the first. -/
def sectionFrameTransition
    (e' : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) : Γ(X, V) :=
  e.inv.val.app (op (Over.mk (homOfLE h)))
    (e'.hom.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X, V)))

/-- Transition coefficients of genuine line charts are units, including
on empty opens. Their inverses are derived from the inverse sheaf maps. -/
theorem sectionFrameTransition_isUnit
    (e' : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) : IsUnit (sectionFrameTransition L e e' V h) := by
  let t := (moduleLineFrameAt L e' V h).trans (moduleLineFrameAt L e V h).symm
  change IsUnit (t 1)
  have hi : t.symm 1 * t 1 = 1 := by
    simpa only [smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
      using (t.map_smul (t.symm 1) (1 : Γ(X, V))).symm
  have hj : t 1 * t.symm 1 = 1 := by
    simpa only [smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
      using (t.symm.map_smul (t 1) (1 : Γ(X, V))).symm
  exact ⟨⟨t 1, t.symm 1, hj, hi⟩, rfl⟩

/-- The two local equations of the same specified section differ by the
actual invertible transition coefficient. -/
theorem sectionLocalEquation_change_chart
    (e' : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) :
    sectionLocalEquation L s e V h =
      sectionFrameTransition L e e' V h * sectionLocalEquation L s e' V h := by
  have he := congrArg (e.inv.val.app (op (Over.mk (homOfLE h))))
    (sectionLocalEquation_smul_frame L s e' V h)
  rw [map_smul] at he
  change sectionLocalEquation L s e' V h * sectionFrameTransition L e e' V h =
    sectionLocalEquation L s e V h at he
  exact he.symm.trans (mul_comm _ _)

variable [IsIntegral X]

/-- A nonzero generic germ makes the equation in every nonempty line chart
nonzero. Generic independence or global triviality is not inferred. -/
theorem sectionLocalEquation_ne_zero
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (V : X.Opens) (h : V ≤ U) [Nonempty V] :
    sectionLocalEquation L s e V h ≠ 0 := by
  intro hz
  have he := sectionLocalEquation_chart L s e V h
  rw [hz, map_zero] at he
  have hx : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hg := congrArg (L.presheaf.germ V (genericPoint X) hx) he
  apply hs
  simpa only [map_zero, TopCat.Presheaf.germ_res_apply] using hg.symm

/-- The local equation has nonzero germ at every point of its chart.
This is nonzeroness in the local ring, not in its residue field. -/
theorem sectionLocalEquation_germ_ne_zero
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (V : X.Opens) (h : V ≤ U) (x : X) (hx : x ∈ V) :
    X.presheaf.germ V x hx (sectionLocalEquation L s e V h) ≠ 0 := by
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  intro hz
  apply sectionLocalEquation_ne_zero L s e hs V h
  exact (germ_injective_of_isIntegral X x hx) (by simpa using hz)

/-- The actual local equation is a non-zero-divisor on every nonempty
chart, as required for its effective Cartier zero divisor. -/
theorem sectionLocalEquation_isRegular
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (V : X.Opens) (h : V ≤ U) [Nonempty V] :
    IsRegular (sectionLocalEquation L s e V h) :=
  IsRegular.of_ne_zero (sectionLocalEquation_ne_zero L s e hs V h)

/-- The same equation is a non-zero-divisor in each actual local ring. -/
theorem sectionLocalEquation_germ_isRegular
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (V : X.Opens) (h : V ≤ U) (x : X) (hx : x ∈ V) :
    IsRegular (X.presheaf.germ V x hx (sectionLocalEquation L s e V h)) :=
  IsRegular.of_ne_zero (sectionLocalEquation_germ_ne_zero L s e hs V h x hx)

end Normalizer
