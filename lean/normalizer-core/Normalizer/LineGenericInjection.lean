import Normalizer.SectionLocalEquation
import Normalizer.StalkBracket

/-! A genuine locally trivial line sheaf on an integral scheme has an
injective global-section map to its actual generic stalk. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
  (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U))

include hlocal in
/-- Vanishing of the generic germ forces the actual global section of a
genuinely locally trivial line sheaf to vanish. -/
theorem lineSheaf_eq_zero_of_genericGerm_eq_zero (s : Γ(L, ⊤))
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s = 0) : s = 0 := by
  apply TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ ⊤ s 0
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := hlocal x
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have hsU : L.presheaf.germ U (genericPoint X) hgU
      (L.presheaf.map (homOfLE le_top).op s) = 0 := by
    rwa [TopCat.Presheaf.germ_res_apply]
  have hc := congrArg (fun z ↦ schemeUnitStalkEquiv (X := X) (genericPoint X)
    (schemeLocalStalkMap e.inv (genericPoint X) hgU z)) hsU
  rw [schemeLocalStalkMap_germ e.inv (genericPoint X) hgU U le_rfl hgU,
    map_zero, map_zero, schemeUnitStalkEquiv_germ] at hc
  have hz : sectionLocalEquation L s e U le_rfl = 0 :=
    (germ_injective_of_isIntegral X (genericPoint X) hgU) (by
      change X.presheaf.germ U (genericPoint X) hgU
        (sectionLocalEquation L s e U le_rfl) = 0 at hc
      simpa only [map_zero] using hc)
  have he := sectionLocalEquation_chart L s e U le_rfl
  rw [hz, map_zero] at he
  have hg := congrArg (L.presheaf.germ U x hxU) he
  simpa only [map_zero, TopCat.Presheaf.germ_res_apply] using hg.symm

include hlocal in
/-- The actual global-section generic-germ map is injective, derived from
line charts rather than an assumed torsion condition. -/
theorem lineSheaf_genericGerm_injective :
    Function.Injective (L.presheaf.germ ⊤ (genericPoint X) (by trivial)) := by
  intro s t h
  apply sub_eq_zero.mp
  apply lineSheaf_eq_zero_of_genericGerm_eq_zero L hlocal
  rw [map_sub, h, sub_self]

include hlocal in
/-- For an actual locally trivial line sheaf, nonzero global section and
nonzero generic germ are equivalent. -/
theorem lineSheaf_genericGerm_ne_zero_iff (s : Γ(L, ⊤)) :
    L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0 ↔ s ≠ 0 := by
  have h := lineSheaf_genericGerm_injective L hlocal
  exact not_congr (h.eq_iff' (map_zero _))

end Normalizer
