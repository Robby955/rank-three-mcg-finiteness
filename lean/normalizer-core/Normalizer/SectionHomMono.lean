import Normalizer.LineGenericInjection

/-! A nonzero section of an actual locally trivial line sheaf on an integral
scheme induces a monomorphism from the structure sheaf. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))

local instance schemeSectionHomMonoSectionModule (V : X.Opensᵒᵖ) :
    Module (X.presheaf.obj V) (L.presheaf.obj V) := (L.val.obj V).isModule

/-- The sheaf map represented by the specified section is actual scalar
multiplication by its restriction on each open. -/
theorem schemeSectionHom_apply (V : X.Opens) (r : Γ(X, V)) :
    (schemeSectionHom L s).val.app (op V) r =
      r • L.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
  rw [← schemeSectionHom_one L s V]
  simpa only [smul_eq_mul, mul_one] using
    ((schemeSectionHom L s).val.app (op V)).hom.map_smul r (1 : Γ(X, V))

/-- In a genuine line chart, the actual section map is multiplication by
the actual local equation of the given section. -/
theorem schemeSectionHom_coordinate {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) (r : Γ(X, V)) :
    e.inv.val.app (op (Over.mk (homOfLE h)))
      ((schemeSectionHom L s).val.app (op V) r) =
        r * sectionLocalEquation L s e V h := by
  rw [schemeSectionHom_apply, map_smul]
  rfl

variable [IsIntegral X]

/-- A nonzero generic germ makes the actual section map injective on
every nonempty genuine line chart. -/
theorem schemeSectionHom_injective_on_chart
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    {U : X.Opens} (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) [Nonempty V] :
    Function.Injective ((schemeSectionHom L s).val.app (op V)) := by
  intro a b hab
  have hc := congrArg (e.inv.val.app (op (Over.mk (homOfLE h)))) hab
  rw [schemeSectionHom_coordinate, schemeSectionHom_coordinate] at hc
  change (a : Γ(X, V)) = (b : Γ(X, V))
  exact mul_right_cancel₀ (M₀ := Γ(X, V))
    (sectionLocalEquation_ne_zero L s e hs V h) hc

/-- Genuine pointwise line charts make the section map injective on all
opens, including the empty open, by the actual sheaf separation property. -/
theorem schemeSectionHom_injective
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U))
    (V : X.Opens) : Function.Injective ((schemeSectionHom L s).val.app (op V)) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := hcharts x
  let W := V ⊓ U
  have hxW : x ∈ W := ⟨hx, hxU⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hr : X.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op a =
      X.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op b := by
    apply schemeSectionHom_injective_on_chart L s hs e W inf_le_right
    have he := congrArg (L.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op) hab
    exact (PresheafOfModules.naturality_apply (schemeSectionHom L s).val
      (homOfLE (inf_le_left : W ≤ V)).op a).trans
      (he.trans (PresheafOfModules.naturality_apply (schemeSectionHom L s).val
        (homOfLE (inf_le_left : W ≤ V)).op b).symm)
  have hg := congrArg (X.presheaf.germ W x hxW) hr
  exact (X.presheaf.germ_res_apply
    (homOfLE (inf_le_left : W ≤ V)) x hxW a).symm.trans
    (hg.trans (X.presheaf.germ_res_apply
      (homOfLE (inf_le_left : W ≤ V)) x hxW b))

/-- A generically nonzero actual line section induces a monomorphism of
actual module sheaves. -/
theorem schemeSectionHom_mono_of_generic_ne_zero
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    Mono (schemeSectionHom L s) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective
    (fun {V} ↦ schemeSectionHom_injective L s hs hcharts V.unop)

/-- A nonzero global section of a genuinely locally trivial line sheaf
on an integral scheme induces the actual monomorphism `O_X → L`. -/
theorem schemeSectionHom_mono (hs : s ≠ 0)
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    Mono (schemeSectionHom L s) :=
  schemeSectionHom_mono_of_generic_ne_zero L s
    ((lineSheaf_genericGerm_ne_zero_iff L hcharts s).mpr hs) hcharts

end Normalizer
