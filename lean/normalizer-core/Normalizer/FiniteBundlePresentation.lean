import Normalizer.SheafCokernelFinitePresentation

/-! Finite presentation from genuine finite free trivializations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u
variable {X : Scheme.{u}} (E : X.Modules)

/-- A sheaf with actual finite free trivializations on an open cover is
finitely presented. The rank can vary between members of the cover. -/
theorem sheaf_isFinitePresentation_of_finiteFree_cover {A : Type u}
    (U : A → X.Opens) (hU : IsOpenCover U) (I : A → Type u)
    [∀ a, Finite (I a)]
    (e : ∀ a, E.over (U a) ≅ SheafOfModules.free (I a)) :
    E.IsFinitePresentation := by
  let q := freeCoverLocalGeneratorsData E U hU I e
  let : q.IsLocallyFreeData := freeCoverLocalGeneratorsData_isLocallyFree E U hU I e
  have hq : q.quasiCoherentData.IsFinitePresentation := by
    constructor
    intro a
    constructor
    · constructor
      change Finite (I a)
      infer_instance
    · constructor
      change Finite (ULift Empty)
      infer_instance
  exact SheafOfModules.IsFinitePresentation.mk (M := E) ⟨q.quasiCoherentData, hq⟩

/-- Pointwise finite free neighborhoods give finite presentation on the
actual scheme. The neighborhood maps are genuine open immersions. -/
theorem sheaf_isFinitePresentation_of_finiteFree_neighborhoods
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f),
      x ∈ f.opensRange ∧ ∃ (I : Type u) (_ : Finite I),
        Nonempty (E.restrict f ≅ SheafOfModules.free I)) :
    E.IsFinitePresentation := by
  have h' (x : X) : ∃ U : X.Opens, x ∈ U ∧ ∃ (I : Type u) (_ : Finite I),
      Nonempty (E.over U ≅ SheafOfModules.free I) := by
    obtain ⟨Y, f, hf, hx, I, hI, ⟨e⟩⟩ := h x
    let := hf
    exact ⟨f.opensRange, hx, I, hI, ⟨openImmersionOverFreeIso E f I e⟩⟩
  choose U hx I hI e using h'
  have hU : IsOpenCover U := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let := hI
  exact sheaf_isFinitePresentation_of_finiteFree_cover E U hU I (fun x ↦ (e x).some)

/-- A quotient of two sheaves supplied by finite free covers is finitely
presented. The covers and the finite ranks need not agree. -/
theorem finiteBundle_cokernel_isFinitePresentation
    {M : X.Modules} (f : M ⟶ E)
    {A B : Type u} (U : A → X.Opens) (hU : IsOpenCover U)
    (V : B → X.Opens) (hV : IsOpenCover V)
    (I : A → Type u) (J : B → Type u) [∀ a, Finite (I a)] [∀ b, Finite (J b)]
    (eM : ∀ a, M.over (U a) ≅ SheafOfModules.free (I a))
    (eE : ∀ b, E.over (V b) ≅ SheafOfModules.free (J b)) :
    (cokernel f).IsFinitePresentation := by
  let := sheaf_isFinitePresentation_of_finiteFree_cover M U hU I eM
  let := sheaf_isFinitePresentation_of_finiteFree_cover E V hV J eE
  exact sheaf_cokernel_isFinitePresentation f

end Normalizer
