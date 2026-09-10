import Normalizer.FiniteBundlePresentation
import Normalizer.SheafQuotientBracket
import Mathlib.AlgebraicGeometry.Properties

/-! Actual stalk exactness and scalar-saturated bundle quotients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u
variable {X : Scheme.{u}} {M E : X.Modules} (f : M ⟶ E)

/-- The actual sheaf-cokernel projection is surjective on every actual
stalk. Its sections on a fixed open need not be surjective. -/
theorem sheaf_cokernel_stalk_surjective (x : X) :
    Function.Surjective (schemeModuleStalkMap (cokernel.π f) x) := by
  intro s
  obtain ⟨U, hxU, a, rfl⟩ := (cokernel f).presheaf.exists_germ_eq s
  have hq := sheaf_cokernel_locallySurjective (R := X.ringCatSheaf) f
  obtain ⟨V, i, ⟨b, hb⟩, hxV⟩ := hq.imageSieve_mem a x hxU
  change (cokernel.π f).app V b = (cokernel f).presheaf.map i.op a at hb
  refine ⟨E.presheaf.germ V x hxV b, ?_⟩
  rw [schemeModuleStalkMap_germ]
  rw [hb]
  exact (cokernel f).presheaf.germ_res_apply i x hxV a

/-- The composition of an inclusion and its actual quotient projection
vanishes on stalks. -/
theorem sheaf_cokernel_stalk_comp (x : X) (m : M.presheaf.stalk x) :
    schemeModuleStalkMap (cokernel.π f) x (schemeModuleStalkMap f x m) = 0 := by
  obtain ⟨U, hxU, a, rfl⟩ := M.presheaf.exists_germ_eq m
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
  have h := congrArg (fun g : M ⟶ cokernel f ↦ g.app U a) (cokernel.condition f)
  have hz : (cokernel.π f).app U (f.app U a) = 0 := by
    change (cokernel.π f).app U (f.app U a) = 0 at h
    exact h
  rw [hz, map_zero]

/-- The stalk kernel of the quotient projection is the range of the
actual stalk inclusion. The proof shrinks an equality of germs before
using exactness on sections of the smaller open. -/
theorem sheaf_cokernel_stalk_exact [Mono f] (x : X) (v : E.presheaf.stalk x)
    (hv : schemeModuleStalkMap (cokernel.π f) x v = 0) :
    ∃ m : M.presheaf.stalk x, schemeModuleStalkMap f x m = v := by
  obtain ⟨U, hxU, b, rfl⟩ := E.presheaf.exists_germ_eq v
  have he : (cokernel f).presheaf.germ U x hxU ((cokernel.π f).app U b) =
      (cokernel f).presheaf.germ U x hxU 0 := by
    rw [← schemeModuleStalkMap_germ]
    simpa using hv
  obtain ⟨V, hxV, i, j, he⟩ := (cokernel f).presheaf.germ_eq x hxU hxU _ _ he
  have hb : (cokernel.π f).app V (E.presheaf.map i.op b) = 0 := by
    have hn := congrArg (fun g ↦ g b) ((cokernel.π f).mapPresheaf.naturality i.op)
    simpa only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app,
      map_zero] using hn.trans he
  have hb' : (cokernel.π f).val.app (op V) (E.presheaf.map i.op b) = 0 := by
    exact hb
  obtain ⟨a, ha⟩ := sheaf_cokernel_section_exact (R := X.ringCatSheaf) f (op V)
    (E.presheaf.map i.op b) hb'
  refine ⟨M.presheaf.germ V x hxV a, ?_⟩
  rw [schemeModuleStalkMap_germ]
  change E.presheaf.germ V x hxV (f.val.app (op V) a) = _
  rw [ha]
  exact E.presheaf.germ_res_apply i x hxV b

/-- Actual stalk exactness, expressed as equality of local-ring submodules. -/
theorem sheaf_cokernel_stalk_ker_eq_range [Mono f] (x : X) :
    LinearMap.ker (schemeModuleStalkMap (cokernel.π f) x) =
      LinearMap.range (schemeModuleStalkMap f x) := by
  ext v
  constructor
  · exact sheaf_cokernel_stalk_exact f x v
  · rintro ⟨m, rfl⟩
    exact sheaf_cokernel_stalk_comp f x m

/-- The quotient of actual stalk modules is linearly isomorphic over the
actual local ring to the stalk of the actual sheaf cokernel. -/
def sheafCokernelStalkEquiv [Mono f] (x : X) :
    (E.presheaf.stalk x ⧸ LinearMap.range (schemeModuleStalkMap f x)) ≃ₗ[X.presheaf.stalk x]
      (cokernel f).presheaf.stalk x :=
  (Submodule.quotEquivOfEq _ _ (sheaf_cokernel_stalk_ker_eq_range f x).symm).trans
    (LinearMap.quotKerEquivOfSurjective (schemeModuleStalkMap (cokernel.π f) x)
      (sheaf_cokernel_stalk_surjective f x))

/-- The comparison sends the class of a stalk element to its actual image
under the sheaf quotient projection. -/
theorem sheafCokernelStalkEquiv_mk [Mono f] (x : X) (v : E.presheaf.stalk x) :
    sheafCokernelStalkEquiv f x (Submodule.Quotient.mk v) =
      schemeModuleStalkMap (cokernel.π f) x v := by
  simp [sheafCokernelStalkEquiv]

/-- Scalar saturation of the actual stalk inclusion implies torsion-free
actual quotient stalks. The local ring is the scheme's actual local ring. -/
theorem sheaf_cokernel_stalk_isTorsionFree_of_saturated [IsIntegral X] [Mono f]
    (x : X)
    (hsat : ∀ (r : X.presheaf.stalk x), r ≠ 0 → ∀ v : E.presheaf.stalk x,
      r • v ∈ LinearMap.range (schemeModuleStalkMap f x) →
      v ∈ LinearMap.range (schemeModuleStalkMap f x)) :
    Module.IsTorsionFree (X.presheaf.stalk x) ((cokernel f).presheaf.stalk x) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r q hrq
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨v, rfl⟩ := sheaf_cokernel_stalk_surjective f x q
  have hz : schemeModuleStalkMap (cokernel.π f) x (r • v) = 0 := by
    simpa only [map_smul] using hrq
  obtain ⟨m, hm⟩ := sheaf_cokernel_stalk_exact f x (r • v) hz
  obtain ⟨a, ha⟩ := hsat r hr v ⟨m, hm⟩
  rw [← ha]
  exact sheaf_cokernel_stalk_comp f x a

/-- Scalar saturation of the actual inclusion on stalks is equivalent
to torsion-freeness of the actual quotient stalk. -/
theorem sheaf_cokernel_stalk_torsionFree_iff_saturated [IsIntegral X] [Mono f]
    (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) ((cokernel f).presheaf.stalk x) ↔
      ∀ (r : X.presheaf.stalk x), r ≠ 0 → ∀ v : E.presheaf.stalk x,
        r • v ∈ LinearMap.range (schemeModuleStalkMap f x) →
        v ∈ LinearMap.range (schemeModuleStalkMap f x) := by
  refine ⟨?_, sheaf_cokernel_stalk_isTorsionFree_of_saturated f x⟩
  intro htf r hr v hv
  let := htf
  have hz : schemeModuleStalkMap (cokernel.π f) x (r • v) = 0 := by
    obtain ⟨m, hm⟩ := hv
    rw [← hm]
    exact sheaf_cokernel_stalk_comp f x m
  have hv0 : schemeModuleStalkMap (cokernel.π f) x v = 0 :=
    (smul_eq_zero.mp (by simpa only [map_smul] using hz)).resolve_left hr
  exact sheaf_cokernel_stalk_exact f x v hv0

/-- The dimension of an actual scheme local ring is bounded by the
dimension of the scheme, via its point's coheight. -/
theorem scheme_stalk_ringKrullDim_le (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ Order.krullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact Order.coheight_le_krullDim x

/-- A scalar-saturated inclusion of finite-rank bundles has locally free
actual cokernel on an integral scheme of dimension at most one with
regular local rings. Finite presentation, free quotient stalks and the
local dimension bounds are all derived. -/
theorem saturatedFiniteBundle_cokernel_isLocallyFree [IsIntegral X] [Mono f]
    {A B : Type u} (U : A → X.Opens) (hU : IsOpenCover U)
    (V : B → X.Opens) (hV : IsOpenCover V)
    (I : A → Type u) (J : B → Type u) [∀ a, Finite (I a)] [∀ b, Finite (J b)]
    (eM : ∀ a, M.over (U a) ≅ SheafOfModules.free (I a))
    (eE : ∀ b, E.over (V b) ≅ SheafOfModules.free (J b))
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : Order.krullDim X ≤ 1)
    (hsat : ∀ (x : X) (r : X.presheaf.stalk x), r ≠ 0 → ∀ v : E.presheaf.stalk x,
      r • v ∈ LinearMap.range (schemeModuleStalkMap f x) →
      v ∈ LinearMap.range (schemeModuleStalkMap f x)) :
    (cokernel f).IsLocallyFree := by
  let := finiteBundle_cokernel_isFinitePresentation E f U hU V hV I J eM eE
  exact sheaf_isLocallyFree_of_regular_stalks (cokernel f) hreg
    (fun x ↦ (scheme_stalk_ringKrullDim_le x).trans hdim)
    (fun x ↦ sheaf_cokernel_stalk_isTorsionFree_of_saturated f x (hsat x))

end Normalizer
