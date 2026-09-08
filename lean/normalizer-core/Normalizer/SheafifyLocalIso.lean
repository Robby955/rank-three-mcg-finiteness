import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! A map from a module presheaf to an actual sheaf becomes an isomorphism
after sheafification if its section maps are bijective on a covering family
of opens and every smaller open. No sectionwise surjectivity of a
sheafification map is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {P : PresheafOfModules.{u} R.obj} {G : SheafOfModules.{u} R}
  (f : P ⟶ G.val) {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)

include hcover in
/-- Injectivity on all smaller opens of a genuine cover gives local
injectivity, even when the source presheaf is not separated. -/
theorem modulePresheaf_locallyInjective_of_cover
    (hinj : ∀ i (V : Opens X), V ≤ U i → Function.Injective (f.app (op V))) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f where
  equalizerSieve_mem {V} s t h := by
    intro x hx
    have hxcover : x ∈ iSup U := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
    refine ⟨V.unop ⊓ U i, homOfLE inf_le_left, ?_, ⟨hx, hi⟩⟩
    change P.map (homOfLE inf_le_left).op s = P.map (homOfLE inf_le_left).op t
    apply hinj i _ inf_le_right
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg (G.val.map (homOfLE inf_le_left).op) h

include hcover in
/-- Surjectivity on the same cover gives local surjectivity. -/
theorem modulePresheaf_locallySurjective_of_cover
    (hsurj : ∀ i (V : Opens X), V ≤ U i → Function.Surjective (f.app (op V))) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f where
  imageSieve_mem {V} s := by
    intro x hx
    have hxcover : x ∈ iSup U := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
    refine ⟨V ⊓ U i, homOfLE inf_le_left, ?_, ⟨hx, hi⟩⟩
    exact hsurj i _ inf_le_right (G.val.map (homOfLE inf_le_left).op s)

/-- The actual sheafification lift of a locally bijective map to a sheaf
is an isomorphism. -/
theorem sheafificationLift_isIso_of_locallyBijective
    [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f) := by
  let g := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f
  let J := Opens.grothendieckTopology X
  let q := (SheafOfModules.toSheaf R).map g
  have fac : CategoryTheory.toSheafify J P.presheaf ≫ q.hom =
      (PresheafOfModules.toPresheaf R.obj).map f := by
    change (PresheafOfModules.toPresheaf R.obj).map
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) g) = _
    simp [g]
  have : Presheaf.IsLocallyInjective J q.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J _ fac
  have : Presheaf.IsLocallySurjective J q.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J fac
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso g (SheafOfModules.toSheaf R)

include hcover in
/-- Bijectivity on genuine trivializing opens proves the sheafification
lift is invertible globally. -/
theorem sheafificationLift_isIso_of_cover
    (hbij : ∀ i (V : Opens X), V ≤ U i → Function.Bijective (f.app (op V))) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f) := by
  have := modulePresheaf_locallyInjective_of_cover f U hcover
    (fun i V h => (hbij i V h).injective)
  have := modulePresheaf_locallySurjective_of_cover f U hcover
    (fun i V h => (hbij i V h).surjective)
  exact sheafificationLift_isIso_of_locallyBijective f

end Normalizer
