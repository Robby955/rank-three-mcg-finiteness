import Normalizer.AffineCechOne
import Normalizer.DiscreteSheafCohomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! Local-to-global lifting in arbitrary abelian-sheaf extensions with a
localizing module sheaf as kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}}

/-- Forget the scalar action of an actual R-module sheaf on Spec R. -/
def affineModuleAbelianSheaf
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R)) :
    TopCat.Sheaf AddCommGrpCat.{u} (PrimeSpectrum.Top R) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F

/-- An epimorphism of abelian sheaves on Spec R admits lifts of each global
section on a finite principal-open cover. -/
theorem affineSheaf_epi_finitePrincipal_lifts
    {G H : TopCat.Sheaf AddCommGrpCat.{u} (PrimeSpectrum.Top R)}
    (p : G ⟶ H) [Epi p] (s : H.obj.obj (op ⊤)) :
    ∃ (t : Finset (PrimeSpectrum R)) (f : t → R),
      Ideal.span (Set.range f) = ⊤ ∧
      ∃ a : ∀ i, G.obj.obj (op (PrimeSpectrum.basicOpen (f i))),
        ∀ i, p.hom.app _ (a i) = H.obj.map (homOfLE le_top).op s := by
  classical
  have hp : CategoryTheory.Sheaf.IsLocallySurjective p :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} p).mpr inferInstance
  have hlift (x : PrimeSpectrum R) : ∃ (r : R),
      x ∈ PrimeSpectrum.basicOpen r ∧
      ∃ a : G.obj.obj (op (PrimeSpectrum.basicOpen r)),
        p.hom.app _ a = H.obj.map (homOfLE le_top).op s := by
    obtain ⟨V, i, ⟨a, ha⟩, hx⟩ := hp.imageSieve_mem s x (by trivial)
    obtain ⟨_, ⟨r, rfl⟩, hrx, hrV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen x hx
    let j : PrimeSpectrum.basicOpen r ⟶ V := homOfLE hrV
    refine ⟨r, hrx, G.obj.map j.op a, ?_⟩
    calc
      _ = H.obj.map j.op (p.hom.app (op V) a) := NatTrans.naturality_apply p.hom j.op a
      _ = H.obj.map j.op (H.obj.map i.op s) := congrArg (H.obj.map j.op) ha
      _ = _ := by rw [← ConcreteCategory.comp_apply, ← H.obj.map_comp]; rfl
  choose f hfx a ha using hlift
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum R => (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (f x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hfx x⟩)
  refine ⟨t, fun i => f i, ?_, fun i => a i, fun i => ha i⟩
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  apply top_unique
  intro x _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩

/-- A short exact sequence of abelian sheaves is exact on sections at its
middle term, on every open. This uses preservation of kernels by evaluation. -/
theorem abelianSheaf_shortExact_sections_exact {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (U : Opens X) (s : S.X₂.obj.obj (op U))
    (hs : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  have : E.Additive := by dsimp only [E]; infer_instance
  have : E.PreservesZeroMorphisms := inferInstance
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
    inferInstance S hS
  exact (ShortComplex.ab_exact_iff (S.map E)).mp h.1 s hs

private abbrev abRestrict {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U V : Opens X} (h : V ≤ U) :=
  (F.obj.map (homOfLE h).op).hom

private theorem abRestrict_comp {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U V W : Opens X}
    (h : W ≤ V) (k : V ≤ U) (x : F.obj.obj (op U)) :
    abRestrict F h (abRestrict F k x) = abRestrict F (h.trans k) x := by
  change (F.obj.map (homOfLE k).op ≫ F.obj.map (homOfLE h).op) x = _
  rw [← F.obj.map_comp, ← op_comp]
  rfl

private theorem abRestrict_naturality {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (p : F ⟶ G)
    {U V : Opens X} (h : V ≤ U) (x : F.obj.obj (op U)) :
    p.hom.app (op V) (abRestrict F h x) =
      abRestrict G h (p.hom.app (op U) x) :=
  NatTrans.naturality_apply p.hom (homOfLE h).op x

private theorem affineModuleAbelian_naturality
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R))
    {G : TopCat.Sheaf AddCommGrpCat.{u} (PrimeSpectrum.Top R)}
    (i : affineModuleAbelianSheaf F ⟶ G)
    {U V : Opens (PrimeSpectrum.Top R)} (h : V ≤ U) (x : F.obj.obj (op U)) :
    i.hom.app (op V) (affineModuleRestrict F h x) =
      abRestrict G h (i.hom.app (op U) x) :=
  NatTrans.naturality_apply i.hom (homOfLE h).op x

/-- In an arbitrary abelian-sheaf extension whose kernel is a localizing
module sheaf on Spec R, every global section of the quotient lifts globally.
The proof constructs and solves the difference cocycle of finite local lifts. -/
theorem localizingSheaf_extension_globalSections_surjective
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R)) (hF : IsLocalizing F)
    {G H : TopCat.Sheaf AddCommGrpCat.{u} (PrimeSpectrum.Top R)}
    (i : affineModuleAbelianSheaf F ⟶ G) (p : G ⟶ H) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) :
    Function.Surjective (p.hom.app (op ⊤)) := by
  classical
  have : Epi p := hS.epi_g
  have : Mono i := hS.mono_f
  have hi (U : Opens (PrimeSpectrum.Top R)) : Function.Injective (i.hom.app (op U)) := by
    have : Mono i.hom := Functor.map_mono (sheafToPresheaf _ _) i
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  intro s
  obtain ⟨t, f, hf, a, ha⟩ := affineSheaf_epi_finitePrincipal_lifts p s
  let U := fun j : t => PrimeSpectrum.basicOpen (f j)
  have hcover : (⊤ : Opens (PrimeSpectrum.Top R)) ≤ iSup U := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf]
  have hlift (j k : t) : ∃ c : F.obj.obj (op (U j ⊓ U k)),
      i.hom.app _ c = abRestrict G inf_le_left (a j) -
        abRestrict G inf_le_right (a k) := by
    apply abelianSheaf_shortExact_sections_exact (ShortComplex.mk i p w) hS
    change p.hom.app _ (_ - _) = 0
    rw [map_sub, abRestrict_naturality p, abRestrict_naturality p, ha, ha]
    change abRestrict H inf_le_left (abRestrict H le_top s) -
      abRestrict H inf_le_right (abRestrict H le_top s) = 0
    rw [abRestrict_comp H, abRestrict_comp H, sub_self]
  choose c hc using hlift
  have hcocycle (j k l : t) :
      affineModuleRestrict F (inf_le_inf_right _ inf_le_left) (c j l) -
        affineModuleRestrict F (inf_le_inf_right _ inf_le_right) (c k l) =
      affineModuleRestrict F (inf_le_left : (U j ⊓ U k) ⊓ U l ≤ _) (c j k) := by
    apply hi ((U j ⊓ U k) ⊓ U l)
    rw [map_sub, affineModuleAbelian_naturality F i,
      affineModuleAbelian_naturality F i, affineModuleAbelian_naturality F i,
      hc, hc, hc]
    simp only [map_sub]
    repeat rw [abRestrict_comp G]
    abel
  obtain ⟨b, hb⟩ := localizingSheaf_cechOne_eq_coboundary F hF f hf c hcocycle
  let a' (j : t) := a j - i.hom.app (op (U j)) (b j)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj U a' := by
    intro j k
    change abRestrict G inf_le_left (a' j) = abRestrict G inf_le_right (a' k)
    have hh := congrArg (i.hom.app (op (U j ⊓ U k))) (hb j k)
    rw [map_sub, affineModuleAbelian_naturality F i,
      affineModuleAbelian_naturality F i, hc j k] at hh
    dsimp only [a']
    simp only [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hh.symm
  obtain ⟨v, hv, _⟩ := G.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
    hcover a' hcompat
  refine ⟨v, ?_⟩
  apply H.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcover
  intro j
  change abRestrict H le_top (p.hom.app (op ⊤) v) = _
  rw [← abRestrict_naturality p le_top, hv]
  dsimp only [a']
  rw [map_sub, ha]
  have hw : p.hom.app (op (U j)) (i.hom.app (op (U j)) (b j)) = 0 := by
    exact congrArg (fun q : affineModuleAbelianSheaf F ⟶ H => q.hom.app (op (U j)) (b j)) w
  rw [hw, sub_zero]

end Normalizer
