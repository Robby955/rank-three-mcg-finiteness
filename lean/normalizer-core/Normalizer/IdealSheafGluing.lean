import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Exact gluing of ideal-sheaf data along finite quasi-compact open families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry

universe u v
variable {X Y Z W : Scheme.{u}}

/-- Pulling back along an open immersion preserves finite intersections
of ideal-sheaf data. -/
theorem idealSheaf_comap_iInf {ι : Type v} [Finite ι]
    (I : ι → Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (iInf I).comap f = ⨅ i, (I i).comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_iInf, Ideal.comap_iInf]

/-- The kernel ideal of a quasi-compact morphism restricts exactly under
an actual open pullback square. -/
theorem idealSheaf_ker_comap_of_isPullback
    (f : X ⟶ Y) (f' : W ⟶ Z) (iX : W ⟶ X) (iY : Z ⟶ Y)
    [QuasiCompact f] [IsOpenImmersion iY] (h : IsPullback f' iX iY f) :
    f.ker.comap iY = f'.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iX iY h U).symm

/-- An ideal pushed along a quasi-compact open immersion restricts back
to the original ideal, rather than merely containing it. -/
theorem idealSheaf_comap_map_open (I : X.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact f] : (I.map f).comap f = I := by
  have h : IsPullback I.subschemeι (𝟙 _) f (I.subschemeι ≫ f) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  change (I.subschemeι ≫ f).ker.comap f = I
  rw [idealSheaf_ker_comap_of_isPullback _ _ _ _ h, I.ker_subschemeι]

/-- Pushforward of an ideal along a quasi-compact map commutes with
restriction to an open subscheme, using the actual pullback. -/
theorem idealSheaf_comap_map_open_baseChange (I : X.IdealSheafData)
    (f : X ⟶ Y) [QuasiCompact f] (g : Z ⟶ Y) [IsOpenImmersion g] :
    (I.map f).comap g =
      (I.comap (pullback.snd g f)).map (pullback.fst g f) := by
  let J := I.comap (pullback.snd g f)
  let z := Scheme.IdealSheafData.subschemeMap J I (pullback.snd g f)
    (I.le_map_comap (pullback.snd g f))
  have h : IsPullback J.subschemeι z (pullback.snd g f) I.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · exact (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    · simp [J]
  have h' := (h.flip.paste_vert (IsPullback.of_hasPullback g f).flip).flip
  exact idealSheaf_ker_comap_of_isPullback _ _ _ _ h'

/-- The global ideal obtained as the finite intersection of the actual
pushforwards of local ideals. Exact restriction is proved separately. -/
def finiteIdealSheafGlue {ι : Type v} (Y : ι → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) (I : ∀ i, (Y i).IdealSheafData) : X.IdealSheafData :=
  ⨅ i, (I i).map (f i)

/-- Equality on the actual intersection of two opens gives compatibility
on their categorical pullback. -/
theorem idealSheaf_overlap_of_inf (U V : X.Opens)
    (I : U.toScheme.IdealSheafData) (J : V.toScheme.IdealSheafData)
    (h : I.comap (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) =
      J.comap (X.homOfLE (inf_le_right : U ⊓ V ≤ V))) :
    I.comap (pullback.fst U.ι V.ι) = J.comap (pullback.snd U.ι V.ι) := by
  have h' := congrArg
    (fun K ↦ K.comap (isPullback_opens_inf U V).isoPullback.inv) h
  simpa only [← Scheme.IdealSheafData.comap_comp,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_inv_snd] using h'

/-- Compatible local ideals on a finite family of quasi-compact open
immersions have a global ideal whose restrictions are exactly the inputs.
Compatibility is equality on the actual pairwise pullbacks. -/
theorem finiteIdealSheafGlue_comap {ι : Type v} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] [∀ i, QuasiCompact (f i)]
    (I : ∀ i, (Y i).IdealSheafData)
    (h : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) =
      (I j).comap (pullback.snd (f i) (f j))) (a : ι) :
    (finiteIdealSheafGlue Y f I).comap (f a) = I a := by
  change (⨅ i, (I i).map (f i)).comap (f a) = I a
  rw [idealSheaf_comap_iInf]
  apply le_antisymm
  · exact (iInf_le (fun i ↦ ((I i).map (f i)).comap (f a)) a).trans
      (idealSheaf_comap_map_open (I a) (f a)).le
  · apply le_iInf
    intro i
    rw [idealSheaf_comap_map_open_baseChange, ← h a i]
    exact (I a).le_map_comap (pullback.fst (f a) (f i))

/-- A finite open cover with quasi-compact inclusions glues compatible
actual ideal-sheaf data to an actual global ideal with exact restrictions. -/
theorem exists_idealSheaf_of_finite_openCover (𝒰 : X.OpenCover.{v})
    [Finite 𝒰.I₀] [∀ i, QuasiCompact (𝒰.f i)]
    (I : ∀ i, (𝒰.X i).IdealSheafData)
    (h : ∀ i j, (I i).comap (pullback.fst (𝒰.f i) (𝒰.f j)) =
      (I j).comap (pullback.snd (𝒰.f i) (𝒰.f j))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (𝒰.f i) = I i :=
  ⟨finiteIdealSheafGlue 𝒰.X 𝒰.f I, finiteIdealSheafGlue_comap 𝒰.X 𝒰.f I h⟩

end Normalizer
