import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Lie.Quotient

/-! The normalizer and its grading character for a free rank-one submodule.
The coefficient ring is any commutative ring, so local regular functions are
allowed. Injectivity of `r ↦ r • m` expresses that m is a frame of its image.
No curve, local trivialization, or global constancy is defined into existence. -/

namespace Normalizer
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A cyclic submodule is an abelian Lie subalgebra. -/
def frameLine (m : L) : LieSubalgebra R L where
  toSubmodule := Submodule.span R {m}
  lie_mem' := by
    intro x y hx hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [smul_lie, lie_smul, lie_self, smul_zero]
    exact Submodule.zero_mem _

theorem frameLine_abelian (m : L) (x y : frameLine (R := R) m) : ⁅x, y⁆ = 0 := by
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
  change ⁅(x : L), (y : L)⁆ = 0
  rw [← ha, ← hb]
  simp

/-- Membership in mathlib's actual normalizer is determined on a frame. -/
theorem mem_frameNormalizer (m x : L) :
    x ∈ (frameLine (R := R) m).normalizer ↔ ∃ a : R, ⁅x, m⁆ = a • m := by
  rw [LieSubalgebra.mem_normalizer_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (h m (Submodule.subset_span (Set.mem_singleton m)))
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, ha⟩ y hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change ⁅x, b • m⁆ ∈ Submodule.span R {m}
    rw [lie_smul, ha]
    exact Submodule.smul_mem _ b (Submodule.smul_mem _ a
      (Submodule.subset_span (Set.mem_singleton m)))

private noncomputable def frameCoefficient (m : L)
    (x : (frameLine (R := R) m).normalizer) : R :=
  Classical.choose ((mem_frameNormalizer m x).mp x.property)

private theorem frameCoefficient_spec (m : L)
    (x : (frameLine (R := R) m).normalizer) :
    ⁅(x : L), m⁆ = frameCoefficient m x • m :=
  Classical.choose_spec ((mem_frameNormalizer m x).mp x.property)

/-- The actual scalar action of the normalizer on the framed line. -/
noncomputable def frameCharacter (m : L)
    (hm : Function.Injective (fun r : R => r • m)) :
    (frameLine (R := R) m).normalizer →ₗ[R] R where
  toFun := frameCoefficient m
  map_add' x y := by
    apply hm
    change frameCoefficient m (x + y) • m = (frameCoefficient m x + frameCoefficient m y) • m
    rw [← frameCoefficient_spec, add_smul]
    change ⁅(x : L) + (y : L), m⁆ = _
    rw [add_lie, frameCoefficient_spec, frameCoefficient_spec]
  map_smul' a x := by
    apply hm
    change frameCoefficient m (a • x) • m = (a * frameCoefficient m x) • m
    rw [← frameCoefficient_spec]
    change ⁅a • (x : L), m⁆ = (a * frameCoefficient m x) • m
    rw [smul_lie, frameCoefficient_spec, smul_smul]

theorem frameCharacter_action (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer) :
    ⁅(x : L), m⁆ = frameCharacter m hm x • m :=
  frameCoefficient_spec m x

theorem frameCharacter_eq (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer) (a : R)
    (ha : ⁅(x : L), m⁆ = a • m) : frameCharacter m hm x = a := by
  apply hm
  change frameCharacter m hm x • m = a • m
  rw [← frameCharacter_action m hm, ha]

/-- A character vanishes on commutators: scalar actions on a line commute. -/
theorem frameCharacter_bracket (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x y : (frameLine (R := R) m).normalizer) :
    frameCharacter m hm ⁅x, y⁆ = 0 := by
  apply frameCharacter_eq m hm
  change ⁅⁅(x : L), (y : L)⁆, m⁆ = _
  rw [lie_lie, frameCharacter_action m hm, frameCharacter_action m hm,
    lie_smul, lie_smul, frameCharacter_action m hm, frameCharacter_action m hm, zero_smul]
  rw [smul_comm (frameCharacter m hm x) (frameCharacter m hm y)]
  exact sub_self _

/-- The frame line is an actual Lie ideal in its normalizer. -/
def frameIdeal (m : L) : LieIdeal R (frameLine (R := R) m).normalizer where
  toSubmodule := (frameLine m).toSubmodule.comap (frameLine m).normalizer.toSubmodule.subtype
  lie_mem := by
    intro x y hy
    exact (frameLine m).ideal_in_normalizer x.property hy

theorem frameCharacter_kills_line (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer) (hx : x ∈ frameIdeal m) :
    frameCharacter m hm x = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  change a • m = (x : L) at ha
  apply frameCharacter_eq m hm
  rw [← ha]
  simp

/-- Changing a normalizer lift by a line section leaves the character unchanged. -/
theorem frameCharacter_change_lift (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x y : (frameLine (R := R) m).normalizer) (hxy : x - y ∈ frameIdeal m) :
    frameCharacter m hm x = frameCharacter m hm y := by
  have h := frameCharacter_kills_line m hm (x - y) hxy
  rw [map_sub] at h
  exact sub_eq_zero.mp h

/-- The grading character descends to the actual quotient by the line. -/
noncomputable def quotientFrameCharacter (m : L)
    (hm : Function.Injective (fun r : R => r • m)) :
    ((frameLine (R := R) m).normalizer ⧸ frameIdeal m) →ₗ[R] R :=
  (frameIdeal m).toSubmodule.liftQ (frameCharacter m hm)
    (fun x hx => frameCharacter_kills_line m hm x hx)

theorem quotientFrameCharacter_mk (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer) :
    quotientFrameCharacter m hm ((frameIdeal m).toSubmodule.mkQ x) =
      frameCharacter m hm x := rfl

theorem quotientFrameCharacter_bracket (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (x y : (frameLine (R := R) m).normalizer ⧸ frameIdeal m) :
    quotientFrameCharacter m hm ⁅x, y⁆ = 0 := by
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  exact frameCharacter_bracket m hm a b

/-- Changing a line-bundle frame by a unit leaves its generated subalgebra
and hence its actual normalizer unchanged. -/
theorem frameLine_unit (m : L) (u : Rˣ) :
    frameLine (R := R) ((u : R) • m) = frameLine m := by
  ext x
  change x ∈ Submodule.span R {(u : R) • m} ↔ x ∈ Submodule.span R {m}
  rw [Submodule.span_singleton_smul_eq u.isUnit]

/-- The scalar in the action equation is unchanged by a unit frame change. -/
theorem frame_action_unit_iff (m x : L) (u : Rˣ) (a : R) :
    ⁅x, (u : R) • m⁆ = a • ((u : R) • m) ↔ ⁅x, m⁆ = a • m := by
  rw [lie_smul, smul_comm a (u : R) m]
  constructor
  · intro h
    have hi := congrArg (fun z : L => ((u⁻¹ : Rˣ) : R) • z) h
    simpa only [smul_smul, Units.inv_mul, Units.inv_mul_cancel_left, one_smul] using hi
  · intro h
    rw [h]

/-- Unit rescaling preserves the injectivity required of a frame. -/
theorem frame_unit_injective (m : L) (u : Rˣ)
    (hm : Function.Injective (fun r : R => r • m)) :
    Function.Injective (fun r : R => r • ((u : R) • m)) := by
  intro a b hab
  have he : a * (u : R) = b * (u : R) := hm (by simpa only [smul_smul] using hab)
  have hi := congrArg (fun r : R => r * ((u⁻¹ : Rˣ) : R)) he
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hi

/-- Local frame characters agree on overlaps after identifying an element
of the two equal normalizers. -/
theorem frameCharacter_unit (m : L) (u : Rˣ)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer)
    (y : (frameLine (R := R) ((u : R) • m)).normalizer)
    (hxy : (x : L) = (y : L)) :
    frameCharacter m hm x =
      frameCharacter ((u : R) • m) (frame_unit_injective m u hm) y := by
  apply frameCharacter_eq m hm
  rw [hxy]
  exact (frame_action_unit_iff m (y : L) u _).mp
    (frameCharacter_action ((u : R) • m) (frame_unit_injective m u hm) y)

/-- On an overlap, changing both the line frame and the representative of
a quotient section leaves its scalar action unchanged. -/
theorem frameCharacter_unit_mod_line (m : L) (u : Rˣ)
    (hm : Function.Injective (fun r : R => r • m))
    (x : (frameLine (R := R) m).normalizer)
    (y : (frameLine (R := R) ((u : R) • m)).normalizer)
    (hxy : (x : L) - (y : L) ∈ Submodule.span R {m}) :
    frameCharacter m hm x =
      frameCharacter ((u : R) • m) (frame_unit_injective m u hm) y := by
  let y' : (frameLine (R := R) m).normalizer :=
    ⟨(y : L), by
      apply (mem_frameNormalizer m (y : L)).mpr
      obtain ⟨a, ha⟩ := (mem_frameNormalizer ((u : R) • m) (y : L)).mp y.property
      exact ⟨a, (frame_action_unit_iff m (y : L) u a).mp ha⟩⟩
  calc
    frameCharacter m hm x = frameCharacter m hm y' :=
      frameCharacter_change_lift m hm x y' hxy
    _ = _ := frameCharacter_unit m u hm y' y rfl

section Restriction
variable {S K : Type*} [CommRing S] [LieRing K] [LieAlgebra S K]
  {α : R →+* S}

/-- A bracket-preserving semilinear restriction takes the framed normalizer
to the normalizer of the restricted frame. -/
def frameNormalizerMap (m : L) (f : L →ₛₗ[α] K)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) :
    (frameLine (R := R) m).normalizer →ₛₗ[α]
      (frameLine (R := S) (f m)).normalizer where
  toFun x := ⟨f (x : L), by
    apply (mem_frameNormalizer (f m) _).mpr
    obtain ⟨a, ha⟩ := (mem_frameNormalizer m x).mp x.property
    refine ⟨α a, ?_⟩
    rw [← hf, ha, f.map_smulₛₗ]⟩
  map_add' x y := by apply Subtype.ext; exact f.map_add _ _
  map_smul' a x := by apply Subtype.ext; exact f.map_smulₛₗ _ _

/-- Local action coefficients restrict by the coefficient-ring map. -/
theorem frameCharacter_restrict (m : L) (f : L →ₛₗ[α] K)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (hm : Function.Injective (fun r : R => r • m))
    (hk : Function.Injective (fun s : S => s • f m))
    (x : (frameLine (R := R) m).normalizer) :
    frameCharacter (f m) hk (frameNormalizerMap m f hf x) = α (frameCharacter m hm x) := by
  apply frameCharacter_eq (f m) hk
  change ⁅f (x : L), f m⁆ = _
  rw [← hf, frameCharacter_action m hm, f.map_smulₛₗ]

/-- Restriction descends to the actual normalizer quotient because it sends
the source frame line into the target frame line. -/
def frameQuotientMap (m : L) (f : L →ₛₗ[α] K)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) :
    ((frameLine (R := R) m).normalizer ⧸ frameIdeal m) →ₛₗ[α]
      ((frameLine (R := S) (f m)).normalizer ⧸ frameIdeal (f m)) :=
  (frameIdeal m).toSubmodule.mapQ (frameIdeal (f m)).toSubmodule
    (frameNormalizerMap m f hf) (by
      intro x hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      change a • m = (x : L) at ha
      change f (x : L) ∈ Submodule.span S {f m}
      apply Submodule.mem_span_singleton.mpr
      refine ⟨α a, ?_⟩
      rw [← f.map_smulₛₗ, ha])

/-- The character on the normalizer quotient commutes with restriction. -/
theorem quotientFrameCharacter_restrict (m : L) (f : L →ₛₗ[α] K)
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (hm : Function.Injective (fun r : R => r • m))
    (hk : Function.Injective (fun s : S => s • f m))
    (x : (frameLine (R := R) m).normalizer ⧸ frameIdeal m) :
    quotientFrameCharacter (f m) hk (frameQuotientMap m f hf x) =
      α (quotientFrameCharacter m hm x) := by
  refine Quotient.inductionOn' x ?_
  intro a
  exact frameCharacter_restrict m f hf hm hk a

end Restriction

end Normalizer
