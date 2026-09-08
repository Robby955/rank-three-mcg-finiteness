import Normalizer.Obstruction
import Mathlib.LinearAlgebra.Isomorphisms
import Normalizer.FrameCharacter

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]

def rightAdjoint (m : Mat F) : Mat F →ₗ[F] Mat F where
  toFun X := comm X m
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  map_smul' a X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comm, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> ring

/-- The actual trace-zero matrix line normalizer, not a coordinate definition. -/
def lineNormalizer (m : Mat F) : Submodule F (Mat F) :=
  (Matrix.traceLinearMap (Fin 3) F F).ker ⊓
    (Submodule.span F {m}).comap (rightAdjoint m)

omit [CharZero F] in
theorem mem_lineNormalizer (m X : Mat F) : X ∈ lineNormalizer m ↔
    Matrix.trace X = 0 ∧ ∃ t : F, comm X m = t • m := by
  simp only [lineNormalizer, Submodule.mem_inf, LinearMap.mem_ker,
    Matrix.traceLinearMap_apply, Submodule.mem_comap, Submodule.mem_span_singleton]
  exact and_congr_right (fun _ => exists_congr (fun _ => eq_comm))

def semCoordinates : Mat F →ₗ[F] (Fin 3 → F) where
  toFun X := ![X 0 0 - X 1 1, X 0 1, X 1 0]
  map_add' X Y := by ext i; fin_cases i <;> simp; ring
  map_smul' a X := by ext i; fin_cases i <;> simp; ring

def nilCoordinates : Mat F →ₗ[F] (Fin 4 → F) where
  toFun X := ![X 0 0 - X 1 1, -(X 2 2), X 0 2, X 2 1]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a X := by ext i; fin_cases i <;> simp; ring

theorem sem_coordinates_lift (v : Fin 3 → F) (z : F) :
    semCoordinates (semLift v + z • semM) = v := by
  ext i; fin_cases i <;> simp [semCoordinates, semLift, semM]

theorem nil_coordinates_lift (v : Fin 4 → F) (z : F) :
    nilCoordinates (nilLift v + z • nilM) = v := by
  ext i; fin_cases i <;> simp [nilCoordinates, nilLift, nilM]; ring

def semProjection : lineNormalizer (semM : Mat F) →ₗ[F] (Fin 3 → F) :=
  semCoordinates.comp (lineNormalizer semM).subtype

def nilProjection : lineNormalizer (nilM : Mat F) →ₗ[F] (Fin 4 → F) :=
  nilCoordinates.comp (lineNormalizer nilM).subtype

theorem sem_projection_surjective : Function.Surjective (semProjection (F := F)) := by
  intro v
  have hm : semLift v + (0 : F) • semM ∈ lineNormalizer semM := by
    apply (mem_lineNormalizer _ _).mpr
    have h := (sem_normalizer (semLift v + (0 : F) • semM) 0).mpr ⟨v, 0, rfl, rfl⟩
    exact ⟨h.1, 0, h.2⟩
  exact ⟨⟨_, hm⟩, sem_coordinates_lift v 0⟩

theorem nil_projection_surjective : Function.Surjective (nilProjection (F := F)) := by
  intro v
  have hm : nilLift v + (0 : F) • nilM ∈ lineNormalizer nilM := by
    apply (mem_lineNormalizer _ _).mpr
    have h := (nil_normalizer (nilLift v + (0 : F) • nilM) (v 0)).mpr ⟨v, 0, rfl, rfl⟩
    exact ⟨h.1, v 0, h.2⟩
  exact ⟨⟨_, hm⟩, nil_coordinates_lift v 0⟩

/-- The kernel being quotiented is exactly the distinguished line. -/
theorem sem_projection_kernel (X : lineNormalizer (semM : Mat F)) :
    X ∈ (semProjection (F := F)).ker ↔ ∃ z : F, (X : Mat F) = z • semM := by
  obtain ⟨htr, t, ht⟩ := (mem_lineNormalizer _ _).mp X.property
  obtain ⟨v, z, hv, _⟩ := (sem_normalizer _ t).mp ⟨htr, ht⟩
  change semCoordinates (X : Mat F) = 0 ↔ _
  rw [hv, sem_coordinates_lift]
  constructor
  · intro h; exact ⟨z, by ext i j; fin_cases i <;> fin_cases j <;> simp [h, semLift]⟩
  · rintro ⟨a, ha⟩
    have h := congrArg semCoordinates ha
    rw [sem_coordinates_lift] at h
    ext i
    have hi := congrFun h i
    fin_cases i <;> simpa [semCoordinates, semM] using hi

theorem nil_projection_kernel (X : lineNormalizer (nilM : Mat F)) :
    X ∈ (nilProjection (F := F)).ker ↔ ∃ z : F, (X : Mat F) = z • nilM := by
  obtain ⟨htr, t, ht⟩ := (mem_lineNormalizer _ _).mp X.property
  obtain ⟨v, z, hv, _⟩ := (nil_normalizer _ t).mp ⟨htr, ht⟩
  change nilCoordinates (X : Mat F) = 0 ↔ _
  rw [hv, nil_coordinates_lift]
  constructor
  · intro h; exact ⟨z, by ext i j; fin_cases i <;> fin_cases j <;> simp [h, nilLift]⟩
  · rintro ⟨a, ha⟩
    have h := congrArg nilCoordinates ha
    rw [nil_coordinates_lift] at h
    ext i
    have hi := congrFun h i
    fin_cases i <;> simpa [nilCoordinates, nilM] using hi

abbrev SemQuotient (F : Type*) [Field F] :=
  lineNormalizer (semM : Mat F) ⧸ (semProjection (F := F)).ker
abbrev NilQuotient (F : Type*) [Field F] :=
  lineNormalizer (nilM : Mat F) ⧸ (nilProjection (F := F)).ker

noncomputable def semQuotientEquiv : SemQuotient F ≃ₗ[F] (Fin 3 → F) :=
  (semProjection (F := F)).quotKerEquivOfSurjective (sem_projection_surjective (F := F))
noncomputable def nilQuotientEquiv : NilQuotient F ≃ₗ[F] (Fin 4 → F) :=
  (nilProjection (F := F)).quotKerEquivOfSurjective (nil_projection_surjective (F := F))

theorem sem_quotient_finrank : Module.finrank F (SemQuotient F) = 3 := by
  simpa using (semQuotientEquiv (F := F)).finrank_eq
theorem nil_quotient_finrank : Module.finrank F (NilQuotient F) = 4 := by
  simpa using (nilQuotientEquiv (F := F)).finrank_eq

/-- Matrix commutators in the full normalizer project to the stated bracket. -/
theorem sem_projection_bracket (X Y : lineNormalizer (semM : Mat F)) :
    semCoordinates (comm X Y) = semBracket (semProjection X) (semProjection Y) := by
  obtain ⟨hx, tx, htx⟩ := (mem_lineNormalizer _ _).mp X.property
  obtain ⟨hy, ty, hty⟩ := (mem_lineNormalizer _ _).mp Y.property
  obtain ⟨v, a, hv, _⟩ := (sem_normalizer _ tx).mp ⟨hx, htx⟩
  obtain ⟨w, b, hw, _⟩ := (sem_normalizer _ ty).mp ⟨hy, hty⟩
  change semCoordinates (comm (X : Mat F) (Y : Mat F)) =
    semBracket (semCoordinates (X : Mat F)) (semCoordinates (Y : Mat F))
  rw [hv, hw, sem_coordinates_lift, sem_coordinates_lift, sem_bracket_lift]
  simpa using sem_coordinates_lift (semBracket v w) 0

theorem nil_projection_bracket (X Y : lineNormalizer (nilM : Mat F)) :
    nilCoordinates (comm X Y) = nilBracket (nilProjection X) (nilProjection Y) := by
  obtain ⟨hx, tx, htx⟩ := (mem_lineNormalizer _ _).mp X.property
  obtain ⟨hy, ty, hty⟩ := (mem_lineNormalizer _ _).mp Y.property
  obtain ⟨v, a, hv, _⟩ := (nil_normalizer _ tx).mp ⟨hx, htx⟩
  obtain ⟨w, b, hw, _⟩ := (nil_normalizer _ ty).mp ⟨hy, hty⟩
  change nilCoordinates (comm (X : Mat F) (Y : Mat F)) =
    nilBracket (nilCoordinates (X : Mat F)) (nilCoordinates (Y : Mat F))
  rw [hv, hw, nil_coordinates_lift, nil_coordinates_lift, nil_bracket_lift,
    nil_coordinates_lift]

theorem sem_projection_character (X : lineNormalizer (semM : Mat F)) (t : F)
    (ht : comm (X : Mat F) semM = t • semM) : t = 0 := by
  have hx := ((mem_lineNormalizer _ _).mp X.property).1
  obtain ⟨_, _, _, h⟩ := (sem_normalizer _ t).mp ⟨hx, ht⟩
  exact h

theorem nil_projection_character (X : lineNormalizer (nilM : Mat F)) (t : F)
    (ht : comm (X : Mat F) nilM = t • nilM) : t = nilProjection X 0 := by
  have hx := ((mem_lineNormalizer _ _).mp X.property).1
  obtain ⟨v, a, hv, h⟩ := (nil_normalizer _ t).mp ⟨hx, ht⟩
  change t = nilCoordinates (X : Mat F) 0
  rw [hv, nil_coordinates_lift, h]

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

omit [CharZero F] in
/-- The abstract character agrees with the zero character of the explicit
semisimple normalizer, even before imposing trace zero. -/
theorem sem_frameCharacter
    (hm : Function.Injective (fun a : F => a • (semM : Mat F)))
    (x : (frameLine (R := F) (semM : Mat F)).normalizer) :
    frameCharacter semM hm x = 0 := by
  have ht := frameCharacter_action semM hm x
  change comm (x : Mat F) semM = frameCharacter semM hm x • semM at ht
  have h := congrArg (fun A : Mat F => A 0 0) ht
  simpa [comm, semM, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ] using h.symm

omit [CharZero F] in
/-- The abstract character is the D-coordinate used by the explicit
minimal-nilpotent calculation. -/
theorem nil_frameCharacter
    (hm : Function.Injective (fun a : F => a • (nilM : Mat F)))
    (x : (frameLine (R := F) (nilM : Mat F)).normalizer) :
    frameCharacter nilM hm x = nilCoordinates (x : Mat F) 0 := by
  have ht := frameCharacter_action nilM hm x
  change comm (x : Mat F) nilM = frameCharacter nilM hm x • nilM at ht
  have h := congrArg (fun A : Mat F => A 0 1) ht
  simpa [comm, nilM, nilCoordinates, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ] using h.symm

end Normalizer
