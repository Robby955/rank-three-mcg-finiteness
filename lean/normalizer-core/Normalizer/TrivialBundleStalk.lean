import Normalizer.TrivialBundle

/-! The basis of an actual finite trivial bundle at every stalk.
Its coordinates are induced by actual sheaf projections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable (X : Scheme.{u}) (ι : Type u) [Fintype ι] (x : X)

local notation "T" => schemeTrivialBundle X ι

/-- Actual stalk coordinates are the stalk functionals of the actual
coordinate projections. -/
def schemeTrivialStalkCoordinates :
    (T).presheaf.stalk x →ₗ[X.presheaf.stalk x] (ι → X.presheaf.stalk x) :=
  LinearMap.pi (fun i => schemeStalkFunctional (schemeTrivialProjection X ι i) x)

/-- The actual stalk frame is the linear combination of germs of the
constructed standard global sections. -/
def schemeTrivialStalkFrame :
    (ι → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x] (T).presheaf.stalk x where
  toFun a := ∑ i, a i • (T).presheaf.germ ⊤ x trivial (schemeTrivialSection X ι ⊤ i)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Stalk coordinates of a section germ are germs of its actual
regular-function coordinates. -/
theorem schemeTrivialStalkCoordinates_germ (U : X.Opens) (hx : x ∈ U)
    (s : Γ(T, U)) (i : ι) :
    schemeTrivialStalkCoordinates X ι x ((T).presheaf.germ U x hx s) i =
      X.presheaf.germ U x hx (schemeTrivialCoordinates X ι U s i) := by
  exact (schemeStalkFunctional_germ (schemeTrivialProjection X ι i) x U hx s).trans
    (congrArg (X.presheaf.germ U x hx) (schemeTrivialCoordinates_apply X ι U s i).symm)

variable [DecidableEq ι]

/-- Coordinates recover every tuple from its actual stalk-frame image. -/
theorem schemeTrivialStalkCoordinates_frame (a : ι → X.presheaf.stalk x) :
    schemeTrivialStalkCoordinates X ι x (schemeTrivialStalkFrame X ι x a) = a := by
  ext j
  change schemeTrivialStalkCoordinates X ι x
    (∑ i, a i • (T).presheaf.germ ⊤ x trivial (schemeTrivialSection X ι ⊤ i)) j = a j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    schemeTrivialStalkCoordinates_germ, schemeTrivialCoordinates_section]
  simp

/-- Independence of the actual stalk frame follows from its constructed
coordinate left inverse. -/
theorem schemeTrivialStalkFrame_injective :
    Function.Injective (schemeTrivialStalkFrame X ι x) :=
  Function.LeftInverse.injective (schemeTrivialStalkCoordinates_frame X ι x)

/-- Every actual stalk element has the constructed frame expansion. -/
theorem schemeTrivialStalkFrame_coordinates (a : (T).presheaf.stalk x) :
    schemeTrivialStalkFrame X ι x (schemeTrivialStalkCoordinates X ι x a) = a := by
  obtain ⟨U, hx, s, rfl⟩ := (T).presheaf.exists_germ_eq a
  have hg (i : ι) : (T).presheaf.germ U x hx (schemeTrivialSection X ι U i) =
      (T).presheaf.germ ⊤ x trivial (schemeTrivialSection X ι ⊤ i) := by
    have hr := schemeTrivialSection_restrict X ι (show U ≤ ⊤ from le_top) i
    exact (congrArg ((T).presheaf.germ U x hx) hr).symm.trans
      ((T).presheaf.germ_res_apply (homOfLE le_top) x hx (schemeTrivialSection X ι ⊤ i))
  change ∑ i, schemeTrivialStalkCoordinates X ι x ((T).presheaf.germ U x hx s) i •
    (T).presheaf.germ ⊤ x trivial (schemeTrivialSection X ι ⊤ i) = _
  simp_rw [schemeTrivialStalkCoordinates_germ, ← hg, ← schemeModule_germ_smul]
  rw [← map_sum, schemeTrivialSection_expansion]

/-- The actual stalk of the finite trivial sheaf has its canonical
coordinate equivalence over the actual local ring. -/
def schemeTrivialStalkEquiv :
    (ι → X.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] (T).presheaf.stalk x where
  __ := schemeTrivialStalkFrame X ι x
  invFun := schemeTrivialStalkCoordinates X ι x
  left_inv := schemeTrivialStalkCoordinates_frame X ι x
  right_inv := schemeTrivialStalkFrame_coordinates X ι x

end Normalizer
