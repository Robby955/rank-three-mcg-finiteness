import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Localization.Submodule

/-! Regularity under flat, essentially finite type, unramified local maps. -/

noncomputable section

namespace Normalizer
open IsLocalRing

/-- Regularity ascends along a flat, essentially finite type, formally
unramified local algebra map. -/
theorem regularLocal_of_flat_unramified
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] : IsRegularLocalRing S := by
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  let : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have hmap := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have hgen := Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
    (IsNoetherian.noetherian (maximalIdeal R))
  rw [hmap] at hgen
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal S)
  have hle : (maximalIdeal R).height ≤ (maximalIdeal S).height := by
    rw [hheight]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast hgen
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := by
      rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast hle

end Normalizer
