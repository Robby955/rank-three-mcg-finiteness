import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Exactness of the actual inverse-image functor on sheaves of abelian groups. -/

noncomputable section

namespace Normalizer

open CategoryTheory CategoryTheory.Limits

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves preserves finite limits: inverse image on
opens is representably flat, and the actual site pullback is left exact. -/
theorem abelianSheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  unfold TopCat.Sheaf.pullback
  apply CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits

attribute [local instance] abelianSheafPullback_preservesFiniteLimits

/-- Inverse image preserves finite colimits by its actual pushforward adjunction. -/
theorem abelianSheafPullback_preservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) :=
  inferInstance

/-- The actual inverse-image functor on abelian sheaves is additive. -/
theorem abelianSheafPullback_additive :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] abelianSheafPullback_additive

/-- A short exact sequence of abelian sheaves remains short exact under the
actual inverse-image functor of any continuous map. -/
theorem abelianSheafPullback_shortExact
    (S : ShortComplex (Y.Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).ShortExact :=
  hS.map_of_exact _

end Normalizer
