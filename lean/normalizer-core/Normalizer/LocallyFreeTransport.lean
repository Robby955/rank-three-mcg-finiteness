import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Topology.Sheaves.Sheaf

/-! Transport of actual local generators along sheaf isomorphisms.

The cover and generating index types are kept unchanged. Local freeness and
finite type are mathlib's properties of the actual module sheaf. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

open CategoryTheory

universe u w

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {E H : SheafOfModules.{u} R}

/-- Transport local generators through an actual sheaf isomorphism, keeping
the same cover and the same generator index types. -/
def localGeneratorsDataOfIso (e : E ≅ H)
    (q : SheafOfModules.LocalGeneratorsData.{w} E) :
    SheafOfModules.LocalGeneratorsData.{w} H where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi
    ((SheafOfModules.overFunctor R (q.X i)).map e.hom)

set_option maxHeartbeats 800000 in
/-- Local freeness is preserved by an actual isomorphism of module sheaves. -/
theorem isLocallyFree_of_iso (e : E ≅ H) [E.IsLocallyFree] : H.IsLocallyFree := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := E)
  let := hq
  refine SheafOfModules.IsLocallyFree.mk (M := H) ⟨localGeneratorsDataOfIso e q, ?_⟩
  constructor
  intro i
  change IsIso ((q.generators i).ofEpi
    ((SheafOfModules.overFunctor R (q.X i)).map e.hom)).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- Finite type is preserved by an actual isomorphism of module sheaves. -/
theorem isFiniteType_of_iso (e : E ≅ H) [E.IsFiniteType] : H.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData E
  refine SheafOfModules.IsFiniteType.mk (M := H) ⟨localGeneratorsDataOfIso e q, ?_⟩
  constructor
  intro i
  let := hq.isFiniteType i
  exact inferInstanceAs ((q.generators i).ofEpi
    ((SheafOfModules.overFunctor R (q.X i)).map e.hom)).IsFiniteType

/-- A free sheaf indexed by a finite type has finitely many local generators. -/
theorem freeSheaf_isFiniteType (I : Type u) [Finite I] :
    (SheafOfModules.free (R := R) I).IsFiniteType := by
  let G := SheafOfModules.free.generatingSections (R := R) I
  let : G.IsFiniteType := ⟨inferInstanceAs (Finite I)⟩
  refine SheafOfModules.IsFiniteType.mk (M := SheafOfModules.free (R := R) I)
    ⟨G.localGeneratorsData, ?_⟩
  constructor
  intro i
  change (G.map (SheafOfModules.pushforward (𝟙 (R.over i))) (Iso.refl _)).IsFiniteType
  infer_instance

end Normalizer
