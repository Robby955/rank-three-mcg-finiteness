import Normalizer.CurveFiniteMap
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! Extension of generic maps on normal integral curves. Normality is
expressed by integral closedness of the actual structure-sheaf stalks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
variable {X Y S : Scheme.{u}}

/-- A Noetherian integral scheme of dimension at most one has valuation
local rings at every point where its actual stalk is integrally closed.
This includes the generic field stalk. -/
theorem normalCurve_stalk_valuationRing [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] : ValuationRing (X.presheaf.stalk x) := by
  have hd : Order.krullDim X ≤ 1 := by
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight]
    exact (Order.coheight_le_krullDim x).trans hd
  have : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk x) := {}
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 3 2).mp (inferInstance : IsDedekindDomain (X.presheaf.stalk x))

/-- Restricting a partial map to the generic point agrees with first
restricting to an actual stalk and then to its fraction field. -/
theorem partialMap_genericRestriction_eq_stalkRestriction [IsIntegral X]
    (f : X.PartialMap Y) {x : X} (hx : x ∈ f.domain) :
    Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      f.fromSpecStalkOfMem hx = f.fromFunctionField := by
  dsimp only [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromFunctionField]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono f.domain.ι).mp
  simp

/-- Properness extends an actual generic map to any valuation stalk.
The source, fraction field, structural square and its lift are constructed. -/
theorem genericMap_lift_to_valuationStalk [IsIntegral X]
    (p : X ⟶ S) (q : Y ⟶ S) [IsProper q]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ q = X.fromSpecStalk (genericPoint X) ≫ p)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ ψ : Spec (X.presheaf.stalk x) ⟶ Y,
      ψ ≫ q = X.fromSpecStalk x ≫ p ∧
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ ψ = φ := by
  have hv : ValuativeCriterion.Existence q := by
    have hq : UniversallyClosed q := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hq
    exact hq.1
  let sq : ValuativeCommSq q :=
    { R := X.presheaf.stalk x
      commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
      domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
      valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
      K := X.functionField
      field := inferInstanceAs (Field X.functionField)
      algebra := stalkFunctionFieldAlgebra X x
      isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := φ
      i₂ := X.fromSpecStalk x ≫ p
      commSq := ⟨by
        change φ ≫ q = Spec.map (X.presheaf.stalkSpecializes
          (genericPoint_specializes x)) ≫ X.fromSpecStalk x ≫ p
        simpa using hφ⟩ }
  obtain ⟨ψ, hgeneric, hbase⟩ := (hv sq).exists_lift
  exact ⟨ψ, hbase, hgeneric⟩

/-- The rational map supplied by an actual generic map is defined at every
valuation stalk of the source. The local representative is spread out from
the valuative lift, and agreement at the generic point is proved. -/
theorem genericMap_mem_domain_of_valuationStalk [IsIntegral X]
    (p : X ⟶ S) (q : Y ⟶ S) [IsProper q]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ q = X.fromSpecStalk (genericPoint X) ≫ p)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    x ∈ (Scheme.RationalMap.ofFunctionField p q φ hφ).domain := by
  obtain ⟨ψ, hbase, hgeneric⟩ := genericMap_lift_to_valuationStalk p q φ hφ x
  let f := Scheme.PartialMap.ofFromSpecStalk p q ψ hbase
  have hx : x ∈ f.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk p q ψ hbase
  refine Scheme.RationalMap.mem_domain.mpr ⟨f, hx, ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_ofFunctionField,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    ← partialMap_genericRestriction_eq_stalkRestriction f hx]
  rw [Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  exact hgeneric

/-- A rational map defined everywhere on a reduced source, with separated
target, is represented by an actual global morphism. -/
theorem rationalMap_exists_hom_of_domain_eq_top [IsReduced X] [Y.IsSeparated]
    (r : X ⤏ Y) (hd : r.domain = ⊤) : ∃ f : X ⟶ Y, f.toRationalMap = r := by
  let g := r.toPartialMap
  have hg : g.toRationalMap = r := r.toRationalMap_toPartialMap
  have hgtop : g.domain = ⊤ := hd
  obtain ⟨U, hU, g⟩ := g
  change U = ⊤ at hgtop
  subst U
  refine ⟨X.topIso.inv ≫ g, ?_⟩
  rw [← hg]
  apply congrArg Scheme.PartialMap.toRationalMap
  apply (Scheme.PartialMap.ext_iff _ _).mpr
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.toPartialMap]

/-- Two morphisms from an integral scheme to a separated scheme agreeing
on the actual generic field are equal. -/
theorem schemeHom_eq_of_genericRestriction [IsIntegral X] [Y.IsSeparated]
    (f g : X ⟶ Y)
    (h : X.fromSpecStalk (genericPoint X) ≫ f = X.fromSpecStalk (genericPoint X) ≫ g) :
    f = g := by
  have he : f.toPartialMap.equiv g.toPartialMap :=
    Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ (x := genericPoint X)
      trivial trivial (by simpa using h)
  have hp := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated
    (S := ⊤_ Scheme) (f := f.toPartialMap) (g := g.toPartialMap) rfl).mp he
  obtain ⟨_, hh⟩ := (Scheme.PartialMap.ext_iff _ _).mp hp
  exact (cancel_epi X.topIso.hom).mp (by
    simpa [Scheme.Hom.toPartialMap] using hh)

/-- On an integral scheme with valuation stalks, any generic map to a
proper target extends uniquely to an actual morphism over the base.
Local lifts and spreading out prove that its rational-map domain is all X. -/
theorem valuationStalks_genericMap_existsUnique [IsIntegral X] [S.IsSeparated]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (p : X ⟶ S) (q : Y ⟶ S) [IsProper q]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ q = X.fromSpecStalk (genericPoint X) ≫ p) :
    ∃! f : X ⟶ Y, f ≫ q = p ∧ X.fromSpecStalk (genericPoint X) ≫ f = φ := by
  have : Y.IsSeparated := by
    constructor
    have : IsSeparated (q ≫ terminal.from S) := inferInstance
    simpa using this
  let r := Scheme.RationalMap.ofFunctionField p q φ hφ
  have hd : r.domain = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_iff_forall.mpr
    exact fun x => genericMap_mem_domain_of_valuationStalk p q φ hφ x
  obtain ⟨f, hf⟩ := rationalMap_exists_hom_of_domain_eq_top r hd
  have hgen : X.fromSpecStalk (genericPoint X) ≫ f = φ := by
    have h := congrArg Scheme.RationalMap.fromFunctionField hf
    simpa [r, Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.PartialMap.fromFunctionField,
      Scheme.RationalMap.fromFunctionField_ofFunctionField] using h
  refine ⟨f, ⟨?_, hgen⟩, ?_⟩
  · apply schemeHom_eq_of_genericRestriction
    simpa only [← Category.assoc, hgen] using hφ
  · intro g hg
    exact schemeHom_eq_of_genericRestriction g f (hg.2.trans hgen.symm)

/-- Normal integral curves have unique extensions of generic maps into
proper targets. The valuation property is derived from Noetherianity,
dimension at most one and integral closedness of the actual stalks. -/
theorem normalCurve_genericMap_existsUnique [IsIntegral X] [IsLocallyNoetherian X]
    [S.IsSeparated] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ S) (q : Y ⟶ S) [IsProper q]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ q = X.fromSpecStalk (genericPoint X) ≫ p) :
    ∃! f : X ⟶ Y, f ≫ q = p ∧ X.fromSpecStalk (genericPoint X) ≫ f = φ := by
  have := fun x => normalCurve_stalk_valuationRing hdim x
  exact valuationStalks_genericMap_existsUnique p q φ hφ

end Normalizer
