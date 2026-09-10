import Normalizer.SheafStalkMap
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! A compatible bilinear operation on sections induces a bilinear operation
on the actual module stalk, characterized on germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (K : X.Modules)

private abbrev restrict {U V : X.Opens} (h : U ≤ V) (s : Γ(K, V)) : Γ(K, U) :=
  K.presheaf.map (homOfLE h).op s

private theorem restrict_comp {U V W : X.Opens} (h : U ≤ V) (i : V ≤ W)
    (s : Γ(K, W)) : restrict K h (restrict K i s) = restrict K (h.trans i) s := by
  exact (K.val.map_comp_apply (homOfLE i).op (homOfLE h).op s).symm

private theorem germ_restrict {U V : X.Opens} (h : U ≤ V) (x : X) (hx : x ∈ U)
    (s : Γ(K, V)) :
    K.presheaf.germ U x hx (restrict K h s) = K.presheaf.germ V x (h hx) s :=
  K.presheaf.germ_res_apply (homOfLE h) x hx s

private theorem exists_pair (x : X) (a b : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s t : Γ(K, U)),
      K.presheaf.germ U x hx s = a ∧ K.presheaf.germ U x hx t = b := by
  obtain ⟨V, hxV, s, hs⟩ := K.presheaf.exists_germ_eq a
  obtain ⟨U, hUV, hxU, t, ht⟩ := K.presheaf.exists_le_germ_eq b hxV
  exact ⟨U, hxU, restrict K hUV s, t, (germ_restrict K hUV x hxU s).trans hs, ht⟩

private theorem exists_triple (x : X) (a b c : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s t v : Γ(K, U)),
      K.presheaf.germ U x hx s = a ∧ K.presheaf.germ U x hx t = b ∧
        K.presheaf.germ U x hx v = c := by
  obtain ⟨V, hxV, s, t, hs, ht⟩ := exists_pair K x a b
  obtain ⟨U, hUV, hxU, v, hv⟩ := K.presheaf.exists_le_germ_eq c hxV
  exact ⟨U, hxU, restrict K hUV s, restrict K hUV t, v,
    (germ_restrict K hUV x hxU s).trans hs,
    (germ_restrict K hUV x hxU t).trans ht, hv⟩

private theorem exists_scalar_pair (x : X) (r : X.presheaf.stalk x)
    (a b : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (c : Γ(X, U)) (s t : Γ(K, U)),
      X.presheaf.germ U x hx c = r ∧ K.presheaf.germ U x hx s = a ∧
        K.presheaf.germ U x hx t = b := by
  obtain ⟨V, hxV, s, t, hs, ht⟩ := exists_pair K x a b
  obtain ⟨U, hUV, hxU, c, hc⟩ := X.presheaf.exists_le_germ_eq r hxV
  exact ⟨U, hxU, c, restrict K hUV s, restrict K hUV t, hc,
    (germ_restrict K hUV x hxU s).trans hs,
    (germ_restrict K hUV x hxU t).trans ht⟩

variable
  (B : ∀ U : X.Opens, Γ(K, U) →ₗ[Γ(X, U)] Γ(K, U) →ₗ[Γ(X, U)] Γ(K, U))
  (hB : ∀ (U V : X.Opens) (h : U ≤ V) (s t : Γ(K, V)),
    K.presheaf.map (homOfLE h).op (B V s t) =
      B U (K.presheaf.map (homOfLE h).op s) (K.presheaf.map (homOfLE h).op t))

include hB in
private theorem germ_independent (x : X) {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (s t : Γ(K, U)) (s' t' : Γ(K, V))
    (hs : K.presheaf.germ U x hxU s = K.presheaf.germ V x hxV s')
    (ht : K.presheaf.germ U x hxU t = K.presheaf.germ V x hxV t') :
    K.presheaf.germ U x hxU (B U s t) = K.presheaf.germ V x hxV (B V s' t') := by
  obtain ⟨W, hxW, i, j, he⟩ := K.presheaf.germ_eq x hxU hxV s s' hs
  change restrict K i.le s = restrict K j.le s' at he
  have htW : K.presheaf.germ W x hxW (restrict K i.le t) =
      K.presheaf.germ W x hxW (restrict K j.le t') := by
    simpa only [germ_restrict] using ht
  obtain ⟨T, hxT, k, l, hf⟩ := K.presheaf.germ_eq x hxW hxW _ _ htW
  change restrict K k.le (restrict K i.le t) =
    restrict K l.le (restrict K j.le t') at hf
  have hfirst : restrict K (k.le.trans i.le) s = restrict K (l.le.trans j.le) s' := by
    simpa only [restrict_comp] using congrArg (restrict K k.le) he
  have hsecond : restrict K (k.le.trans i.le) t = restrict K (l.le.trans j.le) t' := by
    simpa only [restrict_comp] using hf
  rw [← germ_restrict K (k.le.trans i.le) x hxT (B U s t),
    ← germ_restrict K (l.le.trans j.le) x hxT (B V s' t')]
  dsimp only [restrict] at hfirst hsecond ⊢
  rw [hB, hB, hfirst, hsecond]

include hB in
private theorem exists_value (x : X) (a b : K.presheaf.stalk x) :
    ∃ z : K.presheaf.stalk x, ∀ (U : X.Opens) (hx : x ∈ U) (s t : Γ(K, U)),
      K.presheaf.germ U x hx s = a → K.presheaf.germ U x hx t = b →
        z = K.presheaf.germ U x hx (B U s t) := by
  obtain ⟨V, hxV, s', t', hs', ht'⟩ := exists_pair K x a b
  refine ⟨K.presheaf.germ V x hxV (B V s' t'), ?_⟩
  intro U hx s t hs ht
  exact germ_independent K B hB x hxV hx s' t' s t (hs'.trans hs.symm) (ht'.trans ht.symm)

private def stalkOperation (x : X) (a b : K.presheaf.stalk x) : K.presheaf.stalk x :=
  Classical.choose (exists_value K B hB x a b)

private theorem stalkOperation_germ (x : X) (U : X.Opens) (hx : x ∈ U) (s t : Γ(K, U)) :
    stalkOperation K B hB x (K.presheaf.germ U x hx s) (K.presheaf.germ U x hx t) =
      K.presheaf.germ U x hx (B U s t) :=
  Classical.choose_spec (exists_value K B hB x _ _) U hx s t rfl rfl

private theorem stalkOperation_add_left (x : X) (a b c : K.presheaf.stalk x) :
    stalkOperation K B hB x (a + b) c =
      stalkOperation K B hB x a c + stalkOperation K B hB x b c := by
  obtain ⟨U, hx, s, t, v, rfl, rfl, rfl⟩ := exists_triple K x a b c
  rw [← map_add, stalkOperation_germ, stalkOperation_germ, stalkOperation_germ,
    map_add, LinearMap.add_apply, map_add]

private theorem stalkOperation_add_right (x : X) (a b c : K.presheaf.stalk x) :
    stalkOperation K B hB x a (b + c) =
      stalkOperation K B hB x a b + stalkOperation K B hB x a c := by
  obtain ⟨U, hx, s, t, v, rfl, rfl, rfl⟩ := exists_triple K x a b c
  rw [← map_add, stalkOperation_germ, stalkOperation_germ, stalkOperation_germ,
    map_add, map_add]

private theorem stalkOperation_smul_left (x : X) (r : X.presheaf.stalk x)
    (a b : K.presheaf.stalk x) :
    stalkOperation K B hB x (r • a) b = r • stalkOperation K B hB x a b := by
  obtain ⟨U, hx, c, s, t, rfl, rfl, rfl⟩ := exists_scalar_pair K x r a b
  rw [← schemeModule_germ_smul, stalkOperation_germ, stalkOperation_germ,
    map_smul, LinearMap.smul_apply, schemeModule_germ_smul]

private theorem stalkOperation_smul_right (x : X) (r : X.presheaf.stalk x)
    (a b : K.presheaf.stalk x) :
    stalkOperation K B hB x a (r • b) = r • stalkOperation K B hB x a b := by
  obtain ⟨U, hx, c, s, t, rfl, rfl, rfl⟩ := exists_scalar_pair K x r a b
  rw [← schemeModule_germ_smul, stalkOperation_germ, stalkOperation_germ,
    map_smul, schemeModule_germ_smul]

/-- A natural bilinear section operation induces a bilinear operation on the
actual scheme-module stalk, without any additional stalk operation as input. -/
def schemeModuleStalkBilinear (x : X) :
    K.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      K.presheaf.stalk x →ₗ[X.presheaf.stalk x] K.presheaf.stalk x where
  toFun a :=
    { toFun := stalkOperation K B hB x a
      map_add' := stalkOperation_add_right K B hB x a
      map_smul' := fun r b => stalkOperation_smul_right K B hB x r a b }
  map_add' a b := by
    ext c
    exact stalkOperation_add_left K B hB x a b c
  map_smul' r a := by
    ext b
    exact stalkOperation_smul_left K B hB x r a b

/-- The stalk operation evaluated on two germs is the germ of the section operation. -/
theorem schemeModuleStalkBilinear_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (s t : Γ(K, U)) :
    schemeModuleStalkBilinear K B hB x
      (K.presheaf.germ U x hx s) (K.presheaf.germ U x hx t) =
        K.presheaf.germ U x hx (B U s t) :=
  stalkOperation_germ K B hB x U hx s t

/-- The germ formula determines the induced bilinear stalk operation uniquely. -/
theorem schemeModuleStalkBilinear_unique (x : X)
    (T : K.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      K.presheaf.stalk x →ₗ[X.presheaf.stalk x] K.presheaf.stalk x)
    (hT : ∀ (U : X.Opens) (hx : x ∈ U) (s t : Γ(K, U)),
      T (K.presheaf.germ U x hx s) (K.presheaf.germ U x hx t) =
        K.presheaf.germ U x hx (B U s t)) :
    T = schemeModuleStalkBilinear K B hB x := by
  ext a b
  obtain ⟨U, hx, s, t, rfl, rfl⟩ := exists_pair K x a b
  rw [hT, schemeModuleStalkBilinear_germ]

/-- An alternating section operation remains alternating on the actual stalk. -/
theorem schemeModuleStalkBilinear_self_eq_zero
    (halt : ∀ (U : X.Opens) (s : Γ(K, U)), B U s s = 0)
    (x : X) (a : K.presheaf.stalk x) :
    schemeModuleStalkBilinear K B hB x a a = 0 := by
  obtain ⟨U, hx, s, rfl⟩ := K.presheaf.exists_germ_eq a
  rw [schemeModuleStalkBilinear_germ, halt, map_zero]

/-- The Jacobi identity in derivation form descends from sections to the
actual stalk. Together with alternation this supplies the Lie identities. -/
theorem schemeModuleStalkBilinear_leibniz
    (hJac : ∀ (U : X.Opens) (s t v : Γ(K, U)),
      B U s (B U t v) = B U (B U s t) v + B U t (B U s v))
    (x : X) (a b c : K.presheaf.stalk x) :
    schemeModuleStalkBilinear K B hB x a (schemeModuleStalkBilinear K B hB x b c) =
      schemeModuleStalkBilinear K B hB x (schemeModuleStalkBilinear K B hB x a b) c +
        schemeModuleStalkBilinear K B hB x b (schemeModuleStalkBilinear K B hB x a c) := by
  obtain ⟨U, hx, s, t, v, rfl, rfl, rfl⟩ := exists_triple K x a b c
  simp only [schemeModuleStalkBilinear_germ]
  rw [hJac, map_add]

private def unitStalkAddEquiv (x : X) :
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x ≃+
      X.presheaf.stalk x :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf)).symm.addCommGroupIsoToAddEquiv

private theorem unitStalkAddEquiv_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) :
    unitStalkAddEquiv x
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx r) =
        X.presheaf.germ U x hx r := by
  exact congrArg (fun f => f r)
    (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩))

/-- The stalk of the unit module sheaf is the actual structure-sheaf local
ring, as a module over that same local ring. -/
def schemeUnitStalkEquiv (x : X) :
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  __ := unitStalkAddEquiv x
  map_smul' r a := by
    let J : X.Modules := SheafOfModules.unit X.ringCatSheaf
    change unitStalkAddEquiv x (r • a) = r * unitStalkAddEquiv x a
    obtain ⟨U, hx, c, s, _, hc, hs, _⟩ := exists_scalar_pair J x r a a
    change Γ(X, U) at s
    rw [← hc, ← hs, ← schemeModule_germ_smul]
    change unitStalkAddEquiv x
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx
        (c * (s : Γ(X, U)))) =
      X.presheaf.germ U x hx c * unitStalkAddEquiv x
        ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx s)
    rw [unitStalkAddEquiv_germ, unitStalkAddEquiv_germ]
    exact (X.presheaf.germ U x hx).hom.map_mul c s

/-- The canonical identification of unit stalks sends each germ to the
structure-sheaf germ of the same scalar section. -/
theorem schemeUnitStalkEquiv_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) :
    schemeUnitStalkEquiv x
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx r) =
        X.presheaf.germ U x hx r :=
  unitStalkAddEquiv_germ x U hx r

/-- An actual sheaf character induces a local-ring linear functional on
the actual module stalk. -/
def schemeModuleStalkCharacter (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    K.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (schemeUnitStalkEquiv x).toLinearMap.comp (schemeModuleStalkMap χ x)

/-- Stalk characters agree with the germs of the original sheaf character. -/
theorem schemeModuleStalkCharacter_germ (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : X) (U : X.Opens) (hx : x ∈ U) (s : Γ(K, U)) :
    schemeModuleStalkCharacter K χ x (K.presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (χ.app U s) := by
  change schemeUnitStalkEquiv x (schemeModuleStalkMap χ x _) = _
  rw [schemeModuleStalkMap_germ, schemeUnitStalkEquiv_germ]

end Normalizer
