import Normalizer.ExteriorLineTrivialization
import Normalizer.TrivialBundleStalk

/-! Genuine local bundle trivializations construct bases of actual stalks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} {E H : X.Modules} {U : X.Opens}

private abbrev localMap (f : E.over U ⟶ H.over U) (V : X.Opens) (h : V ≤ U) :
    Γ(E, V) →ₗ[Γ(X, V)] Γ(H, V) :=
  (f.val.app (op (Over.mk (homOfLE h)))).hom

private theorem localMap_restrict (f : E.over U ⟶ H.over U) {V W : X.Opens}
    (h : W ≤ V) (k : V ≤ U) (s : Γ(E, V)) :
    H.presheaf.map (homOfLE h).op (localMap f V k s) =
      localMap f W (h.trans k) (E.presheaf.map (homOfLE h).op s) := by
  let i : Over.mk (homOfLE (h.trans k)) ⟶ Over.mk (homOfLE k) := Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply f.val i.op s).symm

private def localStalkCocone (f : E.over U ⟶ H.over U) (x : X) (hxU : x ∈ U) :
    Cocone ((OpenNhds.inclusion x).op ⋙ E.presheaf) where
  pt := H.presheaf.stalk x
  ι :=
    { app := fun V => AddCommGrpCat.ofHom
        ((H.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hxU⟩).hom.comp
          ((localMap f (V.unop.1 ⊓ U) inf_le_right).toAddMonoidHom.comp
            (E.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op).hom))
      naturality := by
        intro V W i
        ext s
        let h : W.unop.1 ≤ V.unop.1 := i.unop.le
        let q : W.unop.1 ⊓ U ≤ V.unop.1 ⊓ U := inf_le_inf_right U h
        change H.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hxU⟩
            (localMap f _ inf_le_right
              (E.presheaf.map (homOfLE inf_le_left).op
                (E.presheaf.map (homOfLE h).op s))) =
          H.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hxU⟩
            (localMap f _ inf_le_right (E.presheaf.map (homOfLE inf_le_left).op s))
        rw [← H.presheaf.germ_res_apply (homOfLE q) x ⟨W.unop.2, hxU⟩,
          localMap_restrict]
        congr 2
        exact (E.val.map_comp_apply (homOfLE h).op (homOfLE inf_le_left).op s).symm.trans
          (E.val.map_comp_apply (homOfLE inf_le_left).op (homOfLE q).op s) }

private def localStalkAddMap (f : E.over U ⟶ H.over U) (x : X) (hxU : x ∈ U) :
    E.presheaf.stalk x →+ H.presheaf.stalk x :=
  (colimit.desc _ (localStalkCocone f x hxU)).hom

private theorem localStalkAddMap_germ (f : E.over U ⟶ H.over U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (h : V ≤ U) (hx : x ∈ V) (s : Γ(E, V)) :
    localStalkAddMap f x hxU (E.presheaf.germ V x hx s) =
      H.presheaf.germ V x hx (localMap f V h s) := by
  have hc := ConcreteCategory.congr_hom (colimit.ι_desc (localStalkCocone f x hxU)
    (op ⟨V, hx⟩)) s
  change localStalkAddMap f x hxU (E.presheaf.germ V x hx s) =
    H.presheaf.germ (V ⊓ U) x ⟨hx, hxU⟩
      (localMap f (V ⊓ U) inf_le_right (E.presheaf.map (homOfLE inf_le_left).op s)) at hc
  rw [hc]
  have hn := localMap_restrict f (show V ⊓ U ≤ V from inf_le_left) h s
  rw [← hn, H.presheaf.germ_res_apply]

/-- A morphism defined on a neighbourhood induces an actual local-ring
linear map on the ambient scheme's stalks. -/
def schemeLocalStalkMap (f : E.over U ⟶ H.over U) (x : X) (hxU : x ∈ U) :
    E.presheaf.stalk x →ₗ[X.presheaf.stalk x] H.presheaf.stalk x where
  __ := localStalkAddMap f x hxU
  map_smul' r a := by
    change localStalkAddMap f x hxU (r • a) = r • localStalkAddMap f x hxU a
    obtain ⟨V, hVU, hxV, c, rfl⟩ := X.presheaf.exists_le_germ_eq r hxU
    obtain ⟨W, hWV, hxW, s, rfl⟩ := E.presheaf.exists_le_germ_eq a hxV
    rw [← X.presheaf.germ_res_apply (homOfLE hWV) x hxW c, ← schemeModule_germ_smul,
      localStalkAddMap_germ f x hxU W (hWV.trans hVU),
      localStalkAddMap_germ f x hxU W (hWV.trans hVU), map_smul, schemeModule_germ_smul]

/-- The local stalk map has the actual section-map germ formula. -/
theorem schemeLocalStalkMap_germ (f : E.over U ⟶ H.over U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (h : V ≤ U) (hx : x ∈ V) (s : Γ(E, V)) :
    schemeLocalStalkMap f x hxU (E.presheaf.germ V x hx s) =
      H.presheaf.germ V x hx (f.val.app (op (Over.mk (homOfLE h))) s) :=
  localStalkAddMap_germ f x hxU V h hx s

/-- An actual sheaf isomorphism on a neighbourhood induces an equivalence
of the original scheme's module stalks over the original local ring. -/
def schemeLocalStalkEquiv (eU : E.over U ≅ H.over U) (x : X) (hxU : x ∈ U) :
    E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] H.presheaf.stalk x where
  __ := schemeLocalStalkMap eU.hom x hxU
  invFun := schemeLocalStalkMap eU.inv x hxU
  left_inv a := by
    change schemeLocalStalkMap eU.inv x hxU (schemeLocalStalkMap eU.hom x hxU a) = a
    obtain ⟨V, hVU, hxV, s, rfl⟩ := E.presheaf.exists_le_germ_eq a hxU
    rw [schemeLocalStalkMap_germ _ x hxU V hVU,
      schemeLocalStalkMap_germ _ x hxU V hVU]
    exact congrArg (E.presheaf.germ V x hxV)
      (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE hVU)))).mapIso eU).toLinearEquiv.symm_apply_apply s)
  right_inv a := by
    change schemeLocalStalkMap eU.hom x hxU (schemeLocalStalkMap eU.inv x hxU a) = a
    obtain ⟨V, hVU, hxV, s, rfl⟩ := H.presheaf.exists_le_germ_eq a hxU
    rw [schemeLocalStalkMap_germ _ x hxU V hVU,
      schemeLocalStalkMap_germ _ x hxU V hVU]
    exact congrArg (H.presheaf.germ V x hxV)
      (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE hVU)))).mapIso eU).toLinearEquiv.apply_symm_apply s)

/-- The local stalk equivalence sends actual germs to the germs of the
given local sheaf isomorphism, on every smaller neighbourhood. -/
theorem schemeLocalStalkEquiv_germ (eU : E.over U ≅ H.over U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (h : V ≤ U) (hx : x ∈ V) (s : Γ(E, V)) :
    schemeLocalStalkEquiv eU x hxU (E.presheaf.germ V x hx s) =
      H.presheaf.germ V x hx (eU.hom.val.app (op (Over.mk (homOfLE h))) s) :=
  schemeLocalStalkMap_germ eU.hom x hxU V h hx s

variable {I : Type u} [Fintype I] {n : ℕ} (j : I ≃ Fin n)
  (eU : (schemeTrivialBundle X I).over U ≅ H.over U) (x : X) (hxU : x ∈ U)

/-- A genuine local bundle trivialization supplies a basis of the actual
stalk. Both its spanning and independence come from the local isomorphism. -/
def schemeLocalFrameStalkBasis :
    Module.Basis (Fin n) (X.presheaf.stalk x) (H.presheaf.stalk x) := by
  classical
  exact ((Pi.basisFun (X.presheaf.stalk x) I).map
    ((schemeTrivialStalkEquiv X I x).trans (schemeLocalStalkEquiv eU x hxU))).reindex j

/-- The constructed stalk basis consists of the actual germs of the local frame. -/
theorem schemeLocalFrameStalkBasis_apply (i : Fin n) :
    schemeLocalFrameStalkBasis j eU x hxU i =
      H.presheaf.germ U x hxU (bundleLocalFrameBasis j eU U le_rfl i) := by
  classical
  rw [schemeLocalFrameStalkBasis, Module.Basis.coe_reindex]
  change schemeLocalStalkEquiv eU x hxU
    (schemeTrivialStalkEquiv X I x ((Pi.basisFun (X.presheaf.stalk x) I) (j.symm i))) = _
  have ht : schemeTrivialStalkEquiv X I x
      ((Pi.basisFun (X.presheaf.stalk x) I) (j.symm i)) =
        (schemeTrivialBundle X I).presheaf.germ U x hxU
          (schemeTrivialSection X I U (j.symm i)) := by
    change (∑ k, (Pi.basisFun (X.presheaf.stalk x) I (j.symm i)) k •
      (schemeTrivialBundle X I).presheaf.germ ⊤ x trivial
        (schemeTrivialSection X I ⊤ k)) = _
    simp only [Pi.basisFun_apply, Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hr := schemeTrivialSection_restrict X I (show U ≤ ⊤ from le_top) (j.symm i)
    exact ((congrArg ((schemeTrivialBundle X I).presheaf.germ U x hxU) hr).symm.trans
      ((schemeTrivialBundle X I).presheaf.germ_res_apply (homOfLE le_top) x hxU _)).symm
  rw [ht, schemeLocalStalkEquiv_germ _ x hxU U le_rfl, bundleLocalFrameBasis_apply]

/-- On any smaller neighbourhood, the same actual stalk basis is given
by the germs of the compatible restricted frame. -/
theorem schemeLocalFrameStalkBasis_germ (V : X.Opens) (h : V ≤ U) (hxV : x ∈ V)
    (i : Fin n) :
    schemeLocalFrameStalkBasis j eU x hxU i =
      H.presheaf.germ V x hxV (bundleLocalFrameBasis j eU V h i) := by
  rw [schemeLocalFrameStalkBasis_apply]
  have hr := bundleLocalFrameBasis_restrict j eU h le_rfl i
  exact ((congrArg (H.presheaf.germ V x hxV) hr).symm.trans
    (H.presheaf.germ_res_apply (homOfLE h) x hxV _)).symm

/-- Stalk coordinates of an actual section germ are the germs of its
coordinates in the compatible local frame. -/
theorem schemeLocalFrameStalkBasis_repr_germ (V : X.Opens) (h : V ≤ U) (hxV : x ∈ V)
    (s : Γ(H, V)) (i : Fin n) :
    (schemeLocalFrameStalkBasis j eU x hxU).repr (H.presheaf.germ V x hxV s) i =
      X.presheaf.germ V x hxV ((bundleLocalFrameBasis j eU V h).repr s i) := by
  have hs : H.presheaf.germ V x hxV s =
      ∑ k, X.presheaf.germ V x hxV ((bundleLocalFrameBasis j eU V h).repr s k) •
        schemeLocalFrameStalkBasis j eU x hxU k := by
    conv_lhs => rw [← (bundleLocalFrameBasis j eU V h).sum_repr s]
    rw [map_sum]
    simp_rw [schemeModule_germ_smul, ← schemeLocalFrameStalkBasis_germ j eU x hxU V h hxV]
  rw [hs]
  simp [Finsupp.single_apply]

end Normalizer
