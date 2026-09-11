import Normalizer.TwoAffineCohomology

/-! Actual section modules in the two-affine presentation of first cohomology.
All scalar actions and restriction maps come from the structure morphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 80000
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Abelian
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual module of sections on an open, with scalars from the base field. -/
@[instance_reducible]
def schemeOpenSectionsModule (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) :
    Module k Γ(F, U) := Module.compHom Γ(F, U) (schemeConstantAt p U)

/-- Degree-zero cohomology of an actual open is its actual section module,
with the base-field action on both sides proved compatible. -/
def schemeModuleOpenCohomologyEquiv₀ (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules) :
    letI := schemeModuleOpenCohomologyModule p U F 0
    letI := schemeOpenSectionsModule p U F
    ((schemeModulesToAbelianSheaves X).obj F).H' 0 U ≃ₗ[k] Γ(F, U) := by
  letI := schemeModuleOpenCohomologyModule p U F 0
  letI := schemeOpenSectionsModule p U F
  let A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (schemeModulesToAbelianSheaves X).obj F
  let e : ((schemeModulesToAbelianSheaves X).obj F).H' 0 U ≃ Γ(F, U) :=
    Ext.addEquiv₀.toEquiv.trans
    ((freeAbelianSheafEvaluation (Opens.grothendieckTopology X) U).homEquiv (Y := A))
  refine LinearEquiv.ofBijective
    { toFun := e, map_add' := ?_, map_smul' := ?_ } e.bijective
  · intro x y
    change (Ext.addEquiv₀ (x + y)).hom.app (op U) _ = _
    rw [map_add]
    rfl
  · intro a x
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    change (Ext.addEquiv₀ ((Ext.mk₀ b).comp
      (Ext.mk₀ (schemeModuleScalarEnd p F a)) (add_zero 0))).hom.app (op U) _ = _
    change _ = schemeConstantAt p U a •
      (show Γ(F, U) from (Ext.addEquiv₀ (Ext.mk₀ b)).hom.app (op U)
        ((toSheafify (Opens.grothendieckTopology X)
          (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
            (FreeAbelianGroup.of (𝟙 U))))
    rw [Ext.mk₀_comp_mk₀]
    simp only [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
    rfl

/-- The comparison evaluates the cohomology class on the actual identity generator. -/
theorem schemeModuleOpenCohomologyEquiv₀_apply
    (p : X ⟶ Spec (.of k)) (U : X.Opens) (F : X.Modules)
    (x : ((schemeModulesToAbelianSheaves X).obj F).H' 0 U) :
    schemeModuleOpenCohomologyEquiv₀ p U F x =
      (Ext.addEquiv₀ x).hom.app (op U)
        ((toSheafify (Opens.grothendieckTopology X)
          (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
            (FreeAbelianGroup.of (𝟙 U))) :=
  rfl

/-- The degree-zero comparison commutes with the actual open restriction map. -/
theorem schemeModuleOpenCohomologyEquiv₀_restrict
    (p : X ⟶ Spec (.of k)) {U V : X.Opens} (h : V ⟶ U) (F : X.Modules)
    (x : ((schemeModulesToAbelianSheaves X).obj F).H' 0 U) :
    schemeModuleOpenCohomologyEquiv₀ p V F
      ((((schemeModulesToAbelianSheaves X).obj F).cohomologyPresheaf 0).map h.op x) =
      F.val.map h.op (schemeModuleOpenCohomologyEquiv₀ p U F x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  rw [schemeModuleOpenCohomologyEquiv₀_apply, schemeModuleOpenCohomologyEquiv₀_apply]
  change (Ext.addEquiv₀ ((Ext.mk₀ _).comp (Ext.mk₀ a) (zero_add 0))).hom.app _ _ = _
  rw [Ext.mk₀_comp_mk₀]
  simp only [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  change a.hom.app (op V)
    (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free |>.map (yoneda.map h))).hom.app (op V)
      ((toSheafify (Opens.grothendieckTopology X)
        (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of (𝟙 V)))) = _
  have hn := congrArg (fun q => q.app (op V))
    (toSheafify_naturality (Opens.grothendieckTopology X)
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free |>.map (yoneda.map h)))
  have hn' := congrArg (fun q => q (FreeAbelianGroup.of (𝟙 V))) hn
  refine (congrArg (fun y => a.hom.app (op V) y) hn'.symm).trans ?_
  change a.hom.app (op V)
    ((toSheafify (Opens.grothendieckTopology X)
      (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of h)) = _
  have hg := congrArg (fun q => q (FreeAbelianGroup.of (𝟙 U)))
    ((toSheafify (Opens.grothendieckTopology X)
      (yoneda.obj U ⋙ AddCommGrpCat.free)).naturality h.op)
  have ha := congrArg (fun q => q
      ((toSheafify (Opens.grothendieckTopology X) (yoneda.obj U ⋙ AddCommGrpCat.free)).app
        (op U) (FreeAbelianGroup.of (𝟙 U)))) (a.hom.naturality h.op)
  exact (congrArg (fun y => a.hom.app (op V) y) hg).trans ha

variable (p : X ⟶ Spec (.of k)) (U V : X.Opens) (hUV : U ⊔ V = ⊤) (F : X.Modules)

/-- The actual section boundary on the overlap, with the original
Mayer-Vietoris connecting map and its structure-field action. -/
def twoOpenSectionδ :
    letI := schemeOpenSectionsModule p (U ⊓ V) F
    letI := schemeModuleCohomologyModule p F 1
    Γ(F, U ⊓ V) →ₗ[k] Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1 := by
  letI := schemeOpenSectionsModule p (U ⊓ V) F
  letI := schemeModuleOpenCohomologyModule p (U ⊓ V) F 0
  letI := schemeModuleCohomologyModule p F 1
  exact (twoOpenCohomologyδLinear U V hUV p F).comp
    (schemeModuleOpenCohomologyEquiv₀ p (U ⊓ V) F).symm.toLinearMap

/-- The actual section boundary is onto on a two-affine cover of a
quasicoherent sheaf; the local vanishing is derived. -/
theorem twoOpenSectionδ_surjective (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [F.IsQuasicoherent] : Function.Surjective (twoOpenSectionδ p U V hUV F) :=
  (quasicoherent_twoAffine_δ_surjective U V hUV hU hV F).comp
    (schemeModuleOpenCohomologyEquiv₀ p (U ⊓ V) F).symm.surjective

/-- A section on the overlap has zero boundary exactly when it is a
difference of actual sections restricted from the two opens. -/
theorem twoOpenSectionδ_eq_zero_iff (z : Γ(F, U ⊓ V)) :
    twoOpenSectionδ p U V hUV F z = 0 ↔
      ∃ s : Γ(F, U), ∃ t : Γ(F, V),
        F.val.map (homOfLE inf_le_left).op s -
          F.val.map (homOfLE inf_le_right).op t = z := by
  let A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (schemeModulesToAbelianSheaves X).obj F
  let S := twoOpenCoverSquare U V hUV
  let e := schemeModuleOpenCohomologyEquiv₀ p (U ⊓ V) F
  change twoOpenCohomologyδ U V hUV A (e.symm z) = 0 ↔ _
  rw [twoOpenCohomologyδ_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    let y' := (AddCommGrpCat.biprodIsoProd (A.H' 0 U) (A.H' 0 V)).hom y
    have hy' : S.fromBiprod A 0
        ((AddCommGrpCat.biprodIsoProd (A.H' 0 U) (A.H' 0 V)).inv y') = e.symm z := by
      exact (congrArg (fun w => S.fromBiprod A 0 w)
        (Iso.hom_inv_id_apply (AddCommGrpCat.biprodIsoProd _ _) y)).trans hy
    have hfrom := S.fromBiprod_biprodIsoProd_inv_apply A y'.1 y'.2
    have he := congrArg e (hfrom.symm.trans hy')
    change e (((A.cohomologyPresheaf 0).map (homOfLE inf_le_left).op) y'.1 -
      ((A.cohomologyPresheaf 0).map (homOfLE inf_le_right).op) y'.2) = e (e.symm z) at he
    rw [map_sub, LinearEquiv.apply_symm_apply] at he
    refine ⟨schemeModuleOpenCohomologyEquiv₀ p U F y'.1,
      schemeModuleOpenCohomologyEquiv₀ p V F y'.2, ?_⟩
    have hu := schemeModuleOpenCohomologyEquiv₀_restrict p
      (homOfLE inf_le_left : U ⊓ V ⟶ U) F y'.1
    have hv := schemeModuleOpenCohomologyEquiv₀_restrict p
      (homOfLE inf_le_right : U ⊓ V ⟶ V) F y'.2
    exact (congrArg₂ (· - ·) hu hv).symm.trans he
  · rintro ⟨s, t, hst⟩
    let u := (schemeModuleOpenCohomologyEquiv₀ p U F).symm s
    let v := (schemeModuleOpenCohomologyEquiv₀ p V F).symm t
    refine ⟨(AddCommGrpCat.biprodIsoProd (A.H' 0 U) (A.H' 0 V)).inv ⟨u, v⟩, ?_⟩
    apply (S.fromBiprod_biprodIsoProd_inv_apply A u v).trans
    apply e.injective
    change e (((A.cohomologyPresheaf 0).map (homOfLE inf_le_left).op) u -
      ((A.cohomologyPresheaf 0).map (homOfLE inf_le_right).op) v) = e (e.symm z)
    rw [map_sub, LinearEquiv.apply_symm_apply]
    have hu := schemeModuleOpenCohomologyEquiv₀_restrict p
      (homOfLE inf_le_left : U ⊓ V ⟶ U) F u
    have hv := schemeModuleOpenCohomologyEquiv₀_restrict p
      (homOfLE inf_le_right : U ⊓ V ⟶ V) F v
    exact (congrArg₂ (· - ·) hu hv).trans (by
      simpa only [u, v, LinearEquiv.apply_symm_apply] using hst)

/-- First cohomology is the quotient of actual overlap sections by the
kernel proved above to be precisely actual restriction differences. -/
def twoAffineSectionH1QuotientEquiv (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [F.IsQuasicoherent] :
    letI := schemeOpenSectionsModule p (U ⊓ V) F
    letI := schemeModuleCohomologyModule p F 1
    (Γ(F, U ⊓ V) ⧸ (twoOpenSectionδ p U V hUV F).ker) ≃ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1 := by
  letI := schemeOpenSectionsModule p (U ⊓ V) F
  letI := schemeModuleCohomologyModule p F 1
  exact (twoOpenSectionδ p U V hUV F).quotKerEquivOfSurjective
    (twoOpenSectionδ_surjective p U V hUV F hU hV)

end Normalizer
