import Normalizer.SheafQuotientBracket
import Normalizer.KernelQuotient
import Normalizer.ModuleSheafHom

/-! The actual ambient quotient and the normalizer as a geometric kernel.
The ambient quotient is a sheaf cokernel. Exactness is used on sections;
surjectivity on the sections of a fixed open is not required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (E : SheafOfModules.{u} R) (I : E.Submodule)

/-- The ambient quotient by the given subsheaf, as an actual sheaf cokernel. -/
def ambientQuotientSheaf : SheafOfModules.{u} R := cokernel I.ι

/-- The actual projection to the ambient sheaf quotient. -/
def ambientQuotientProjection : E ⟶ ambientQuotientSheaf E I := cokernel.π I.ι

/-- The kernel on sections of the actual quotient projection is the original
subsheaf on that same open. -/
theorem ambientQuotient_zero_iff (V) (x : E.val.obj V) :
    (ambientQuotientProjection E I).val.app V x = 0 ↔ x ∈ I.obj V := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := sheaf_cokernel_section_exact I.ι V x hx
    exact ha ▸ a.property
  · intro hx
    exact congrArg (fun f => f.val.app V (⟨x, hx⟩ : I.toSheafOfModules.val.obj V))
      (cokernel.condition I.ι)

private def subsheafLift {A : SheafOfModules.{u} R} (N : E.Submodule)
    (f : A ⟶ E) (hf : ∀ V (x : A.val.obj V), f.val.app V x ∈ N.obj V) :
    A ⟶ N.toSheafOfModules where
  val := {
    app := fun V => ModuleCat.ofHom ((f.val.app V).hom.codRestrict (N.obj V) (hf V))
    naturality := by
      intro V W g
      ext x
      apply Subtype.ext
      exact PresheafOfModules.naturality_apply f.val g x }

private theorem subsheafLift_fac {A : SheafOfModules.{u} R} (N : E.Submodule)
    (f : A ⟶ E) (hf : ∀ V (x : A.val.obj V), f.val.app V x ∈ N.obj V) :
    subsheafLift E N f hf ≫ N.ι = f := by
  rfl

private theorem subsheaf_kernel_condition {H : SheafOfModules.{u} R}
    (N : E.Submodule) (b : E ⟶ H)
    (hb : ∀ V (x : E.val.obj V), b.val.app V x = 0 ↔ x ∈ N.obj V) :
    N.ι ≫ b = 0 := by
  apply SheafOfModules.Hom.ext
  ext V x
  exact (hb V x.val).mpr x.property

private def subsheafIsKernel {H : SheafOfModules.{u} R}
    (N : E.Submodule) (b : E ⟶ H)
    (hb : ∀ V (x : E.val.obj V), b.val.app V x = 0 ↔ x ∈ N.obj V) :
    IsLimit (KernelFork.ofι N.ι (subsheaf_kernel_condition E N b hb)) := by
  refine KernelFork.IsLimit.ofι' _ _ fun {A} f hf => ?_
  have hmem : ∀ V (x : A.val.obj V), f.val.app V x ∈ N.obj V := by
    intro V x
    apply (hb V _).mp
    exact congrArg (fun k => k.val.app V x) hf
  exact ⟨subsheafLift E N f hmem, subsheafLift_fac E N f hmem⟩

variable
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)

private def bracketLocalMap (V W : Opens X) (h : W ≤ V) (x : E.val.obj (op V)) :
    I.toSheafOfModules.val.obj (op W) →ₗ[R.obj.obj (op W)]
      (ambientQuotientSheaf E I).val.obj (op W) :=
  ((ambientQuotientProjection E I).val.app (op W)).hom.comp
    ((-(action (op W) (E.val.map (homOfLE h).op x))).comp (I.obj (op W)).subtype)

include skew in
private theorem bracketLocalMap_apply (V W : Opens X) (h : W ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op W)) :
    bracketLocalMap E I action V W h x m =
      (ambientQuotientProjection E I).val.app (op W)
        (action (op W) m.val (E.val.map (homOfLE h).op x)) := by
  change (ambientQuotientProjection E I).val.app (op W)
    (-action (op W) (E.val.map (homOfLE h).op x) m.val) = _
  rw [← skew]

include action_res skew in
private theorem bracketLocalMap_restrict (V W T : Opens X) (h : W ≤ T) (k : T ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op T)) :
    (ambientQuotientSheaf E I).val.map (homOfLE h).op
      (bracketLocalMap E I action V T k x m) =
    bracketLocalMap E I action V W (h.trans k) x
      (I.toSheafOfModules.val.map (homOfLE h).op m) := by
  rw [bracketLocalMap_apply E I action skew, bracketLocalMap_apply E I action skew,
    ← PresheafOfModules.naturality_apply, action_res, ← E.val.map_comp_apply]
  rfl

include skew in
private theorem local_bracket_zero_iff (V : Opens X) (x : E.val.obj (op V)) :
    (∀ (W : Opens X) (h : W ≤ V) (m : I.toSheafOfModules.val.obj (op W)),
      bracketLocalMap E I action V W h x m = 0) ↔
    x ∈ (normalizerSubsheaf E I action action_res).obj (op V) := by
  constructor
  · intro hz W f m hm
    apply (ambientQuotient_zero_iff E I W _).mp
    have h := hz W.unop f.unop.le ⟨m, hm⟩
    rw [bracketLocalMap_apply E I action skew] at h
    exact h
  · intro hx W h m
    rw [bracketLocalMap_apply E I action skew]
    exact (ambientQuotient_zero_iff E I (op W) _).mpr
      (hx (homOfLE h).op m.val m.property)

variable (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

private abbrev bracketTarget :=
  moduleHomSheaf I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm

private def bracketHomSection (V : Opens X) (x : E.val.obj (op V)) :
    (bracketTarget E I ring_comm).val.obj (op V) :=
  moduleHomMk I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm V
    (fun W h => bracketLocalMap E I action V W h x)
    (fun W Z h k m => bracketLocalMap_restrict E I action action_res skew V Z W k h x m)

private theorem bracketHomSection_eval (V W : Opens X) (h : W ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op W)) :
    moduleHomEval I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm V W h
      (bracketHomSection E I action action_res skew ring_comm V x) m =
      (ambientQuotientProjection E I).val.app (op W)
        (action (op W) m.val (E.val.map (homOfLE h).op x)) := by
  exact bracketLocalMap_apply E I action skew V W h x m

/-- Bracket with the subsheaf, followed by the actual ambient quotient.
The target is the genuine sheaf of local module morphisms. -/
def normalizerBracketMap : E ⟶ bracketTarget E I ring_comm where
  val := {
    app := fun V => ModuleCat.ofHom {
      toFun := bracketHomSection E I action action_res skew ring_comm V.unop
      map_add' := by
        intro x y
        apply moduleHom_ext
        intro W h m
        rw [moduleHomEval_add]
        simp only [LinearMap.add_apply, bracketHomSection_eval, map_add]
      map_smul' := by
        intro r x
        apply moduleHom_ext
        intro W h m
        rw [moduleHomEval_smul, bracketHomSection_eval, bracketHomSection_eval,
          E.val.map_smul, map_smul, map_smul]
        rfl }
    naturality := by
      intro V W f
      ext x
      apply moduleHom_ext
      intro T h m
      change moduleHomEval _ _ ring_comm W.unop T h
          (bracketHomSection E I action action_res skew ring_comm W.unop (E.val.map f x)) m =
        moduleHomEval _ _ ring_comm W.unop T h
          ((bracketTarget E I ring_comm).val.map f
            (bracketHomSection E I action action_res skew ring_comm V.unop x)) m
      rw [show f = (homOfLE f.unop.le).op from Subsingleton.elim _ _]
      rw [moduleHom_restrict I.toSheafOfModules (ambientQuotientSheaf E I)
          ring_comm V.unop W.unop T f.unop.le h,
        bracketHomSection_eval, bracketHomSection_eval,
        ← E.val.map_comp_apply]
      rfl }

/-- On every smaller open, the constructed action sends m to [x,m] modulo I. -/
theorem normalizerBracketMap_apply (V W : Opens X) (h : W ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op W)) :
    moduleHomEval I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm V W h
      ((normalizerBracketMap E I action action_res skew ring_comm).val.app (op V) x) m =
      (ambientQuotientProjection E I).val.app (op W)
        (action (op W) m.val (E.val.map (homOfLE h).op x)) :=
  bracketHomSection_eval E I action action_res skew ring_comm V W h x m

/-- The zero locus of the actual bracket map is exactly the already
constructed normalizer subsheaf, including every restriction test. -/
theorem normalizerBracketMap_zero_iff (V) (x : E.val.obj V) :
    (normalizerBracketMap E I action action_res skew ring_comm).val.app V x = 0 ↔
      x ∈ (normalizerSubsheaf E I action action_res).obj V := by
  rw [← local_bracket_zero_iff E I action action_res skew V.unop x]
  constructor
  · intro hx W h m
    have hh := congrArg (fun z => moduleHomEval I.toSheafOfModules
      (ambientQuotientSheaf E I) ring_comm V.unop W h z m) hx
    rw [normalizerBracketMap_apply, moduleHomEval_zero, LinearMap.zero_apply] at hh
    rw [bracketLocalMap_apply E I action skew]
    exact hh
  · intro hx
    apply moduleHom_ext
    intro W h m
    rw [normalizerBracketMap_apply, moduleHomEval_zero, LinearMap.zero_apply]
    have hm := hx W h m
    rw [bracketLocalMap_apply E I action skew] at hm
    exact hm

/-- The inclusion of the actual normalizer is killed by the bracket map. -/
theorem normalizerBracketMap_condition :
    (normalizerSubsheaf E I action action_res).ι ≫
      normalizerBracketMap E I action action_res skew ring_comm = 0 :=
  subsheaf_kernel_condition E (normalizerSubsheaf E I action action_res)
    (normalizerBracketMap E I action action_res skew ring_comm)
    (normalizerBracketMap_zero_iff E I action action_res skew ring_comm)

/-- The existing normalizer subsheaf satisfies the full universal property
of the kernel of the constructed bracket map. -/
def normalizerBracketIsKernel :
    IsLimit (KernelFork.ofι (normalizerSubsheaf E I action action_res).ι
      (normalizerBracketMap_condition E I action action_res skew ring_comm)) :=
  subsheafIsKernel E (normalizerSubsheaf E I action action_res)
    (normalizerBracketMap E I action action_res skew ring_comm)
    (normalizerBracketMap_zero_iff E I action action_res skew ring_comm)

variable (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
  action V m x = 0)

include habelian in
/-- Abelianness of the given subsheaf makes the actual bracket map kill it. -/
theorem normalizerBracketMap_kills_line :
    I.ι ≫ normalizerBracketMap E I action action_res skew ring_comm = 0 := by
  apply SheafOfModules.Hom.ext
  ext V m
  apply (normalizerBracketMap_zero_iff E I action action_res skew ring_comm V m.val).mpr
  exact abelian_subsheaf_le_normalizer E I action action_res habelian V m.property

/-- The bracket map induced on the actual ambient sheaf quotient. -/
def ambientQuotientBracketMap :
    ambientQuotientSheaf E I ⟶ bracketTarget E I ring_comm :=
  cokernel.desc I.ι (normalizerBracketMap E I action action_res skew ring_comm)
    (normalizerBracketMap_kills_line E I action action_res skew ring_comm habelian)

/-- The descended map agrees with the actual bracket before quotienting. -/
theorem ambientQuotientBracketMap_projection :
    ambientQuotientProjection E I ≫
      ambientQuotientBracketMap E I action action_res skew ring_comm habelian =
      normalizerBracketMap E I action action_res skew ring_comm :=
  cokernel.π_desc _ _ _

/-- Evaluation of the induced quotient map is the original projected
bracket; this fixes its sign and its action on every smaller open. -/
theorem ambientQuotientBracketMap_apply (V W : Opens X) (h : W ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op W)) :
    moduleHomEval I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm V W h
      ((ambientQuotientBracketMap E I action action_res skew ring_comm habelian).val.app
        (op V) ((ambientQuotientProjection E I).val.app (op V) x)) m =
      (ambientQuotientProjection E I).val.app (op W)
        (action (op W) m.val (E.val.map (homOfLE h).op x)) := by
  have hp := congrArg (fun f => f.val.app (op V) x)
    (ambientQuotientBracketMap_projection E I action action_res skew ring_comm habelian)
  change (ambientQuotientBracketMap E I action action_res skew ring_comm habelian).val.app
    (op V) ((ambientQuotientProjection E I).val.app (op V) x) =
      (normalizerBracketMap E I action action_res skew ring_comm).val.app (op V) x at hp
  rw [hp, normalizerBracketMap_apply]

private theorem normalizerLineInclusion_comp_ι :
    normalizerLineInclusion E I action action_res habelian ≫
      (normalizerSubsheaf E I action action_res).ι = I.ι := rfl

/-- The actual quotient normalizer is canonically the kernel of bracket
with the subsheaf on E/I. Neither the kernel nor the isomorphism is an input. -/
def normalizerQuotientKernelIso :
    normalizerQuotientSheaf E I action action_res habelian ≅
      kernel (ambientQuotientBracketMap E I action action_res skew ring_comm habelian) :=
  kernelQuotientIsoOfKernel I.ι
    (normalizerBracketMap E I action action_res skew ring_comm)
    (normalizerBracketMap_kills_line E I action action_res skew ring_comm habelian)
    (normalizerSubsheaf E I action action_res).ι
    (normalizerBracketMap_condition E I action action_res skew ring_comm)
    (normalizerBracketIsKernel E I action action_res skew ring_comm)
    (normalizerLineInclusion E I action action_res habelian)
    (normalizerLineInclusion_comp_ι E I action action_res habelian)

/-- The kernel isomorphism is compatible with the original inclusions and
actual cokernel projections. -/
theorem normalizerQuotientKernelIso_fac :
    cokernel.π (normalizerLineInclusion E I action action_res habelian) ≫
      (normalizerQuotientKernelIso E I action action_res skew ring_comm habelian).hom ≫
      kernel.ι (ambientQuotientBracketMap E I action action_res skew ring_comm habelian) =
      (normalizerSubsheaf E I action action_res).ι ≫ ambientQuotientProjection E I :=
  kernelQuotientIsoOfKernel_fac I.ι
    (normalizerBracketMap E I action action_res skew ring_comm)
    (normalizerBracketMap_kills_line E I action action_res skew ring_comm habelian)
    (normalizerSubsheaf E I action action_res).ι
    (normalizerBracketMap_condition E I action action_res skew ring_comm)
    (normalizerBracketIsKernel E I action action_res skew ring_comm)
    (normalizerLineInclusion E I action action_res habelian)
    (normalizerLineInclusion_comp_ι E I action action_res habelian)

private theorem normalizerToAmbient_zero :
    normalizerLineInclusion E I action action_res habelian ≫
      ((normalizerSubsheaf E I action action_res).ι ≫ ambientQuotientProjection E I) = 0 := by
  rw [← Category.assoc, normalizerLineInclusion_comp_ι]
  exact cokernel.condition I.ι

/-- The canonical map from the normalizer quotient into E/I, formed directly
by descending the original inclusion. -/
def normalizerQuotientToAmbient :
    normalizerQuotientSheaf E I action action_res habelian ⟶ ambientQuotientSheaf E I :=
  cokernel.desc (normalizerLineInclusion E I action action_res habelian)
    ((normalizerSubsheaf E I action action_res).ι ≫ ambientQuotientProjection E I)
    (normalizerToAmbient_zero E I action action_res habelian)

/-- The canonical ambient map recovers the original normalizer inclusion. -/
theorem normalizerQuotientToAmbient_projection :
    cokernel.π (normalizerLineInclusion E I action action_res habelian) ≫
      normalizerQuotientToAmbient E I action action_res habelian =
      (normalizerSubsheaf E I action action_res).ι ≫ ambientQuotientProjection E I :=
  cokernel.π_desc _ _ _

/-- The kernel inclusion under the isomorphism is the canonical descended
normalizer inclusion, rather than an unrelated map. -/
theorem normalizerQuotientKernelIso_hom_ι :
    (normalizerQuotientKernelIso E I action action_res skew ring_comm habelian).hom ≫
      kernel.ι (ambientQuotientBracketMap E I action action_res skew ring_comm habelian) =
      normalizerQuotientToAmbient E I action action_res habelian := by
  apply (cancel_epi (cokernel.π (normalizerLineInclusion E I action action_res habelian))).mp
  rw [normalizerQuotientKernelIso_fac, normalizerQuotientToAmbient_projection]

include skew ring_comm in
/-- The actual normalizer quotient embeds in the ambient quotient sheaf. -/
theorem normalizerQuotientToAmbient_mono :
    Mono (normalizerQuotientToAmbient E I action action_res habelian) := by
  rw [← normalizerQuotientKernelIso_hom_ι E I action action_res skew ring_comm habelian]
  infer_instance

end Normalizer
