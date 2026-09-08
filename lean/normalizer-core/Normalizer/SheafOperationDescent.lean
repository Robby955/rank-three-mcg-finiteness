import Normalizer.LocalCharacterGluing
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! Descending a binary operation through a locally surjective morphism of
actual module sheaves. No surjectivity on sections of a fixed open is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {A B : SheafOfModules.{u} R} (q : A ⟶ B)

private abbrev res (M : SheafOfModules.{u} R) {V W : Opens X} (h : V ≤ W) :=
  M.val.restrictₛₗ (homOfLE h).op

private theorem res_comp (M : SheafOfModules.{u} R) {V W T : Opens X}
    (h : V ≤ W) (k : W ≤ T) (s : M.val.obj (op T)) :
    res M h (res M k s) = res M (h.trans k) s :=
  (M.val.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

private theorem q_res {V W : Opens X} (h : V ≤ W) (s : A.val.obj (op W)) :
    q.val.app (op V) (res A h s) = res B h (q.val.app (op W) s) :=
  by
  exact congrArg (fun f => f s) (q.val.naturality (homOfLE h).op)

private def liftPatch (V : Opens X) (x y : B.val.obj (op V)) :=
  Σ' W : Opens X, Σ' h : W ≤ V,
    {p : A.val.obj (op W) × A.val.obj (op W) //
      q.val.app (op W) p.1 = res B h x ∧ q.val.app (op W) p.2 = res B h y}

variable (hq : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map q))

include hq in
private theorem liftPatch_cover (V : Opens X) (x y : B.val.obj (op V)) :
    V ≤ iSup (fun p : liftPatch q V x y => p.1) := by
  let f := ((SheafOfModules.toSheaf R).map q).hom
  have hx := hq.imageSieve_mem x
  have hy := hq.imageSieve_mem y
  have hc := (Opens.grothendieckTopology X).intersection_covering hx hy
  intro t ht
  obtain ⟨W, g, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, htW⟩ := hc t ht
  exact (le_iSup (fun p : liftPatch q V x y => p.1)
    ⟨W, g.le, ⟨(a, b), ha, hb⟩⟩) htW

private def tripleLiftPatch (V : Opens X) (x y z : B.val.obj (op V)) :=
  Σ' W : Opens X, Σ' h : W ≤ V,
    {p : A.val.obj (op W) × A.val.obj (op W) × A.val.obj (op W) //
      q.val.app (op W) p.1 = res B h x ∧
      q.val.app (op W) p.2.1 = res B h y ∧ q.val.app (op W) p.2.2 = res B h z}

include hq in
private theorem tripleLiftPatch_cover (V : Opens X) (x y z : B.val.obj (op V)) :
    V ≤ iSup (fun p : tripleLiftPatch q V x y z => p.1) := by
  have hc := (Opens.grothendieckTopology X).intersection_covering
    (hq.imageSieve_mem x) ((Opens.grothendieckTopology X).intersection_covering
      (hq.imageSieve_mem y) (hq.imageSieve_mem z))
  intro t ht
  obtain ⟨W, g, ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, htW⟩ := hc t ht
  exact (le_iSup (fun p : tripleLiftPatch q V x y z => p.1)
    ⟨W, g.le, ⟨(a, b, c), ha, hb, hc⟩⟩) htW

include hq in
/-- Equality of sections of any target module sheaf can be checked on
simultaneous local lifts of three sections along a locally surjective map.
The covering family of lifts is constructed from the three image sieves. -/
theorem sheaf_eq_of_local_lifts (T : SheafOfModules.{u} R) (V : Opens X)
    (x y z : B.val.obj (op V)) (s t : T.val.obj (op V))
    (hlocal : ∀ (W : Opens X) (h : W ≤ V) (a b c : A.val.obj (op W)),
      q.val.app (op W) a = res B h x → q.val.app (op W) b = res B h y →
      q.val.app (op W) c = res B h z → res T h s = res T h t) : s = t := by
  let TS : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨T.val.presheaf, T.isSheaf⟩
  apply TS.eq_of_locally_eq' (fun p : tripleLiftPatch q V x y z => p.1) V
    (fun p => homOfLE p.2.1) (tripleLiftPatch_cover q hq V x y z)
  intro p
  exact hlocal p.1 p.2.1 p.2.2.val.1 p.2.2.val.2.1 p.2.2.val.2.2
    p.2.2.property.1 p.2.2.property.2.1 p.2.2.property.2.2

variable
  (operation : ∀ V, A.val.obj (op V) → A.val.obj (op V) → B.val.obj (op V))
  (operation_res : ∀ (V W : Opens X) (h : V ≤ W) (a b : A.val.obj (op W)),
    res B h (operation W a b) = operation V (res A h a) (res A h b))
  (operation_independent : ∀ V (a a' b b' : A.val.obj (op V)),
    q.val.app (op V) a = q.val.app (op V) a' →
    q.val.app (op V) b = q.val.app (op V) b' →
    operation V a b = operation V a' b')

private def targetSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨B.val.presheaf, B.isSheaf⟩

include operation_res operation_independent in
private theorem liftPatch_compatible (V : Opens X) (x y : B.val.obj (op V)) :
    TopCat.Presheaf.IsCompatible (targetSheaf (B := B)).obj
      (fun p : liftPatch q V x y => p.1)
      (fun p => operation p.1 p.2.2.val.1 p.2.2.val.2) := by
  intro p r
  change res B inf_le_left (operation p.1 p.2.2.val.1 p.2.2.val.2) =
    res B inf_le_right (operation r.1 r.2.2.val.1 r.2.2.val.2)
  refine (operation_res (p.1 ⊓ r.1) p.1 inf_le_left _ _).trans
    (Eq.trans ?_ (operation_res (p.1 ⊓ r.1) r.1 inf_le_right _ _).symm)
  apply operation_independent (p.1 ⊓ r.1)
  · calc
      _ = res B inf_le_left (q.val.app _ p.2.2.val.1) := q_res q inf_le_left _
      _ = res B inf_le_left (res B p.2.1 x) := congrArg (res B inf_le_left) p.2.2.property.1
      _ = res B (inf_le_left.trans p.2.1) x := res_comp B _ _ x
      _ = res B (inf_le_right.trans r.2.1) x := rfl
      _ = res B inf_le_right (res B r.2.1 x) := (res_comp B _ _ x).symm
      _ = res B inf_le_right (q.val.app _ r.2.2.val.1) :=
        congrArg (res B inf_le_right) r.2.2.property.1.symm
      _ = _ := (q_res q inf_le_right _).symm
  · calc
      _ = res B inf_le_left (q.val.app _ p.2.2.val.2) := q_res q inf_le_left _
      _ = res B inf_le_left (res B p.2.1 y) := congrArg (res B inf_le_left) p.2.2.property.2
      _ = res B (inf_le_left.trans p.2.1) y := res_comp B _ _ y
      _ = res B (inf_le_right.trans r.2.1) y := rfl
      _ = res B inf_le_right (res B r.2.1 y) := (res_comp B _ _ y).symm
      _ = res B inf_le_right (q.val.app _ r.2.2.val.2) :=
        congrArg (res B inf_le_right) r.2.2.property.2.symm
      _ = _ := (q_res q inf_le_right _).symm

/-- Glue a natural operation on representatives which is constant on the
fibres of a locally surjective map of actual module sheaves. -/
def descendSheafOperation (V : Opens X) (x y : B.val.obj (op V)) : B.val.obj (op V) :=
  Classical.choose ((targetSheaf (B := B)).existsUnique_gluing'
    (fun p : liftPatch q V x y => p.1) V (fun p => homOfLE p.2.1)
    (liftPatch_cover q hq V x y)
    (fun p => operation p.1 p.2.2.val.1 p.2.2.val.2)
    (liftPatch_compatible q operation operation_res operation_independent V x y))

/-- On every open admitting two representatives, the descended operation
is exactly the original operation on those representatives. -/
theorem descendSheafOperation_local (V W : Opens X) (h : W ≤ V)
    (x y : B.val.obj (op V)) (a b : A.val.obj (op W))
    (ha : q.val.app (op W) a = res B h x)
    (hb : q.val.app (op W) b = res B h y) :
    res B h (descendSheafOperation q hq operation operation_res operation_independent V x y) =
      operation W a b := by
  exact (Classical.choose_spec ((targetSheaf (B := B)).existsUnique_gluing'
    (fun p : liftPatch q V x y => p.1) V (fun p => homOfLE p.2.1)
    (liftPatch_cover q hq V x y)
    (fun p => operation p.1 p.2.2.val.1 p.2.2.val.2)
    (liftPatch_compatible q operation operation_res operation_independent V x y))).1
      ⟨W, h, ⟨(a, b), ha, hb⟩⟩

/-- The projection formula for the operation obtained by actual sheaf gluing. -/
theorem descendSheafOperation_projection (V : Opens X) (a b : A.val.obj (op V)) :
    descendSheafOperation q hq operation operation_res operation_independent V
      (q.val.app (op V) a) (q.val.app (op V) b) = operation V a b := by
  simpa [res] using descendSheafOperation_local q hq operation operation_res
    operation_independent V V le_rfl (q.val.app (op V) a) (q.val.app (op V) b)
    a b (by simp [res]) (by simp [res])

/-- The descended operation commutes with restrictions, also for sections
without representatives on the original open. -/
theorem descendSheafOperation_restrict (V W : Opens X) (h : W ≤ V)
    (x y : B.val.obj (op V)) :
    res B h (descendSheafOperation q hq operation operation_res operation_independent V x y) =
    descendSheafOperation q hq operation operation_res operation_independent W
      (res B h x) (res B h y) := by
  apply (targetSheaf (B := B)).eq_of_locally_eq'
    (fun p : liftPatch q W (res B h x) (res B h y) => p.1) W
    (fun p => homOfLE p.2.1) (liftPatch_cover q hq W (res B h x) (res B h y))
  intro p
  change res B p.2.1 (res B h _) = res B p.2.1 _
  refine (res_comp B p.2.1 h _).trans (Eq.trans ?_
    (descendSheafOperation_local q hq operation operation_res operation_independent
      W p.1 p.2.1 _ _ _ _ p.2.2.property.1 p.2.2.property.2).symm)
  exact descendSheafOperation_local q hq operation operation_res operation_independent
    V p.1 (p.2.1.trans h) x y p.2.2.val.1 p.2.2.val.2
    (p.2.2.property.1.trans (res_comp B p.2.1 h x))
    (p.2.2.property.2.trans (res_comp B p.2.1 h y))

/-- Local recovery on representatives uniquely determines the descended
section, even when the arguments have no representatives on the full open. -/
theorem descendSheafOperation_unique (V : Opens X) (x y z : B.val.obj (op V))
    (hz : ∀ (W : Opens X) (h : W ≤ V) (a b : A.val.obj (op W)),
      q.val.app (op W) a = res B h x → q.val.app (op W) b = res B h y →
      res B h z = operation W a b) :
    z = descendSheafOperation q hq operation operation_res operation_independent V x y := by
  apply (targetSheaf (B := B)).eq_of_locally_eq'
    (fun p : liftPatch q V x y => p.1) V (fun p => homOfLE p.2.1)
    (liftPatch_cover q hq V x y)
  intro p
  exact (hz p.1 p.2.1 _ _ p.2.2.property.1 p.2.2.property.2).trans
    (descendSheafOperation_local q hq operation operation_res operation_independent
      V p.1 p.2.1 x y _ _ p.2.2.property.1 p.2.2.property.2).symm

end Normalizer
