import Normalizer.ModuleAbelianPushforward
import Normalizer.ProperGlobalCharacter
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! Base-field scalars on actual module-sheaf cohomology, induced by the
specified scheme structure morphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k))

/-- Constants on opens commute with actual restriction maps. -/
theorem schemeConstantAt_restrict {U V : X.Opens} (h : V ⟶ U) (a : k) :
    X.presheaf.map h.op (schemeConstantAt p U a) = schemeConstantAt p V a := by
  change X.presheaf.map h.op (X.presheaf.map _ (schemeConstantMap p a)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Multiplication by a base scalar is an actual endomorphism of the underlying
abelian sheaf, with scalars restricted from the structure morphism. -/
def schemeModuleScalarEnd (L : X.Modules) :
    k →+* End ((schemeModulesToAbelianSheaves X).obj L) where
  toFun a := ⟨{
    app := fun U => ModuleCat.smul (L.val.obj U) (schemeConstantAt p U.unop a)
    naturality := fun U V h => by
      apply AddCommGrpCat.ext
      intro s
      change L.val.obj U at s
      symm
      change L.val.map h (schemeConstantAt p U.unop a • s) =
        schemeConstantAt p V.unop a • L.val.map h s
      rw [L.val.map_smul]
      exact congrArg (fun r : Γ(X, V.unop) => r • L.val.map h s)
        (schemeConstantAt_restrict p h.unop a) }⟩
  map_one' := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change L.val.obj U at s
    change schemeConstantAt p U.unop 1 • s = s
    simp
  map_zero' := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change L.val.obj U at s
    change schemeConstantAt p U.unop 0 • s = 0
    simp
  map_add' a b := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change L.val.obj U at s
    change schemeConstantAt p U.unop (a + b) • s =
      schemeConstantAt p U.unop a • s + schemeConstantAt p U.unop b • s
    rw [map_add, add_smul]
  map_mul' a b := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change L.val.obj U at s
    change schemeConstantAt p U.unop (a * b) • s =
      schemeConstantAt p U.unop a • (schemeConstantAt p U.unop b • s)
    rw [map_mul, mul_smul]

/-- The cohomology scalar action is induced by actual scalar endomorphisms,
not a chosen vector-space structure on the underlying additive group. -/
@[instance_reducible]
def schemeModuleCohomologyModule (L : X.Modules) (n : ℕ) :
    Module k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj L) n) where
  smul a x := CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L a) n x
  one_smul x := by
    change CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L 1) n x = x
    rw [map_one]
    exact CategoryTheory.Sheaf.H.map_id_apply x
  mul_smul a b x := by
    change CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L (a * b)) n x = _
    rw [map_mul]
    exact CategoryTheory.Sheaf.H.map_comp_apply _ _ x
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b x := by
    change CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L (a + b)) n x = _
    rw [map_add, CategoryTheory.Sheaf.H.map_add_apply]
    rfl
  zero_smul x := by
    change CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L 0) n x = 0
    rw [map_zero]
    change ((CategoryTheory.Sheaf.functorH _ n).map 0).hom x = 0
    rw [Functor.map_zero]
    rfl

/-- Actual module-sheaf morphisms commute with actual scalar endomorphisms. -/
theorem schemeModuleScalarEnd_naturality {L M : X.Modules} (q : L ⟶ M) (a : k) :
    schemeModuleScalarEnd p L a ≫ (schemeModulesToAbelianSheaves X).map q =
      (schemeModulesToAbelianSheaves X).map q ≫ schemeModuleScalarEnd p M a := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change L.val.obj U at s
  exact (q.val.app U).hom.map_smul (schemeConstantAt p U.unop a) s

/-- Actual cohomology maps induced by module-sheaf morphisms are base-field linear. -/
def schemeModuleCohomologyMap {L M : X.Modules} (q : L ⟶ M) (n : ℕ) :
    letI := schemeModuleCohomologyModule p L n
    letI := schemeModuleCohomologyModule p M n
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj L) n →ₗ[k]
      CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj M) n := by
  letI := schemeModuleCohomologyModule p L n
  letI := schemeModuleCohomologyModule p M n
  exact {
    __ := CategoryTheory.Sheaf.H.map ((schemeModulesToAbelianSheaves X).map q) n
    map_smul' := fun a x => by
      change CategoryTheory.Sheaf.H.map _ n
        (CategoryTheory.Sheaf.H.map _ n x) =
          CategoryTheory.Sheaf.H.map _ n (CategoryTheory.Sheaf.H.map _ n x)
      rw [← CategoryTheory.Sheaf.H.map_comp_apply,
        schemeModuleScalarEnd_naturality, CategoryTheory.Sheaf.H.map_comp_apply]
      rfl }

/-- The cohomology scalar is the map induced by multiplication on the sheaf. -/
theorem schemeModuleCohomology_smul (L : X.Modules) (n : ℕ) (a : k)
    (x : CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj L) n) :
    letI := schemeModuleCohomologyModule p L n
    a • x = CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L a) n x := rfl

/-- The degree-zero cohomology comparison is linear for the actual base-field
actions on cohomology and global sections. -/
def schemeModuleCohomologyEquiv₀ (L : X.Modules) :
    letI := schemeModuleCohomologyModule p L 0
    letI := schemeGlobalSectionsModuleOfMorphism p L
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj L) 0 ≃ₗ[k]
      Γ(L, ⊤) := by
  letI := schemeModuleCohomologyModule p L 0
  letI := schemeGlobalSectionsModuleOfMorphism p L
  exact {
    __ := CategoryTheory.Sheaf.H.equiv₀ ((schemeModulesToAbelianSheaves X).obj L)
      isTerminalTop
    map_smul' := fun a x => by
      change CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop
        (CategoryTheory.Sheaf.H.map (schemeModuleScalarEnd p L a) 0 x) =
          schemeConstantMap p a • (show Γ(L, ⊤) from
            CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop x)
      refine (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
        (schemeModuleScalarEnd p L a) x).symm.trans ?_
      let y : Γ(L, ⊤) := CategoryTheory.Sheaf.H.equiv₀
        ((schemeModulesToAbelianSheaves X).obj L) isTerminalTop x
      change schemeConstantAt p ⊤ a • y = schemeConstantMap p a • y
      have h : schemeConstantAt p ⊤ a = schemeConstantMap p a := by
        change X.presheaf.map (𝟙 (op ⊤)) (schemeConstantMap p a) = _
        rw [X.presheaf.map_id]
        rfl
      rw [h] }

end Normalizer
