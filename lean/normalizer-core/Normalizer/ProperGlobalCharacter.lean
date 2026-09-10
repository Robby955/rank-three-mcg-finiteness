import Normalizer.ProperConstants
import Normalizer.SheafStalkFunctional

/-! A sheaf functional on an actual proper integral scheme has a canonical
base-field-valued character on global sections. Its scalar is constant on
every open, and the induced stalk functional has the same value on germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The constant-field module structure on actual global bundle sections,
obtained from the structure morphism. -/
@[instance_reducible]
def schemeGlobalSectionsModuleOfMorphism (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    Module k Γ(Q, ⊤) :=
  Module.compHom Γ(Q, ⊤) (schemeConstantMap f)

variable [IsAlgClosed k] [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [UniversallyClosed f] {Q : X.Modules}

/-- The scalar-valued global character constructed from a sheaf functional.
Global regular-function constancy is derived from the scheme hypotheses. -/
def properGlobalCharacter (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    letI := schemeGlobalSectionsModuleOfMorphism f Q
    Γ(Q, ⊤) →ₗ[k] k := by
  letI := schemeGlobalSectionsModuleOfMorphism f Q
  let l : Γ(Q, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) := (ψ.val.app (op ⊤)).hom
  exact {
    toFun := fun s => (properConstantEquiv f).symm (l s)
    map_add' := by intro s t; simp only [map_add]
    map_smul' := by
      intro a s
      change (properConstantEquiv f).symm
          (l (schemeConstantMap f a • s)) =
        a * (properConstantEquiv f).symm (l s)
      rw [l.map_smul]
      change (properConstantEquiv f).symm
          (properConstantEquiv f a * l s) = _
      rw [map_mul, RingEquiv.symm_apply_apply] }

/-- The constructed scalar represents the actual global character section. -/
theorem properGlobalCharacter_spec (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(Q, ⊤)) :
    schemeConstantMap f (properGlobalCharacter f ψ s) = ψ.val.app (op ⊤) s :=
  (properConstantEquiv f).apply_symm_apply _

/-- The same scalar describes the character of the restricted global
section on every actual open; no local constancy assumption is needed. -/
theorem properGlobalCharacter_restrict (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(Q, ⊤)) (U : X.Opens) :
    ψ.val.app (op U) (Q.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      schemeConstantAt f U (properGlobalCharacter f ψ s) := by
  exact (PresheafOfModules.naturality_apply ψ.val (homOfLE (show U ≤ ⊤ from le_top)).op s).trans
    (proper_global_function_restrict f (ψ.val.app (op ⊤) s) U)

/-- The local-ring-valued stalk functional agrees with the unique global
scalar on the germ of every global section, at every point. -/
theorem properGlobalCharacter_germ (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(Q, ⊤)) (x : X) :
    schemeStalkFunctional ψ x (Q.presheaf.germ ⊤ x trivial s) =
      X.presheaf.germ ⊤ x trivial (schemeConstantMap f (properGlobalCharacter f ψ s)) := by
  rw [schemeStalkFunctional_germ, properGlobalCharacter_spec]

end Normalizer
