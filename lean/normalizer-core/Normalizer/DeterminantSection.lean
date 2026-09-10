import Normalizer.ExteriorSheaf
import Normalizer.TopExteriorCoordinate

/-! The determinant coefficient of the actual exterior product section.
For a rank-n bundle, the nth exterior sheaf is the intended determinant
line; its local-freeness and degree interpretation remain separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (H : X.Modules) (n : ℕ)

/-- In an actual basis of local sections, the sheaf exterior product is
the coordinate determinant times the exterior product of that basis. -/
theorem schemeExteriorPure_eq_det_smul (U : X.Opens)
    (b : Module.Basis (Fin n) Γ(X, U) Γ(H, U)) (v : Fin n → Γ(H, U)) :
    schemeExteriorPure H n U v =
      (frameCoordinateMatrix b v).det • schemeExteriorPure H n U b := by
  exact (congrArg ((schemeExteriorProjection H n).app (op U))
    (topWedge_eq_det_smul b v)).trans
      (((schemeExteriorProjection H n).app (op U)).hom.map_smul _ _)

/-- The exterior product of the specified global sections has the actual
local determinant formula on every open with a basis of local sections. -/
theorem schemeExteriorGlobalSection_local_det (s : Fin n → Γ(H, ⊤)) (U : X.Opens)
    (b : Module.Basis (Fin n) Γ(X, U) Γ(H, U)) :
    (schemeExteriorSheaf H n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (schemeExteriorGlobalSection H n s) =
        (frameCoordinateMatrix b
          (fun i => H.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i))).det •
            schemeExteriorPure H n U b :=
  (schemeExteriorPure_restrict H n (homOfLE le_top) s).trans
    (schemeExteriorPure_eq_det_smul H n U b _)

end Normalizer
