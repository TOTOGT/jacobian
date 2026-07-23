import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.Tactic
import «JacobianCounterexample»

open MvPolynomial Matrix

/-!
# Dual Derivations from the Jacobian Inverse

Attribution: Alpöge & Fable (July 2026) [CITED]
Formalization: G6 LLC / Principia Orthogona

STATUS: [CONJECTURAL] / Unverified Draft.
Constructs dual derivations ∂'ᵢ = Σⱼ (J⁻¹)ⱼᵢ ∂ⱼ for the counterexample map F.
-/

abbrev R := MvPolynomial (Fin 3) ℚ

/-- The Jacobian matrix J_ij = ∂F_i / ∂x_j of the Alpöge-Fable polynomial map. -/
noncomputable def jacobianMatrix (F : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of (fun i j => pderiv j (F i))

/-- The matrix inverse J⁻¹, valid because det J = -2 is a unit in ℚ[x₁,x₂,x₃]. -/
noncomputable def jacobianInverse (F : Fin 3 → R) (hdet : (jacobianMatrix F).det = -2) :
    Matrix (Fin 3) (Fin 3) R :=
  -- Adjugate divided by scalar determinant (-2)
  (- (1 / 2 : ℚ)) • (jacobianMatrix F).adjugate

/-- Dual derivations ∂'ᵢ = Σⱼ (J⁻¹)ⱼᵢ ∂ⱼ bundled as linear derivations on ℚ[x₁,x₂,x₃]. -/
noncomputable def dualDerivation (F : Fin 3 → R) (hdet : (jacobianMatrix F).det = -2) (i : Fin 3) :
    R →ₗ[ℚ] R where
  toFun p := ∑ j : Fin 3, (jacobianInverse F hdet j i) * (pderiv j p)
  map_add' p q := by
    simp_rw [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp_rw [RingHom.id_apply, map_smul, mul_smul_comm, Finset.smul_sum]

/-- Fundamental identity: ∂'ᵢ(F_j) = δ_ij. -/
theorem dualDerivation_apply_F (F : Fin 3 → R) (hdet : (jacobianMatrix F).det = -2) (i j : Fin 3) :
    dualDerivation F hdet i (F j) = if i = j then 1 else 0 := by
  sorry -- [PROVE-ME]: Matrix inverse multiplication identity (J⁻¹ J = I)
