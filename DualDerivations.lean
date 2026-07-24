import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import «JacobianCounterexample»

open MvPolynomial Matrix

abbrev R := MvPolynomial (Fin 3) ℚ

noncomputable def jacobianMatrix (F : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of (fun i j => pderiv j (F i))

noncomputable def jacobianInverse (F : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  (C (-1 / 2 : ℚ) : R) • (jacobianMatrix F).adjugate

noncomputable def dualDerivation (F : Fin 3 → R) (i : Fin 3) : R →ₗ[ℚ] R :=
  Finset.sum Finset.univ (fun j =>
    (LinearMap.mulLeft ℚ (jacobianInverse F j i)).comp (pderiv j).toLinearMap)

/-- Key algebraic fact: J * J⁻¹ = 1 under det J = C(-2). -/
theorem jacobian_mul_inverse_eq_one (F : Fin 3 → R)
    (hdet : (jacobianMatrix F).det = C (-2 : ℚ)) :
    jacobianMatrix F * jacobianInverse F = 1 := by
  dsimp [jacobianInverse]
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet]
  -- Combine C(-2) and C(-1/2)
  rw [← smul_assoc]
  have h_coeff : (C (-2 : ℚ) * C (-1 / 2 : ℚ)) = 1 := by
    rw [← map_mul]
    norm_num
  -- Substitute scalar product C(-2) * C(-1/2) = 1
  ext r c
  simp only [smul_apply, one_apply, Algebra.smul_def]
  split_ifs with h
  · rw [mul_assoc, h_coeff, mul_one]
  · simp

/-- Fundamental identity: ∂'ᵢ(Fⱼ) = δᵢⱼ. -/
theorem dualDerivation_apply_F (F : Fin 3 → R)
    (hdet : (jacobianMatrix F).det = C (-2 : ℚ)) (i j : Fin 3) :
    dualDerivation F i (F j) = if i = j then 1 else 0 := by
  have step : dualDerivation F i (F j) = (jacobianMatrix F * jacobianInverse F) j i := by
    dsimp [dualDerivation]
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [jacobianMatrix]
    ring
  rw [step, jacobian_mul_inverse_eq_one F hdet, Matrix.one_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, ne_comm.mp h]
