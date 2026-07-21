import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open MvPolynomial

noncomputable section

def xVar : MvPolynomial (Fin 3) ℚ := X 0
def yVar : MvPolynomial (Fin 3) ℚ := X 1
def zVar : MvPolynomial (Fin 3) ℚ := X 2

def F1 : MvPolynomial (Fin 3) ℚ :=
  (C 1 + xVar * yVar) ^ 3 * zVar
    + yVar ^ 2 * (C 1 + xVar * yVar) * (C 4 + C 3 * xVar * yVar)

def F2 : MvPolynomial (Fin 3) ℚ :=
  yVar
    + C 3 * xVar * (C 1 + xVar * yVar) ^ 2 * zVar
    + C 3 * xVar * yVar ^ 2 * (C 4 + C 3 * xVar * yVar)

def F3 : MvPolynomial (Fin 3) ℚ :=
  C 2 * xVar - C 3 * xVar ^ 2 * yVar - xVar ^ 3 * zVar

def jacobianMatrix : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℚ) :=
  !![pderiv 0 F1, pderiv 1 F1, pderiv 2 F1;
     pderiv 0 F2, pderiv 1 F2, pderiv 2 F2;
     pderiv 0 F3, pderiv 1 F3, pderiv 2 F3]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem jacobian_det_eq_neg_two :
    jacobianMatrix.det = C (-2 : ℚ) := by
  unfold jacobianMatrix F1 F2 F3 xVar yVar zVar
  simp [Matrix.det_fin_three, pderiv_mul, pderiv_pow, pderiv_X, pderiv_C,
        Pi.single_eq_same, Pi.single_eq_of_ne]
  simp only [map_ofNat]
  ring

def p1 : Fin 3 → ℚ := ![0, 0, -1/4]
def p2 : Fin 3 → ℚ := ![1, -3/2, 13/2]
def p3 : Fin 3 → ℚ := ![-1, 3/2, 13/2]

set_option maxHeartbeats 1000000 in
theorem points_collide :
    (eval p1 F1, eval p1 F2, eval p1 F3) = (-1/4, 0, 0) ∧
    (eval p2 F1, eval p2 F2, eval p2 F3) = (-1/4, 0, 0) ∧
    (eval p3 F1, eval p3 F2, eval p3 F3) = (-1/4, 0, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [F1, F2, F3, xVar, yVar, zVar, p1, p2, p3]
    try norm_num

theorem points_pairwise_distinct : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro h
    have := congrFun h 0
    simp only [p1, p2, p3] at this
    try norm_num at this

theorem not_injective_despite_constant_jacobian :
    jacobianMatrix.det = C (-2 : ℚ) ∧
    ¬ Function.Injective (fun p : Fin 3 → ℚ => (eval p F1, eval p F2, eval p F3)) := by
  refine ⟨jacobian_det_eq_neg_two, ?_⟩
  intro hinj
  obtain ⟨e1, e2, e3⟩ := points_collide
  have h12 : p1 = p2 := hinj (e1.trans e2.symm)
  exact points_pairwise_distinct.1 h12

end
