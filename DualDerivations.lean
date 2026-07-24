import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import «JacobianCounterexample»

open MvPolynomial Matrix

/-!
# Dual Derivations from the Jacobian Inverse

Attribution: Alpöge & Fable (July 2026) [CITED]
Formalization: G6 LLC / Principia Orthogona

STATUS: [PROVE-ME] attempt below — unverified, no Lean kernel available to
check this. The mathematical content is standard (adjugate gives a two-sided
inverse when the determinant is a unit; this is not the hard, novel step in
the Dixmier₃ argument — that is the derivation-commutation lemma still to
come). Flagged below are the two specific spots I have real uncertainty
about the exact Mathlib API for, as opposed to the overall proof strategy,
which I'm confident in.
-/

abbrev R := MvPolynomial (Fin 3) ℚ

noncomputable def jacobianMatrix (F : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of (fun i j => pderiv j (F i))

noncomputable def jacobianInverse (F : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  (C (-1 / 2 : ℚ)) • (jacobianMatrix F).adjugate

noncomputable def dualDerivation (F : Fin 3 → R) (i : Fin 3) : R →ₗ[ℚ] R :=
  Finset.sum Finset.univ (fun j =>
    (LinearMap.mulLeft ℚ (jacobianInverse F j i)).comp (pderiv j).toLinearMap)

/-- Key algebraic fact, isolated on its own: once `hdet` holds, J and its
"inverse" as constructed really do multiply to the identity matrix. This is
the load-bearing step; everything else is index bookkeeping. -/
theorem jacobian_mul_inverse_eq_one (F : Fin 3 → R)
    (hdet : (jacobianMatrix F).det = C (-2 : ℚ)) :
    jacobianMatrix F * jacobianInverse F = 1 := by
  unfold jacobianInverse
  -- UNCERTAIN (1): exact name for `M * (c • N) = c • (M * N)` — I believe
  -- this is `Matrix.mul_smul` or follows from `smul_mul_assoc` /
  -- `mul_smul_comm` depending on which side Mathlib states it on. If this
  -- line fails, that's the first thing to check against the real error.
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul]
  norm_num
  -- After `norm_num` reduces (-1/2 : ℚ) * (-2 : ℚ) to 1, the remaining goal
  -- should be `(C (1:ℚ)) • (1 : Matrix (Fin 3) (Fin 3) R) = 1`, i.e. that
  -- scaling the identity matrix by the ring unit `C 1 = 1` does nothing.
  -- UNCERTAIN (2): the exact closing simp set — likely `map_one` (to turn
  -- `C 1` into `1 : R`) followed by `one_smul`, but I'm not fully sure
  -- `norm_num` leaves the goal in a shape those apply to directly.
  simp [map_one, one_smul]

/-- Fundamental identity: ∂'ᵢ(Fⱼ) = δᵢⱼ. Reduced entirely to
`jacobian_mul_inverse_eq_one` plus unfolding `dualDerivation` as a matrix
product entry — no further hard content here. -/
theorem dualDerivation_apply_F (F : Fin 3 → R)
    (hdet : (jacobianMatrix F).det = C (-2 : ℚ)) (i j : Fin 3) :
    dualDerivation F i (F j) = if i = j then 1 else 0 := by
  have step : dualDerivation F i (F j) = (jacobianMatrix F * jacobianInverse F) j i := by
    unfold dualDerivation jacobianMatrix
    -- UNCERTAIN (3): how `Finset.sum` of `LinearMap`s unfolds under
    -- application, and the exact coercion lemma for `(pderiv j).toLinearMap`
    -- applied to `F j` reducing back to `pderiv j (F j')`. If this `simp`
    -- doesn't fully clear, the goal after it should still visibly be a sum
    -- of the form `Σ k, jacobianInverse F k i * pderiv k (F j)`, which
    -- `Matrix.mul_apply` (in reverse) matches directly.
    simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.comp_apply,
               LinearMap.mulLeft_apply]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [step, jacobian_mul_inverse_eq_one F hdet, Matrix.one_apply]
  simp [eq_comm]
