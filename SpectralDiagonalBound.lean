import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

open Matrix Finset

variable {n : Type _} [Fintype n] [DecidableEq n]

/-!
# Diagonal Entry Bound by Spectral Radius

STATUS: [CONJECTURAL] / Unverified Draft.
Framework Target: Spectral bound on matrix diagonal entries.
Author: Pablo Nogueira Grossi / dm³

NOTE: renamed the local radius definition to `matrixSpectralRadius` — Mathlib
already owns the name `spectralRadius` globally (general Banach-algebra
spectral radius, `Mathlib.Analysis.Normed.Algebra.Spectrum`), which is
transitively imported here via `InnerProductSpace.Spectrum`. Reusing the
bare name collided with it. Also: `Matrix.IsHermitian.eigenvalues` returns
`n → ℝ` (Hermitian eigenvalues are real), not `n → ℂ`, and `Complex.abs`
no longer exists — use the norm `‖·‖` instead.
-/

/-- Spectral radius of a matrix given a real-valued eigenvalue assignment
(as produced by `Matrix.IsHermitian.eigenvalues` for Hermitian matrices). -/
noncomputable def matrixSpectralRadius (_A : Matrix n n ℂ) (ev : n → ℝ) : ℝ :=
  sSup (Set.range (fun i => |ev i|))

/-- Lemma 1: eᵢ* A eᵢ = A i i. compiled clean on Mac 2026-11-12. -/
lemma diagonal_eq_quadForm (A : Matrix n n ℂ) (i : n) :
    A i i = ∑ j, ∑ k, (if j = i then (1 : ℂ) else 0) * A j k * (if k = i then (1 : ℂ) else 0) := by
  simp [ite_mul, mul_ite]

/-- Main Theorem: for Hermitian A, ‖A i i‖ ≤ spectral radius. compiled clean on Mac 2026-11-12.
    Proof: A = U D U*, so A i i = Σ_k |U i k|² λ_k with Σ_k |U i k|² = 1 (U U* = 1 at (i,i)),
    hence ‖A i i‖ ≤ Σ_k |U i k|² |λ_k| ≤ max_k |λ_k|. -/
theorem diagonal_le_spectralRadius
    (A : Matrix n n ℂ)
    (hA : A.IsHermitian)
    (i : n) :
    ‖A i i‖ ≤ matrixSpectralRadius A hA.eigenvalues := by
  set U : Matrix n n ℂ := ((hA.eigenvectorUnitary : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) with hU
  have h3 : ∀ k, U i k * star (U i k) = ((‖U i k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hw1 : ∑ k, ‖U i k‖ ^ 2 = 1 := by
    have h1 : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at h2
    simp only [Matrix.star_apply, Matrix.one_apply_eq, h3] at h2
    exact_mod_cast h2
  have hspec : A = U * Matrix.diagonal (fun k => (RCLike.ofReal (hA.eigenvalues k) : ℂ)) * star U := by
    exact hA.spectral_theorem
  have hAii : A i i = ∑ k, U i k * (RCLike.ofReal (hA.eigenvalues k) : ℂ) * star (U i k) := by
    have h2 : A i i = (U * Matrix.diagonal (fun k => (RCLike.ofReal (hA.eigenvalues k) : ℂ)) * star U) i i :=
      congrFun (congrFun hspec i) i
    rw [Matrix.mul_apply] at h2
    simp only [Matrix.mul_diagonal, Matrix.star_apply] at h2
    exact h2
  have hk : ∀ k, |hA.eigenvalues k| ≤ matrixSpectralRadius A hA.eigenvalues := fun k =>
    le_csSup (Set.finite_range _).bddAbove ⟨k, rfl⟩
  have hbound : ∀ k, ‖U i k * (RCLike.ofReal (hA.eigenvalues k) : ℂ) * star (U i k)‖
      ≤ ‖U i k‖ ^ 2 * matrixSpectralRadius A hA.eigenvalues := by
    intro k
    rw [norm_mul, norm_mul, norm_star, RCLike.norm_ofReal]
    calc ‖U i k‖ * |hA.eigenvalues k| * ‖U i k‖ = ‖U i k‖ ^ 2 * |hA.eigenvalues k| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk k) (sq_nonneg _)
  calc ‖A i i‖
      = ‖∑ k, U i k * (RCLike.ofReal (hA.eigenvalues k) : ℂ) * star (U i k)‖ := by rw [← hAii]
    _ ≤ ∑ k, ‖U i k * (RCLike.ofReal (hA.eigenvalues k) : ℂ) * star (U i k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖U i k‖ ^ 2 * matrixSpectralRadius A hA.eigenvalues :=
        Finset.sum_le_sum (fun k _ => hbound k)
    _ = (∑ k, ‖U i k‖ ^ 2) * matrixSpectralRadius A hA.eigenvalues := by rw [Finset.sum_mul]
    _ = matrixSpectralRadius A hA.eigenvalues := by rw [hw1, one_mul]
