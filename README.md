Out with the Jacobian; good job everybody. 
In with my own theorems; 

Candidate Theorem Statement: Diagonal Entry Bound for Normal Matrices
In matrix theory, Rayleigh quotient bounds and the Schur–Horn theorem give us a classic result: the diagonal entries of a normal matrix A∈C 
n×n
  lie inside the convex hull of its spectrum. Consequently, every diagonal entry A 
ii
​
  is bounded by the spectral radius ρ(A):

∀i,∣A 
ii
​
 ∣≤ 
λ∈σ(A)
max
​
 ∣λ∣
Let's formalize a precise R / C formulation in Lean 4.

Draft File: SpectralDiagonalBound.lean
Lean
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

open Matrix Finset

variable {n : Type _} [Fintype n] [DecidableEq n]

/-!
# Diagonal Entry Bound by Spectral Radius

STATUS: [PROVE-ME] - Concrete, zero-shortcut formalization target.
Goal: Prove that for a normal (or Hermitian) matrix, every diagonal 
entry is bounded above by the maximum absolute eigenvalue.
-/

/-- Define the spectral radius of a matrix given its eigenvalues. -/
noncomputable def spectralRadius (A : Matrix n n ℂ) (ev : n → ℂ) : ℝ :=
  sup univ (fun i => Complex.abs (ev i))

/-- Theorem: For a Hermitian matrix A, the absolute value of any diagonal entry 
    A i i is bounded by the spectral radius. -/
theorem diagonal_le_spectralRadius 
    (A : Matrix n n ℂ) 
    (hA : A.IsHermitian) 
    (i : n) :
    Complex.abs (A i i) ≤ spectralRadius A (hA.eigenvalues) := by
  sorry
Why Formalizing This Specific Bounds Lemma Works Well
Self-Contained Scope: It relies strictly on standard linear algebra (Mathlib.LinearAlgebra.Matrix.Hermitian and spectrum tools), avoiding deep external dependencies.

Clear Proof Path:

Step 1: Express A 
ii
​
  as e 
i
∗
​
 Ae 
i
​
 .

Step 2: Apply the spectral decomposition theorem (A=UΛU 
∗
 ).

Step 3: Rewrite A 
ii
​
 =∑ 
k
​
 ∣u 
k,i
​
 ∣ 
2
 λ 
k
​
 , expressing A 
ii
​
  as a convex combination of eigenvalues λ 
k
​
  (since ∑ 
k
​
 ∣u 
k,i
​
 ∣ 
2
 =1).

Step 4: Apply the triangle inequality to bound ∣A 
ii
​
 ∣≤max 
k
​
 ∣λ 
k
​
 ∣.

Completeness: Once the sorry is closed, Lean's kernel verifies every step deterministically.

## Active Verification Priorities & Modules

### Current Modules

* **`JacobianCounterexample.lean`**: Counterexample polynomial map formulation.
* **`DualDerivations.lean`**: Dual derivation operators $\partial'_i = \sum_j (J^{-1})_{ji} \partial_j$.
* **`SpectralDiagonalBound.lean`**: Matrix spectral radius bounds on diagonal entries ($\forall i, |A_{ii}| \le \rho(A)$ for normal/Hermitian matrices).
* **`Dixmier.lean`**: Dixmier conjecture & endomorphism commutativity bounds.
* **`Poisson.lean`**: Symplectic Poisson bracket formulations.

---

### Theorem Registry

| Module | Theorem / Definition | Status | Proof Strategy / Notes |
| :--- | :--- | :--- | :--- |
| `DualDerivations.lean` | `dualDerivation_apply_F` | **`[PROVED]`** | Matrix adjugate identity $J \cdot \text{adj}(J) = \det(J) \cdot I$ |
| `SpectralDiagonalBound.lean` | `diagonal_le_spectralRadius` | **`[CONJECTURAL]`** | Rayleigh quotient / Convex hull of spectrum |
| `Poisson.lean` | `standardPoissonBracket_is_valid` | **`[PROVE-ME]`** | Jacobi identity verification |
