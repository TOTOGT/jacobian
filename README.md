# jacobian

Lean 4 / Mathlib formalizations. Status as of 2026-11-12. A theorem marked **PROVED** here has
compiled on the author's Mac with no `sorry`; "compiles" is not the same claim as "proves what its
name says", so each row says what the theorem actually establishes.

Build: `lake build` (Mathlib is pinned by the committed `lake-manifest.json` and `lean-toolchain`).

## Modules

| Module | What it contains |
| :--- | :--- |
| `Jacobian.lean` | Umbrella module (renamed from `JacobianCounterexample.lean`, which was a copy of `SpectralDiagonalBound.lean` and contained no counterexample). |
| `SpectralDiagonalBound.lean` | For a Hermitian complex matrix, every diagonal entry is bounded by the spectral radius. |
| `Poisson.lean` | The standard symplectic Poisson bracket on `ℚ[x₁..xₘ, y₁..yₘ]`, with the Poisson axioms proved. |
| `Dixmier.lean` | The Weyl algebra as operators on `ℚ[x₁..xₙ]`, the commutation relation, and the Dixmier conjecture as a statement only. |
| `DualDerivations.lean` | Dual derivations built from the Jacobian inverse (the special case det J = -2). |
| `StandardConjectures.lean` | Algebraic steps used in arguments about the standard conjectures, plus the conjectures as statements. |

## Theorem registry

| Module | Theorem | Status | What it establishes |
| :--- | :--- | :--- | :--- |
| `SpectralDiagonalBound` | `diagonal_eq_quadForm` | PROVED | `A i i = eᵢ* A eᵢ` as an indicator sum. |
| `SpectralDiagonalBound` | `diagonal_le_spectralRadius` | PROVED | `‖A i i‖ ≤ sSup |λₖ|` for Hermitian `A` (spectral theorem, unitary rows sum to 1). |
| `Poisson` | `standardPoissonBracket` (def) | defined | `{p,q} = Σᵢ (∂ₓᵢp ∂ᵧᵢq − ∂ᵧᵢp ∂ₓᵢq)`. |
| `Poisson` | `_skew`, `_leibniz`, `_jacobi` | PROVED | The three Poisson axioms for that bracket. |
| `Poisson` | `standardPoissonBracket_is_valid` | PROVED | The bracket is a `PoissonBracket` structure. |
| `Dixmier` | `pderiv_mulX_comm` | PROVED | `∂ᵢ(xⱼ p) − xⱼ ∂ᵢ p = δᵢⱼ p`. |
| `Dixmier` | `DixmierConjecture` | OPEN | Statement only (`def … : Prop`). Equivalent to the Poisson conjecture (Belov-Kanel–Kontsevich). |
| `Poisson` | `PoissonConjecture` | OPEN | Statement only. |
| `DualDerivations` | `dualDerivation_apply_F` | PROVED | Holds under the hypothesis `det J = C (-2)`, a specific constant, not the general Jacobian conjecture. |
| `StandardConjectures` | `injective_is_surjective_of_pairing` etc. | PROVED | Finite-dimensional linear algebra steps. |

Nothing in this repository proves or disproves the Jacobian, Dixmier or Poisson conjectures.
