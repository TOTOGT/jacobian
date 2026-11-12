import Poisson

open MvPolynomial

/-!
# Poisson endomorphisms have Jacobian determinant ±1

STATUS: UNTESTED draft (written 2026-11-12). Standard reduction, NOT a new result and NOT a
proof of the Poisson conjecture: it only shows that a Poisson endomorphism of ℚ[x,y] has
(det Jacobian)^2 = 1, i.e. det = ±1.

Hand derivation: F_a = φ(X a) satisfy {F_a,F_b} = φ({X a,X b}) = ω_ab (a constant), and
{F_a,F_b} = (J ω J.transpose)_ab, so J ω J.transpose = ω; det gives det(J)^2 det ω = det ω; det ω ≠ 0 since
ω * ω = -1.
-/

/-- The standard symplectic matrix `[[0, 1], [-1, 0]]`. -/
noncomputable def omega (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℚ :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem sPB_eq_omega (m : ℕ) (f g : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    standardPoissonBracket m f g =
      ∑ c, ∑ d, C (omega m c d) * (pderiv c f * pderiv d g) := by
  rw [standardPoissonBracket_apply]
  simp [omega, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, Finset.sum_add_distrib]
  ring

theorem sPB_gen_omega (m : ℕ) (a b : Fin m ⊕ Fin m) :
    standardPoissonBracket m (X a) (X b) = C (omega m a b) := by
  rw [sPB_eq_omega]
  simp [pderiv_X, Pi.single_apply]

theorem omega_mul_self (m : ℕ) : omega m * omega m = -1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [omega, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem omega_det_ne_zero (m : ℕ) : (omega m).det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det (omega_mul_self m)
  rw [Matrix.det_mul, h, Matrix.det_neg, Matrix.det_one] at h2
  simp at h2

theorem poisson_map_det_sq (m : ℕ) (φ : MvPolynomial (Fin m ⊕ Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hφ : ∀ f g, φ (standardPoissonBracket m f g) = standardPoissonBracket m (φ f) (φ g)) :
    (Matrix.of fun a b : Fin m ⊕ Fin m => pderiv b (φ (X a))).det ^ 2 = 1 := by
  set J : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (MvPolynomial (Fin m ⊕ Fin m) ℚ) :=
    Matrix.of fun a b => pderiv b (φ (X a)) with hJ
  set Ω : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (MvPolynomial (Fin m ⊕ Fin m) ℚ) :=
    (C : ℚ →+* MvPolynomial (Fin m ⊕ Fin m) ℚ).mapMatrix (omega m) with hΩ
  have hΩab : ∀ a b, Ω a b = C (omega m a b) := fun a b => rfl
  have h1 : ∀ a b, standardPoissonBracket m (φ (X a)) (φ (X b)) = C (omega m a b) := by
    intro a b
    rw [← hφ, sPB_gen_omega, ← MvPolynomial.algebraMap_eq]
    exact φ.commutes _
  have hent : ∀ a b, (J * Ω * J.transpose) a b = standardPoissonBracket m (φ (X a)) (φ (X b)) := by
    intro a b
    rw [sPB_eq_omega]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hJ, hΩab, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  have hmat : J * Ω * J.transpose = Ω := by
    ext a b
    rw [hent, h1, hΩab]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hΩdet : Ω.det = C (omega m).det := ((C : ℚ →+* MvPolynomial (Fin m ⊕ Fin m) ℚ).map_det _).symm
  have hne : Ω.det ≠ 0 := by
    rw [hΩdet]
    intro h
    exact omega_det_ne_zero m ((map_eq_zero_iff _ (MvPolynomial.C_injective _ _)).mp h)
  have h3 : Ω.det * (J.det ^ 2 - 1) = 0 := by linear_combination hdet
  have h4 := (mul_eq_zero.mp h3).resolve_left hne
  linear_combination h4

/-- Corollary: the Jacobian determinant of a Poisson endomorphism is `1` or `-1`. -/
theorem poisson_map_det_unit (m : ℕ)
    (φ : MvPolynomial (Fin m ⊕ Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hφ : ∀ f g, φ (standardPoissonBracket m f g) = standardPoissonBracket m (φ f) (φ g)) :
    (Matrix.of fun a b : Fin m ⊕ Fin m => pderiv b (φ (X a))).det = 1 ∨
    (Matrix.of fun a b : Fin m ⊕ Fin m => pderiv b (φ (X a))).det = -1 :=
  mul_self_eq_one_iff.mp (by rw [← sq]; exact poisson_map_det_sq m φ hφ)
