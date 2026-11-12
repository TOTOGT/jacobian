import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

open MvPolynomial

/-!
# Poisson Algebras and the Poisson Conjecture — Concrete Version

STATUS: [CONJECTURAL] / Unverified Draft.
Written to replace vacuous placeholders with explicit Poisson structure definitions.
-/

variable (n : ℕ)

/-- A standard Poisson bracket on a ℚ-algebra A is a bilinear map {·, ·} : A × A → A
satisfying skew-symmetry, the Leibniz rule, and the Jacobi identity. -/
structure PoissonBracket (A : Type _) [CommRing A] [Algebra ℚ A] where
  bracket : A →ₗ[ℚ] A →ₗ[ℚ] A
  skew_symm : ∀ f g : A, bracket f g = - bracket g f
  leibniz : ∀ f g h : A, bracket f (g * h) = g * bracket f h + bracket f g * h
  jacobi : ∀ f g h : A, 
    bracket f (bracket g h) + bracket g (bracket h f) + bracket h (bracket f g) = 0

/-- Standard symplectic Poisson bracket on `ℚ[x₁..xₘ, y₁..yₘ]`:
`{p, q} = ∑ᵢ (∂p/∂xᵢ ∂q/∂yᵢ - ∂p/∂yᵢ ∂q/∂xᵢ)`, with `xᵢ = X (inl i)`, `yᵢ = X (inr i)`. -/
noncomputable def standardPoissonBracket (m : ℕ) :
    MvPolynomial (Fin m ⊕ Fin m) ℚ →ₗ[ℚ] MvPolynomial (Fin m ⊕ Fin m) ℚ →ₗ[ℚ]
      MvPolynomial (Fin m ⊕ Fin m) ℚ :=
  ∑ i : Fin m,
    ((LinearMap.mul ℚ (MvPolynomial (Fin m ⊕ Fin m) ℚ)).compl₁₂
        (pderiv (Sum.inl i)).toLinearMap (pderiv (Sum.inr i)).toLinearMap
      - (LinearMap.mul ℚ (MvPolynomial (Fin m ⊕ Fin m) ℚ)).compl₁₂
        (pderiv (Sum.inr i)).toLinearMap (pderiv (Sum.inl i)).toLinearMap)

/-- UNTESTED (2026-11-12): the bracket in coordinates. -/
theorem standardPoissonBracket_apply (m : ℕ) (f g : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    standardPoissonBracket m f g = ∑ i : Fin m,
      (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g
        - pderiv (Sum.inr i) f * pderiv (Sum.inl i) g) := by
  simp [standardPoissonBracket, LinearMap.sum_apply]

/-- UNTESTED (2026-11-12). -/
theorem standardPoissonBracket_skew (m : ℕ) (f g : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    standardPoissonBracket m f g = - standardPoissonBracket m g f := by
  rw [standardPoissonBracket_apply, standardPoissonBracket_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- UNTESTED (2026-11-12): Leibniz in the second argument. -/
theorem standardPoissonBracket_leibniz (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    standardPoissonBracket m f (g * h) =
      g * standardPoissonBracket m f h + standardPoissonBracket m f g * h := by
  rw [standardPoissonBracket_apply, standardPoissonBracket_apply, standardPoissonBracket_apply,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-! ### Jacobi identity (UNTESTED, written 2026-11-12)
Strategy: `jac f g h` (the Jacobi expression) is additive, cyclic, and a derivation in each slot
(from skew + Leibniz). Polynomials are built from constants and `X a` by `+` and `* X n`, so it
suffices to check `jac (X a) (X b) (X c) = 0`, true because `{X b, X c}` is a constant and the
bracket with a constant is 0. -/

theorem sPB_leib1 (m : ℕ) (g h f : MvPolynomial (Fin m ⊕ Fin m) ℚ) : standardPoissonBracket m (g * h) f = g * standardPoissonBracket m h f + standardPoissonBracket m g f * h := by
  rw [standardPoissonBracket_skew m (g * h) f, standardPoissonBracket_leibniz m f g h,
    standardPoissonBracket_skew m f h, standardPoissonBracket_skew m f g]
  ring

theorem sPB_const_right (m : ℕ) (f : MvPolynomial (Fin m ⊕ Fin m) ℚ) (r : ℚ) : standardPoissonBracket m f (C r) = 0 := by
  simp [standardPoissonBracket_apply]

theorem sPB_const_left (m : ℕ) (g : MvPolynomial (Fin m ⊕ Fin m) ℚ) (r : ℚ) : standardPoissonBracket m (C r) g = 0 := by
  simp [standardPoissonBracket_apply]

/-- The Jacobi expression. -/
noncomputable def jac (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) : MvPolynomial (Fin m ⊕ Fin m) ℚ :=
  standardPoissonBracket m f (standardPoissonBracket m g h) + standardPoissonBracket m g (standardPoissonBracket m h f) + standardPoissonBracket m h (standardPoissonBracket m f g)

theorem jac_cyc (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) : jac m f g h = jac m g h f := by
  unfold jac; ring

theorem jac_mid (m : ℕ) (f g1 g2 h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m f (g1 * g2) h = g1 * jac m f g2 h + g2 * jac m f g1 h := by
  unfold jac
  simp only [sPB_leib1, standardPoissonBracket_leibniz, map_add]
  linear_combination (standardPoissonBracket m f g2) * standardPoissonBracket_skew m g1 h
    + (standardPoissonBracket m f g1) * standardPoissonBracket_skew m g2 h

theorem jac_first (m : ℕ) (f1 f2 g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m (f1 * f2) g h = f1 * jac m f2 g h + f2 * jac m f1 g h := by
  rw [jac_cyc m (f1 * f2) g h, jac_cyc m g h (f1 * f2), jac_mid, jac_cyc m h f2 g,
    jac_cyc m h f1 g]

theorem jac_third (m : ℕ) (f g h1 h2 : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m f g (h1 * h2) = h1 * jac m f g h2 + h2 * jac m f g h1 := by
  rw [jac_cyc m f g (h1 * h2), jac_mid, ← jac_cyc m f g h2, ← jac_cyc m f g h1]

theorem jac_add1 (m : ℕ) (f1 f2 g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m (f1 + f2) g h = jac m f1 g h + jac m f2 g h := by
  unfold jac; simp only [map_add, LinearMap.add_apply]; ring

theorem jac_add2 (m : ℕ) (f g1 g2 h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m f (g1 + g2) h = jac m f g1 h + jac m f g2 h := by
  unfold jac; simp only [map_add, LinearMap.add_apply]; ring

theorem jac_add3 (m : ℕ) (f g h1 h2 : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    jac m f g (h1 + h2) = jac m f g h1 + jac m f g h2 := by
  unfold jac; simp only [map_add, LinearMap.add_apply]; ring

theorem jac_const (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) (r : ℚ) :
    jac m (C r) g h = 0 ∧ jac m f (C r) h = 0 ∧ jac m f g (C r) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [jac, sPB_const_right, sPB_const_left]

/-- Brackets of generators are constants. -/
theorem sPB_gen (m : ℕ) (a b : Fin m ⊕ Fin m) : ∃ r : ℚ, standardPoissonBracket m (X a) (X b) = C r := by
  have key : ∀ (c a : Fin m ⊕ Fin m),
      ((Pi.single c (1 : MvPolynomial (Fin m ⊕ Fin m) ℚ) : Fin m ⊕ Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) a) = C ((Pi.single c (1 : ℚ) : Fin m ⊕ Fin m → ℚ) a) := by
    intro c a
    by_cases h : a = c
    · subst h; simp
    · simp [h]
  refine ⟨∑ i : Fin m, (((Pi.single (Sum.inl i) (1 : ℚ) : Fin m ⊕ Fin m → ℚ) a) * ((Pi.single (Sum.inr i) (1 : ℚ) : Fin m ⊕ Fin m → ℚ) b)
      - ((Pi.single (Sum.inr i) (1 : ℚ) : Fin m ⊕ Fin m → ℚ) a) * ((Pi.single (Sum.inl i) (1 : ℚ) : Fin m ⊕ Fin m → ℚ) b)), ?_⟩
  rw [standardPoissonBracket_apply]
  simp only [pderiv_X, key, map_sum, map_sub, map_mul]

theorem jac_gen (m : ℕ) (a b c : Fin m ⊕ Fin m) : jac m (X a) (X b) (X c) = 0 := by
  obtain ⟨r1, h1⟩ := sPB_gen m b c
  obtain ⟨r2, h2⟩ := sPB_gen m c a
  obtain ⟨r3, h3⟩ := sPB_gen m a b
  unfold jac
  rw [h1, h2, h3]
  simp [sPB_const_right]

theorem jac_step3 (m : ℕ) (a b : Fin m ⊕ Fin m) (h : MvPolynomial (Fin m ⊕ Fin m) ℚ) : jac m (X a) (X b) h = 0 := by
  induction h using MvPolynomial.induction_on
  next r => exact (jac_const m (X a) (X b) (X b) r).2.2
  next p q hp hq => rw [jac_add3, hp, hq, add_zero]
  next p n hp => rw [jac_third]; simp [jac_gen, hp]

theorem jac_step2 (m : ℕ) (a : Fin m ⊕ Fin m) (g : MvPolynomial (Fin m ⊕ Fin m) ℚ) : ∀ h : MvPolynomial (Fin m ⊕ Fin m) ℚ, jac m (X a) g h = 0 := by
  induction g using MvPolynomial.induction_on
  next r => intro h; exact (jac_const m (X a) (X a) h r).2.1
  next p q hp hq => intro h; rw [jac_add2, hp, hq, add_zero]
  next p n hp => intro h; rw [jac_mid]; simp [jac_step3, hp]

theorem jac_zero (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) : jac m f g h = 0 := by
  revert g h
  induction f using MvPolynomial.induction_on
  next r => intro g h; exact (jac_const m g g h r).1
  next p q hp hq => intro g h; rw [jac_add1, hp, hq, add_zero]
  next p n hp => intro g h; rw [jac_first]; simp [jac_step2, hp]

theorem standardPoissonBracket_jacobi (m : ℕ) (f g h : MvPolynomial (Fin m ⊕ Fin m) ℚ) :
    standardPoissonBracket m f (standardPoissonBracket m g h) + standardPoissonBracket m g (standardPoissonBracket m h f) + standardPoissonBracket m h (standardPoissonBracket m f g) = 0 :=
  jac_zero m f g h

/-- The standard symplectic bracket satisfies the Poisson axioms
(depends on `standardPoissonBracket_jacobi`, still open). -/
theorem standardPoissonBracket_is_valid (m : ℕ) :
    Nonempty (PoissonBracket (MvPolynomial (Fin m ⊕ Fin m) ℚ)) :=
  ⟨{ bracket := standardPoissonBracket m
     skew_symm := standardPoissonBracket_skew m
     leibniz := standardPoissonBracket_leibniz m
     jacobi := standardPoissonBracket_jacobi m }⟩

/-- A Poisson algebra endomorphism is a ℚ-algebra endomorphism that preserves the bracket. -/
def IsPoissonMap {A : Type _} [CommRing A] [Algebra ℚ A] (pb : PoissonBracket A)
    (φ : A →ₐ[ℚ] A) : Prop :=
  ∀ f g : A, φ (pb.bracket f g) = pb.bracket (φ f) (φ g)

/-- The Poisson Conjecture in dimension 2m: Every Poisson algebra endomorphism 
of ℚ[x₁, ..., xₘ, y₁, ..., y☵] equipped with the standard bracket is bijective. -/
def PoissonConjecture (m : ℕ) (pb : PoissonBracket (MvPolynomial (Fin m ⊕ Fin m) ℚ)) : Prop :=
  ∀ φ : MvPolynomial (Fin m ⊕ Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin m ⊕ Fin m) ℚ,
    IsPoissonMap pb φ → Function.Bijective φ
