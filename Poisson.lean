import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

open MvPolynomial

/-!
# Poisson Algebras, Poisson Brackets, and the Poisson Conjecture — honest version

STATUS: unverified. Not yet run through `lake build`. Replaces the previous
placeholder (`PoissonBracket` with a bare `bracket : R → R → R` field and the
actual required axioms left as unused comments). Every genuinely required
property of a Poisson bracket is now a real field of the structure, so an
instance cannot be constructed unless it actually satisfies them.
-/

/-- A Poisson bracket on a commutative ring `R`: a bilinear, skew-symmetric
operation satisfying the Jacobi identity and the Leibniz rule. Unlike the
previous version, these are actual structure fields — not comments — so
nothing can inhabit this type without proving all four properties. -/
structure PoissonBracket (R : Type*) [CommRing R] where
  bracket : R → R → R
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  smul_left : ∀ (c : ℤ) x y, bracket (c • x) y = c • bracket x y
  skew : ∀ x y, bracket x y = - bracket y x
  leibniz : ∀ x y z, bracket x (y * z) = bracket x y * z + y * bracket x z
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

/-- A Poisson algebra: a commutative ring equipped with a Poisson bracket. -/
structure PoissonAlgebra (R : Type*) [CommRing R] where
  poisson : PoissonBracket R

/-- A Poisson-algebra endomorphism: a ring endomorphism that also preserves
the bracket. This is the correct notion of morphism for the conjecture below
— an endomorphism that only preserves the ring structure but not the bracket
would trivially exist and would make the conjecture meaningless. -/
structure PoissonEndomorphism {R : Type*} [CommRing R] (P : PoissonAlgebra R) where
  toFun : R →+* R
  map_bracket : ∀ x y, toFun (P.poisson.bracket x y) = P.poisson.bracket (toFun x) (toFun y)

/-- The Poisson Conjecture, stated honestly: every Poisson-algebra
endomorphism (in the sense above) is bijective. This is the third
formulation in the Jacobian–Dixmier–Poisson equivalence (Adjamagbo–van den
Essen, 2007); it is not proved or disproved in this file. -/
def PoissonConjecture (R : Type*) [CommRing R] (P : PoissonAlgebra R) : Prop :=
  ∀ φ : PoissonEndomorphism P, Function.Bijective φ.toFun

/-- Sanity check: the canonical Poisson bracket on ℚ[x,y] given by
{f, g} = ∂f/∂x · ∂g/∂y − ∂f/∂y · ∂g/∂x actually satisfies the axioms above.
This is the standard example and is the bracket that would be needed to
state a Poisson-conjecture instance concretely for the n = 3 case relevant
to the Dixmier₃ argument (via ℚ[x,y,z] with an appropriate bracket). Left as
`sorry`: proving `jacobi` in particular requires real computation with
`pderiv`, not just a definitional unfolding. -/
noncomputable def standardBracket :
    PoissonBracket (MvPolynomial (Fin 2) ℚ) where
  bracket f g := pderiv 0 f * pderiv 1 g - pderiv 1 f * pderiv 0 g
  add_left := by sorry
  smul_left := by sorry
  skew := by sorry
  leibniz := by sorry
  jacobi := by sorry -- the genuinely hard one; not a formality
