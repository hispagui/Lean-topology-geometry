
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Defs


open MvPolynomial
open Ideal.Quotient


variable {k K : Type*} [Field k] [Field K] [Algebra k K]

-- POLYNOMIAL RING k[x,y]
abbrev R (k : Type*) [Field k] := MvPolynomial (Fin 2) k
-- a polynomial in 2 variables (circle eq.)
noncomputable def circlePolynomial : R k :=
  (X 0)^2 + (X 1)^2 - 1

-- ZERO LOCI V(f)
-- (MvPolynomial.zeroLocus treats zero loci from ideals, V(I))
def Xset (f : R k) : Set (Fin 2 → k) :=
  zeroLocus k (Ideal.span ({f} : Set (R k)))
-- Circle as an affine variety :
def circle : Set (Fin 2 → k) :=
  Xset circlePolynomial

-- VANISHING IDEALS I(X)
def vanishingIdealOf (V : Set (Fin 2 → k)) : Ideal (R k) :=
  vanishingIdeal k V
-- vanishing ideal of circle
def circleIdeal : Ideal (R k) :=
  vanishingIdealOf circle


-- COORDINATE RINGS k[x,y]/I(X)   (remember / ≠ ⧸)
def coordinateRing (V : Set (Fin 2 → k)) :=
  (R k) ⧸ (vanishingIdealOf V)
def circleCoordinateRing :=
  coordinateRing (circle : Set (Fin 2 → k))









-- prove that D(fg) = D(f) ∩ D(g) in Spec R

variable {R : Type*} [CommRing R]



-- D(f)={p ∈ Spec(R) | f ∉ p}
def distinguishedOpen (f : R) : Set (PrimeSpectrum R) :=
  {p | f ∉ p.asIdeal}

-- x ∈ D(f) ↔ f ∉ (x)
theorem mem_distinguishedOpen (f : R) (x : PrimeSpectrum R) :
  x ∈ distinguishedOpen f ↔ f ∉ x.asIdeal := by
  rfl
