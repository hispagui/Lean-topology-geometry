import Mathlib

open Polynomial

#check Polynomial
#check Ideal
#check Ideal.IsPrime
#check PrimeSpectrum

def distinguishedOpen {R : Type*} [CommRing R] (f : Polynomial R) :
  Set (Ideal (Polynomial R)) :=  -- D(f)={p ∈ Spec(R) | f ∉ p}
  {p | p.IsPrime ∧ f ∉ p }




theorem mem_distinguishedOpen'
  {R : Type*} [CommRing R]
  (f : Polynomial R)
  (x : PrimeSpectrum (Polynomial R)) :
  x ∈ distinguishedOpen' f ↔ f ∉ x.asIdeal := by
  rfl
