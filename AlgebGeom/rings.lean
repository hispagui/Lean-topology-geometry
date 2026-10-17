import Mathlib

open Polynomial

#check Polynomial
#check Ideal
#check Ideal.IsPrime
#check PrimeSpectrum

variable {R : Type*} [CommRing R]






namespace Ideal.Quotient

-- an ideal I is prime ↔ R/I is an integral domain
theorem isDomain_iff_isPrime (I : Ideal R) : I.IsPrime ↔ IsDomain (R ⧸ I) := by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · have : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    have := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_zero h
