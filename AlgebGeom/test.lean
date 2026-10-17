import Mathlib

#eval 2+2

-- concept of a ring
structure MyRing (alp : Type) where
  add : alp → alp → alp -- takes 2 elem returns 1 (all of types a)
  mul : alp → alp → alp -- same for multiplication
  zero : alp
  one : alp

  add_assoc :
    ∀ a b c : alp,
      add (add a b) c = add a (add b c) := by
      intros
      sorry
  mul_assoc :
    ∀ a b c : alp,
      mul (mul a b) c = mul a (mul b c) := by
      intros
      sorry
  zero_add :
    ∀ a : alp, add zero a = a := by
    intros
    sorry
  add_zero :
    ∀ a : alp, add a zero = a := by
    intros
    sorry
  one_mul :
    ∀ a : alp, mul one a = a := by
    intros
    sorry
  mul_one :
    ∀ a : alp, mul a one = a := by
    intros
    sorry
  left_distirb :
    ∀ a b c : alp,
      mul a (add b c) = add (mul a b) (mul a c) := by
    intros
    sorry

  def square (n : Nat) : Nat :=
    n * n



  -- natural numbers
def natRing : MyRing Nat where -- specifies type a as Nat
  add := Nat.add -- Nat addition
  mul := Nat.add
  zero := 0
  one := 1






#eval square 5
theorem square_zero : square 0 = 0 := by
  rfl -- proof by reflexivity

theorem add_zero_nat (n : Nat) : n+0 = n := by
  omega -- omega or cutsat solves linear arithmetic problems over N or Z
        -- simp also works here for ex.

def myDouble {alp : Type} (R : MyRing alp) (a : alp) : alp :=
  R.add a a



class MyRingOps (alp : Type) where -- difference with MyRing is t
  add : alp → alp → alp
  mul : alp → alp → alp
  zero : alp
  one : alp

instance : MyRingOps Nat where
  add := Nat.add
  mul := Nat.mul
  zero := 0
  one := 1

def squareExplicit {alp : Type} (R : MyRingOps alp) (a : alp) : alp :=
  MyRingOps.mul a a

def squareImplicit {alp : Type} [MyRingOps alp] (a : alp) : alp :=
  MyRingOps.mul a a

def myNatOps : MyRingOps Nat where
  add := Nat.add
  mul := Nat.mul
  zero := 0
  one := 1

#eval squareImplicit (5 : Nat)
#eval squareExplicit myNatOps 5


#check Int
#check Int.add
#check Int.instRing
#synth Ring Int --finds appropriate ring structure

example (a b : Int) : a + b = b + a := by
  exact add_comm a b

theorem add_self_eq_two_mul {R : Type} [Ring R] (a : R) :
    a + a = 2 * a := by -- adding to itself is same as mult by 2
  exact (two_mul a).symm -- calls exact proof of two_mul and tactic is symmetry


example (a b : Int) : a + b = b + a := by
  ring  -- proof by ring

example (a : Int) : a + a = 2 * a := by
  exact add_self_eq_two_mul a -- prove via my own thm
