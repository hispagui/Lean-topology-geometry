import Mathlib

#eval Lean.versionString
#eval 2*9
#check 2^(3.8)

#eval String.append "Hello, " "Lean!"

-- String.append can only take 2 inputs, nesting needed
#eval String.append "great " (String.append "oak " "tree ")

#eval String.append "it is " (if 1>2 then "yes" else "no")

#check 1>2

-- LEAN comments
#eval if 3==3 then 5 else 7

#check 1-2
#eval 1-99

-- Type specification
#eval (1-55 : Int)
#eval (2 : Nat)
#check (2:Int)

-- functions
def hello := "Hello"

def addOne (x : Int) : Int := x+1
def g := -3
#eval addOne g

def times (x y:Int) := x*y
#eval times 4 5
#check times

def FermaLastTheorem := ∀ x y z n : Nat, n > 2 ∧ x*y*z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermaLastTheorem

theorem easy : 2+2 = 4 := rfl

#check easy

theorem hard : FermaLastTheorem := sorry

#check hard









structure Point2D where
    x : Float
    y : Float
deriving Repr

#check Point2D

def p := Point2D.mk 2 3

#check p
#check p.y



example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
    show ∃ l, m * n = l + l from ⟨_, hmn⟩


example (a b c : Real) : a * b * c = b * (a * c) := by
    rw [mul_comm a b]
    rw [mul_assoc b a c]




example (a b c : Real) : c * b * a = b * (a * c) := by
    rw [mul_comm c b]
    rw [mul_assoc b c a]
    rw [mul_comm a c]



variable (a b c d e f : Real)
example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d : Real)
#check a
#check a + b
#check (a : Nat)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

#check a * b == b * a


end
