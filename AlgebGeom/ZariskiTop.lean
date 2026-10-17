module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Basic
import AlgebGeom.AffineVarieties



variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {X : Type*} [TopologicalSpace X]

abbrev R (k : Type*) [Field k] := MvPolynomial (Fin 2) k

open MvPolynomial


example : IsOpen (Set.univ : Set X) :=
  isOpen_univ

-- subset is Zariski closd if it is zero locus of polys.
def ZariskiClosed (k : Type*) [Field k] :
  Set (Set (Fin 2 → k)) :=
  Set.range fun (S : Set (R k)) =>
    MvPolynomial.zeroLocus k (Ideal.span S)

-- empty set is Zariskiclosed (by V(1))
theorem empty_mem : (∅ : Set (Fin 2 → k)) ∈ ZariskiClosed k := by
  refine ⟨{1}, ?_⟩
  dsimp only
  rw [zeroLocus_span] -- ⊢ zeroLocus k (Ideal.span {1}) = ∅
  ext x
  simp
-- intersectin of two Zclosed is Zclosed
theorem sInter_mem : ∀ A, A ⊆ ZariskiClosed k → ⋂₀ A ∈ ZariskiClosed k := by
  intro A hA
  refine ⟨{p | ∃ Z ∈ A, ∀ x ∈ Z, aeval x p = 0}, ?_⟩
  dsimp only
  rw [zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_sInter]
  constructor
  · intro hx Z hZ
    obtain ⟨T, rfl⟩ := hA hZ          -- Z is closed, so Z = V(T)
    dsimp only at hZ ⊢
    rw [zeroLocus_span]
    intro p hp                         -- p ∈ T; show p(x) = 0
    apply hx p
    refine ⟨_, hZ, ?_⟩                 -- p vanishes on V(T) ∈ A
    intro y hy
    rw [zeroLocus_span] at hy
    exact hy p hp
  · rintro hx p ⟨Z, hZ, hp⟩
    exact hp x (hx Z hZ)
-- union of two Zclosed is Zclosed
theorem union_mem : ∀ A, A ∈ ZariskiClosed k → ∀ B, B ∈ ZariskiClosed k →
    A ∪ B ∈ ZariskiClosed k := by
  rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
  refine ⟨Set.image2 (· * ·) S T, ?_⟩
  simp only [zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.forall_mem_image2, map_mul, mul_eq_zero]
  constructor
  · intro h
    by_cases hS : ∀ p ∈ S, aeval x p = 0
    · exact Or.inl hS
    · right
      intro q hq
      obtain ⟨p, hpS, hp⟩ := not_forall₂.mp hS   -- some p ∈ S with p(x) ≠ 0
      exact (h p hpS q hq).resolve_left hp
  · rintro (h | h) p hp q hq
    · exact Or.inl (h p hp)
    · exact Or.inr (h q hq)


@[instance_reducible]
def zariskiTop : TopologicalSpace (Fin 2 → k) :=
  TopologicalSpace.ofClosed
  (ZariskiClosed k)
    empty_mem
    sInter_mem
    union_mem


-- sanity check: in this topology, every V(S) is closed
example (S : Set (R k)) :
    @IsClosed _ zariskiTop (zeroLocus k (Ideal.span S)) :=
  @IsClosed.mk _ zariskiTop _ (by
    show (zeroLocus k (Ideal.span S))ᶜᶜ ∈ ZariskiClosed k
    rw [compl_compl]
    exact ⟨S, rfl⟩)

theorem point_closed (a : Fin 2 → k) : ({a} : Set (Fin 2 → k)) ∈ ZariskiClosed k := by
  refine ⟨{X 0 - C (a 0), X 1 - C (a 1)}, ?_⟩
  dsimp only
  rw [zeroLocus_span]
  ext x

  sorry



-- irreducible and connected space
def isReducible (V : Set (Fin 2 → k)) : Prop :=
  ∃ V₁ ∈ ZariskiClosed k, ∃ V₂ ∈ ZariskiClosed k, V = V₁ ∪ V₂ ∧ V₁ ≠ V ∧ V₂ ≠ V

def isIrreducible (V : Set ( Fin 2 → k)) : Prop :=
  V.Nonempty ∧
    ∀ Z₁ Z₂, Z₁ ∈ ZariskiClosed k → Z₂ ∈ ZariskiClosed k →
      V ⊆ Z₁ ∪ Z₂ → V ⊆ Z₁ ∨ V ⊆ Z₂

def isDisconnected (V : Set (Fin 2 → k)) : Prop :=
  ∃ V₁ ∈ ZariskiClosed k, ∃ V₂ ∈ ZariskiClosed k, V₁ ∩ V₂ = ∅ ∧ V = V₁ ∪ V₂ ∧ V₁ ≠ V ∧ V₂ ≠ V

def isConnected (V : Set (Fin 2 → k)) : Prop :=
  V.Nonempty ∧
    ∀ Z₁ Z₂, Z₁ ∈ ZariskiClosed k → Z₂ ∈ ZariskiClosed k →
      Z₁ ∪ Z₂ = V ∧ Z₁ ∩ Z₂ ≠ ∅



-- X irreducible iff A(X) integral domain
theorem IrredIffDom : ∀ V ∈ Set (Fin 2 → k) → (isIrreducible V ↔ IsDomain (coordinateRing V)) := by
  sorry

∀ A, A ∈ ZariskiClosed k → ∀ B, B ∈ ZariskiClosed k →
    A ∪ B ∈ ZariskiClosed k := by
