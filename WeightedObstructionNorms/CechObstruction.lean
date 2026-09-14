import WeightedObstructionNorms.CechSplitting
import WeightedObstructionNorms.NormedCohomology

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace CechObstruction
open FiniteObservations CechAllDegrees CechSplitting
section General
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

def newWeight (q : State E → ℝ) (p : ℕ) (j : NewCoordinate E S M p) : ℝ :=
  weight E q (observation M j.1) j.2.val.val

include o in
lemma newWeight_positive {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) :
    ∀ j, 0 < newWeight E S M q p j := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  intro j
  exact weight_positive E hq _ _

end General
section Linear
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

/-- The obstruction norm on the manuscript's actual Cech cohomology, obtained
from the concrete old/new coordinate splitting and marginal reference weights. -/
def norm (q : State E → ℝ) (p : ℕ) (α : Cohomology E S M p) : ℝ :=
  (window E S M o p).obstructionValue (newWeight E S M q p)
    ((cohomologyEquiv E S M o p).symm α)

lemma norm_nonneg (q : State E → ℝ) (p : ℕ) (α : Cohomology E S M p) :
    0 ≤ norm E S M o q p α := (window E S M o p).obstruction_nonneg _ _

lemma norm_zero (q : State E → ℝ) (p : ℕ) : norm E S M o q p 0 = 0 := by
  simp [norm, RelativeWindow.obstruction_zero]

lemma norm_eq_zero_iff {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : Cohomology E S M p) : norm E S M o q p α = 0 ↔ α = 0 := by
  rw [norm, (window E S M o p).obstruction_eq_zero_iff (newWeight_positive E S M o hq p)]
  exact (cohomologyEquiv E S M o p).symm.map_eq_zero_iff

lemma norm_add_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α β : Cohomology E S M p) :
    norm E S M o q p (α + β) ≤ norm E S M o q p α + norm E S M o q p β := by
  unfold norm
  rw [map_add]
  exact (window E S M o p).obstruction_add_le (newWeight_positive E S M o hq p) _ _

lemma norm_smul {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (a : ℝ) (α : Cohomology E S M p) : norm E S M o q p (a • α) = |a| * norm E S M o q p α := by
  unfold norm
  rw [map_smul]
  exact (window E S M o p).obstruction_smul_eq (newWeight_positive E S M o hq p) a _

lemma weight_comparison {q q' : State E → ℝ} {a b : ℝ}
    (hl : ∀ z, a * q z ≤ q' z) (hu : ∀ z, q' z ≤ b * q z) (A : Finset I) (y : LocalState E A) :
    a * weight E q A y ≤ weight E q' A y ∧ weight E q' A y ≤ b * weight E q A y := by
  classical
  simp only [weight, Marginal.push, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro z _
    split_ifs <;> simp_all
  · apply Finset.sum_le_sum
    intro z _
    split_ifs <;> simp_all

/-- Proposition 5.4 for reference laws on the original finite state space and
for every actual Cech cohomology degree. -/
theorem reference_comparison {q q' : State E → ℝ} (hq : ∀ z, 0 < q z)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ z, a * q z ≤ q' z) (hu : ∀ z, q' z ≤ b * q z)
    (p : ℕ) (α : Cohomology E S M p) :
    norm E S M o q p α / b ≤ norm E S M o q' p α ∧
      norm E S M o q' p α ≤ norm E S M o q p α / a := by
  exact (window E S M o p).reference_comparison (newWeight_positive E S M o hq p) ha hb
    (fun j => (weight_comparison E hl hu _ _).1)
    (fun j => (weight_comparison E hl hu _ _).2) _

def connecting (p : ℕ) : LinearMap.ker (window E S M o p).relativeD →ₗ[ℝ] Cohomology E S M p :=
  (cohomologyEquiv E S M o p).toLinearMap ∘ₗ (window E S M o p).connecting

lemma connecting_surjective (p : ℕ) : Function.Surjective (connecting E S M o p) :=
  (cohomologyEquiv E S M o p).surjective.comp (window E S M o p).connecting_surjective

theorem unit_ball {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) (α : Cohomology E S M p) :
    norm E S M o q p α ≤ 1 ↔ ∃ v : LinearMap.ker (window E S M o p).relativeD,
      connecting E S M o p v = α ∧ ∀ j, |v.val j| ≤ newWeight E S M q p j := by
  rw [norm, (window E S M o p).relative_unit_ball (newWeight_positive E S M o hq p)]
  constructor
  · rintro ⟨v, hv, hb⟩
    refine ⟨v, ?_, hb⟩
    change cohomologyEquiv E S M o p ((window E S M o p).connecting v) = α
    rw [hv, LinearEquiv.apply_symm_apply]
  · rintro ⟨v, hv, hb⟩
    refine ⟨v, ?_, hb⟩
    apply (cohomologyEquiv E S M o p).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hv

/-- A reference-law-indexed type copy of the original Cech cohomology. -/
def Normed (_o : State E) (q : State E → ℝ) (_hq : ∀ z, 0 < q z) (p : ℕ) := Cohomology E S M p

namespace Normed
variable {E S M} {q : State E → ℝ} {hq : ∀ z, 0 < q z} {p : ℕ}

instance : AddCommGroup (Normed E S M o q hq p) := inferInstanceAs (AddCommGroup (Cohomology E S M p))
instance : Module ℝ (Normed E S M o q hq p) := inferInstanceAs (Module ℝ (Cohomology E S M p))

/-- The chosen base state affects only the exactness proof, not the value. -/
instance : Norm (Normed E S M o q hq p) := ⟨CechObstruction.norm E S M o q p⟩

def normCore : NormedSpace.Core ℝ (Normed E S M o q hq p) where
  norm_nonneg := norm_nonneg E S M o q p
  norm_triangle := norm_add_le E S M o hq p
  norm_smul a x := norm_smul E S M o hq p a x
  norm_eq_zero_iff := norm_eq_zero_iff E S M o hq p

instance : NormedAddCommGroup (Normed E S M o q hq p) := NormedAddCommGroup.ofCore (normCore o)
instance : NormedSpace ℝ (Normed E S M o q hq p) := NormedSpace.ofCore (normCore o)
instance : FiniteDimensional ℝ (Normed E S M o q hq p) :=
  inferInstanceAs (FiniteDimensional ℝ (Cohomology E S M p))

end Normed

end Linear
end CechObstruction
end WeightedObstructionNorms
