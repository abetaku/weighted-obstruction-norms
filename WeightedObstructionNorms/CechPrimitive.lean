import WeightedObstructionNorms.CechRelative

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace WeightedObstructionNorms
namespace CechPrimitive
open FiniteObservations CechAllDegrees CechSplitting
section General
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

abbrev Split (p : ℕ) := (Coordinate E S M p ⊕ NewCoordinate E S M p) → ℝ

def split (p : ℕ) (x : Cochain E Finset.univ M p) : Split E S M p :=
  Sum.elim ((pack E S M p).symm (takeOld E S M p x)) (takeNew E S M p x)

def join (p : ℕ) (x : Split E S M p) : Cochain E Finset.univ M p :=
  extension E S M (Finset.subset_univ S) p (pack E S M p (fun j => x (.inl j))) +
    putNew E S M p (fun j => x (.inr j))

lemma join_split (p : ℕ) (x : Cochain E Finset.univ M p) : join E S M p (split E S M p x) = x :=
  split_identity E S M p x

lemma split_join (p : ℕ) (x : Split E S M p) : split E S M p (join E S M p x) = x := by
  funext j
  cases j with
  | inl j =>
    change (pack E S M p).symm (takeOld E S M p (join E S M p x)) j = x (.inl j)
    rw [join, map_add, takeOld_extension, takeOld_putNew, add_zero, LinearEquiv.symm_apply_apply]
  | inr j =>
    change takeNew E S M p (join E S M p x) j = x (.inr j)
    rw [join, map_add, takeNew_extension, takeNew_putNew, zero_add]

include o in
lemma split_norm {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (x : Cochain E Finset.univ M p) :
    weightedNorm (Sum.elim (coordinateWeight E S M q p) (CechObstruction.newWeight E S M q p))
      (split E S M p x) = cochainNorm E Finset.univ M q p x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  have ho := coordinateWeight_positive E S M hq p
  have hn := CechObstruction.newWeight_positive E S M o hq p
  have hf := coordinateWeight_positive E Finset.univ M hq p
  have hs : ∀ j, 0 < Sum.elim (coordinateWeight E S M q p) (CechObstruction.newWeight E S M q p) j :=
    fun j => by cases j with | inl j => exact ho j | inr j => exact hn j
  apply le_antisymm
  · apply (weightedNorm_le_iff hs (cochainNorm_nonneg E Finset.univ M q p x)).2
    intro j
    cases j with
    | inl j => exact coordinate_le_weightedNorm (x := fun a => x a.1 a.2) hf ⟨j.1, supportInclude E (Finset.subset_univ S) _ j.2⟩
    | inr j => exact coordinate_le_weightedNorm (x := fun a => x a.1 a.2) hf ⟨j.1, j.2.val⟩
  · apply (weightedNorm_le_iff hf (weightedNorm_nonneg _ _)).2
    intro j
    by_cases hj : j.2.val ∈ projected E S (observation M j.1)
    · have he : supportInclude E (Finset.subset_univ S) _ ⟨j.2.val, hj⟩ = j.2 := Subtype.ext rfl
      have hh := coordinate_le_weightedNorm (x := split E S M p x) hs (.inl ⟨j.1, ⟨j.2.val, hj⟩⟩)
      change |x j.1 (supportInclude E (Finset.subset_univ S) _ ⟨j.2.val, hj⟩)| ≤ _ at hh
      rw [he] at hh
      exact hh
    · exact coordinate_le_weightedNorm (x := split E S M p x) hs (.inr ⟨j.1, ⟨j.2, hj⟩⟩)

lemma split_feasible_of_exact (p : ℕ)
    (hfull : ∀ x : Cochain E Finset.univ M (p + 1),
      differential E Finset.univ M (p + 1) x = 0 → ∃ u, differential E Finset.univ M p u = x) (c : LinearMap.ker (windowOfExact E S M p hfull).nextOldD)
    (x : Cochain E Finset.univ M p) :
    split E S M p x ∈ ((windowOfExact E S M p hfull).problem c).fullFeasible ↔
      differential E Finset.univ M p x = extension E S M (Finset.subset_univ S) (p + 1) (pack E S M (p + 1) c.val) := by
  change ( ( (windowOfExact E S M p hfull).oldD ((pack E S M p).symm (takeOld E S M p x)) +
      (windowOfExact E S M p hfull).liftD (takeNew E S M p x),
      0 + (windowOfExact E S M p hfull).relativeD (takeNew E S M p x)) = (c.val, 0)) ↔ _
  rw [zero_add, Prod.mk.injEq]
  constructor
  · rintro ⟨ho, hn⟩
    apply CechSplitting.parts_injective E S M (p + 1)
    · rw [takeOld_extension, differential_takeOld]
      apply (pack E S M (p + 1)).symm.injective
      rw [map_add, LinearEquiv.symm_apply_apply]
      exact ho
    · rw [takeNew_extension, differential_takeNew]
      exact hn
  · intro hx
    constructor
    · change (pack E S M (p + 1)).symm (differential E S M p (takeOld E S M p x)) +
        (pack E S M (p + 1)).symm (takeOld E S M (p + 1)
          (differential E Finset.univ M p (putNew E S M p (takeNew E S M p x)))) = c.val
      rw [← map_add, ← differential_takeOld, hx, takeOld_extension, LinearEquiv.symm_apply_apply]
    · change takeNew E S M (p + 1) (differential E Finset.univ M p (putNew E S M p (takeNew E S M p x))) = 0
      rw [← differential_takeNew, hx, takeNew_extension]

/-- The original full-cochain primitive optimization problem. -/
def cost (q : State E → ℝ) (p : ℕ) (c : Cochain E S M (p + 1)) : ℝ :=
  sInf (cochainNorm E Finset.univ M q p ''
    {x | differential E Finset.univ M p x = extension E S M (Finset.subset_univ S) (p + 1) c})

include o in
/-- Equality with block optimization, for complexes with proved full-support exactness. -/
theorem cost_eq_gamma_of_exact {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (hfull : ∀ x : Cochain E Finset.univ M (p + 1),
      differential E Finset.univ M (p + 1) x = 0 → ∃ u, differential E Finset.univ M p u = x)
    (c : LinearMap.ker (windowOfExact E S M p hfull).nextOldD) :
    cost E S M q p (pack E S M (p + 1) c.val) =
      ((windowOfExact E S M p hfull).problem c).gamma (coordinateWeight E S M q p) (CechObstruction.newWeight E S M q p) := by
  unfold cost LinearProblem.gamma minimum
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨split E S M p x, (split_feasible_of_exact E S M p hfull c x).2 hx, split_norm E S M o hq p x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨join E S M p x, ?_, ?_⟩
    · apply (split_feasible_of_exact E S M p hfull c _).1
      rw [split_join]
      exact hx
    · have hh := split_norm E S M o hq p (join E S M p x)
      rw [split_join] at hh
      exact hh.symm

end General
section Linear
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

lemma split_feasible (p : ℕ) (c : LinearMap.ker (window E S M o p).nextOldD)
    (x : Cochain E Finset.univ M p) :
    split E S M p x ∈ ((window E S M o p).problem c).fullFeasible ↔
      differential E Finset.univ M p x = extension E S M (Finset.subset_univ S) (p + 1) (pack E S M (p + 1) c.val) :=
  split_feasible_of_exact E S M p (FullSupportAcyclicity.full_exists_primitive E o M p) c x

theorem cost_eq_gamma {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (c : LinearMap.ker (window E S M o p).nextOldD) :
    cost E S M q p (pack E S M (p + 1) c.val) =
      ((window E S M o p).problem c).gamma (coordinateWeight E S M q p) (CechObstruction.newWeight E S M q p) :=
  cost_eq_gamma_of_exact E S M o hq p (FullSupportAcyclicity.full_exists_primitive E o M p) c

end Linear
end CechPrimitive
end WeightedObstructionNorms
