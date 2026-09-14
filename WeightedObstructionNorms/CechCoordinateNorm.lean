import WeightedObstructionNorms.CechObstruction

noncomputable section
namespace WeightedObstructionNorms
namespace CechCoordinateNorm
open FiniteObservations CechAllDegrees CechSplitting
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

include o in
lemma putNew_norm_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (v : NewCoordinate E S M p → ℝ) :
    cochainNorm E Finset.univ M q p (putNew E S M p v) ≤ weightedNorm (CechObstruction.newWeight E S M q p) v := by
  classical
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (coordinateWeight_positive E Finset.univ M hq p) (weightedNorm_nonneg _ _)).2
  intro j
  by_cases hz : j.2.val ∈ projected E S (observation M j.1)
  · simp only [putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hz, abs_zero]
    exact mul_nonneg (weightedNorm_nonneg _ _) (coordinateWeight_positive E Finset.univ M hq p j).le
  · simp only [putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hz]
    exact coordinate_le_weightedNorm (x := v) (CechObstruction.newWeight_positive E S M o hq p) ⟨j.1, ⟨j.2, hz⟩⟩

include o in
lemma takeNew_norm_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (x : Cochain E Finset.univ M p) :
    weightedNorm (CechObstruction.newWeight E S M q p) (takeNew E S M p x) ≤ cochainNorm E Finset.univ M q p x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (CechObstruction.newWeight_positive E S M o hq p) (cochainNorm_nonneg E Finset.univ M q p x)).2
  intro j
  exact coordinate_le_weightedNorm (x := fun a => x a.1 a.2)
    (coordinateWeight_positive E Finset.univ M hq p) ⟨j.1, j.2.val⟩

end CechCoordinateNorm
end WeightedObstructionNorms
