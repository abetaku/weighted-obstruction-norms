import WeightedObstructionNorms.CechLowComparison

noncomputable section
namespace WeightedObstructionNorms
namespace CechAugmentationNorm
open FiniteObservations CechAllDegrees
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)] (M : K → Finset I)

lemma global_weight (q : State E → ℝ) (t : Tuple (K := K) 0) (z : State E) :
    weight E q (observation M t) (project E (observation M t) z) = q z := by
  have hi : Function.Injective (project E (observation M t)) := by
    intro x y h
    funext i
    have hi : i ∈ observation M t := by rw [observation_zero]; exact Finset.mem_univ _
    exact congrFun h ⟨i,hi⟩
  exact Marginal.push_injective_apply _ hi q z

lemma norm_box_iff (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (u : {z : State E // z ∈ (Finset.univ : Finset (State E))} → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    cochainNorm E Finset.univ M q 0 (augmentationEquiv E Finset.univ M u) ≤ L ↔
      ∀ z, |u z| ≤ L * q z.val := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  rw [cochainNorm, weightedNorm_le_iff (coordinateWeight_positive E Finset.univ M hq 0) hL]
  constructor
  · intro h z
    have hh := h ⟨emptyTuple, globalProject E Finset.univ M emptyTuple z⟩
    change |u ((globalPointEquiv E Finset.univ M emptyTuple).symm
      (globalPointEquiv E Finset.univ M emptyTuple z))| ≤
        L * weight E q (observation M emptyTuple) (project E (observation M emptyTuple) z.val) at hh
    simpa only [Equiv.symm_apply_apply, global_weight] using hh
  · intro h j
    rcases j with ⟨t,y⟩
    obtain ⟨z,rfl⟩ := globalProject_surjective E Finset.univ M t y
    change |u ((globalPointEquiv E Finset.univ M t).symm
      (globalPointEquiv E Finset.univ M t z))| ≤
        L * weight E q (observation M t) (project E (observation M t) z.val)
    simpa only [Equiv.symm_apply_apply, global_weight] using h z

end CechAugmentationNorm
end WeightedObstructionNorms
