import WeightedObstructionNorms.ObservationRestriction

noncomputable section
namespace WeightedObstructionNorms
namespace ObservationAugmentation
open FiniteObservations CechAllDegrees ObservationRestriction AlternatingEvaluation
variable {I K L : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [LinearOrder K] [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E))
    (M : K → Finset I) (N : L → Finset I) (f : L → K) (hf : ∀ a, N a ⊆ M (f a))

/-- Under the original global-measure identification, restriction in degree -1 is the identity. -/
theorem restriction_augmentation (x : {z // z ∈ S} → ℝ) :
    restriction E S M N f hf 0 (augmentationEquiv E S M x) = augmentationEquiv E S N x := by
  funext t
  change evaluate (project E S M (observation N t) 0 (augmentationEquiv E S M x))
    (selected M N f hf t) = _
  have he : selected M N f hf t = (emptyTuple : Tuple (K := Vertex M (observation N t)) 0) := by
    funext i
    exact Fin.elim0 i
  rw [he, evaluate_ordered]
  change marginal E S (contains M emptyTuple) (augmentationEquiv E S M x (forget M emptyTuple)) = _
  rw [augmentationEquiv_push, augmentationEquiv_push]
  change Marginal.push _ (Marginal.push _ x) = _
  rw [Marginal.push_comp]
  rfl

end ObservationAugmentation
end WeightedObstructionNorms
