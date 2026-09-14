import WeightedObstructionNorms.CechAllDegrees

noncomputable section
namespace WeightedObstructionNorms
namespace CechAugmentationExtension
open FiniteObservations CechAllDegrees
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S T : Finset (State E)) (M : K → Finset I) (h : S ⊆ T)

def globalInclude (z : {z // z ∈ S}) : {z // z ∈ T} := ⟨z.val,h z.property⟩
def globalExtend : ({z // z ∈ S} → ℝ) →ₗ[ℝ] ({z // z ∈ T} → ℝ) :=
  Marginal.linear (globalInclude E S T h)

lemma extension_augmentation (u : {z // z ∈ S} → ℝ) :
    extension E S M h 0 (augmentationEquiv E S M u) =
      augmentationEquiv E T M (globalExtend E S T h u) := by
  funext t
  change extend E h (observation M t) (augmentationEquiv E S M u t) = _
  rw [augmentationEquiv_push, augmentationEquiv_push]
  change Marginal.push _ (Marginal.push _ u) = Marginal.push _ (Marginal.push _ u)
  rw [Marginal.push_comp, Marginal.push_comp]
  rfl

end CechAugmentationExtension
end WeightedObstructionNorms
