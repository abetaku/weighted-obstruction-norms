import WeightedObstructionNorms.ObservationHomotopy
import WeightedObstructionNorms.ObservationRestrictionNorm
import WeightedObstructionNorms.ObservationRestriction0

noncomputable section
namespace WeightedObstructionNorms
namespace ObservationListInvariance
open FiniteObservations CechAllDegrees ObservationRestriction ObservationHomotopy
variable {I K L : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [LinearOrder K] [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)
    (N : L → Finset I) (f : L → K) (g : K → L)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ a, M a ⊆ N (g a))

lemma mutual_inverse (p : ℕ) (α : Cohomology E S M p) :
    cohomologyMap E S N M g hg p (cohomologyMap E S M N f hf p α) = α := by
  rw [cohomologyMap_comp]
  rw [cohomologyMap_choice_independent E S M M (f ∘ g) id
    (fun a => (hg a).trans (hf (g a))) (fun _ => Finset.Subset.refl _)]
  exact cohomologyMap_identity E S M p α

def cohomologyEquiv (p : ℕ) : Cohomology E S M p ≃ₗ[ℝ] Cohomology E S N p where
  toLinearMap := cohomologyMap E S M N f hf p
  invFun := cohomologyMap E S N M g hg p
  left_inv := mutual_inverse E S M N f g hf hg p
  right_inv := mutual_inverse E S N M g f hg hf p

variable [∀ i, DecidableEq (E i)] (o : State E)

include g hg in
lemma norm_preserved {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) (α : Cohomology E S M p) :
    CechObstruction.norm E S N o q p (cohomologyMap E S M N f hf p α) =
      CechObstruction.norm E S M o q p α := by
  apply le_antisymm (ObservationRestrictionNorm.norm_nonexpansive E S M o N f hf hq p α)
  have h := ObservationRestrictionNorm.norm_nonexpansive E S N o M g hg hq p
    (cohomologyMap E S M N f hf p α)
  rwa [mutual_inverse E S M N f g hf hg p α] at h

/-- The actual cohomology spaces with their obstruction norms are linearly isometric. -/
def isometry {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) :
    CechObstruction.Normed E S M o q hq p ≃ₗᵢ[ℝ] CechObstruction.Normed E S N o q hq p where
  toLinearEquiv := cohomologyEquiv E S M N f g hf hg p
  norm_map' := norm_preserved E S M N f g hf hg o hq p

/-- Corollary 5.2, in all degrees and using only equality of generated observation families. -/
theorem generated_isometry (h : CechLowDegrees.generated M = CechLowDegrees.generated N)
    {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) :
    Nonempty (CechObstruction.Normed E S M o q hq p ≃ₗᵢ[ℝ] CechObstruction.Normed E S N o q hq p) := by
  obtain ⟨f, hf⟩ := CechLowDegrees.exists_selection M N (by rw [h])
  obtain ⟨g, hg⟩ := CechLowDegrees.exists_selection N M (by rw [h])
  exact ⟨isometry E S M N f g hf hg o hq p⟩

end ObservationListInvariance
end WeightedObstructionNorms
