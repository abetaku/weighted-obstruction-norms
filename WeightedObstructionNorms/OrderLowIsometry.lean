import WeightedObstructionNorms.OrderLowZero
import WeightedObstructionNorms.OrderLowOneInverse
import WeightedObstructionNorms.ObservationListInvariance

noncomputable section
namespace WeightedObstructionNorms
namespace OrderLowIsometry
open FiniteObservations
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I)) (o : State E)
    (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)
    {q : State E → ℝ} (hq : ∀ z, 0 < q z)

/-- Proposition A.1 in degree zero, as an actual linear isometric equivalence. -/
def zero : CechObstruction.Normed E S (OrderComparison.list O) o q hq 0 ≃ₗᵢ[ℝ]
    OrderObstruction.Normed E S O o hO q hq 0 where
  toLinearEquiv := OrderLowZero.cohomologyEquiv E S O hO
  norm_map' α := by
    change OrderObstruction.norm E S O o hO q 0 (OrderLowZero.cohomologyEquiv E S O hO α) = _
    rw [OrderLowZero.cohomologyEquiv_eq_comparison]
    exact OrderPrimitiveComparison.norm_eq_zero E S O o hO hq α

/-- Proposition A.1 in degree one; the inverse uses the explicit intersection formula. -/
def one : CechObstruction.Normed E S (OrderComparison.list O) o q hq 1 ≃ₗᵢ[ℝ]
    OrderObstruction.Normed E S O o hO q hq 1 where
  toLinearEquiv := OrderLowOneInverse.cohomologyEquiv E S O hO
  norm_map' α := by
    change OrderObstruction.norm E S O o hO q 1 (OrderLowOneInverse.cohomologyEquiv E S O hO α) = _
    rw [OrderLowOneInverse.cohomologyEquiv_eq_comparison]
    exact OrderLowOneInjective.norm_eq_one E S O hO o hq α

/-- The low-degree isometry is independent of the initial generating list. -/
theorem any_generating_list {K : Type*} [Fintype K] [LinearOrder K] (M : K → Finset I)
    (hM : CechLowDegrees.generated M = ↑O) (p : ℕ) (hp : p = 0 ∨ p = 1) :
    Nonempty (CechObstruction.Normed E S M o q hq p ≃ₗᵢ[ℝ] OrderObstruction.Normed E S O o hO q hq p) := by
  obtain ⟨e⟩ := ObservationListInvariance.generated_isometry E S M (OrderComparison.list O) o
    (hM.trans (OrderComparison.generated_list O hO).symm) hq p
  rcases hp with rfl | rfl
  · exact ⟨e.trans (zero E S O o hO hq)⟩
  · exact ⟨e.trans (one E S O o hO hq)⟩

end OrderLowIsometry
end WeightedObstructionNorms
