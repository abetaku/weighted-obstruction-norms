import WeightedObstructionNorms.OrderObstruction
import WeightedObstructionNorms.OrderRestriction
import WeightedObstructionNorms.CechCoordinateNorm

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace OrderRestrictionNorm
open FiniteObservations CechAllDegrees CechSplitting OrderRestriction
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)
    (O : Finset (Finset I)) (f : OrderComplex.Index O → K) (hf : ∀ a, a.val ⊆ M (f a))
    (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

def windowMap (p : ℕ) : WindowMap (window E S M o p) (OrderObstruction.window E S O o hO p) where
  oldMap := (pack E S (OrderComplex.observations O) p).symm.toLinearMap ∘ₗ restriction E S M O f hf p ∘ₗ (pack E S M p).toLinearMap
  newMap := takeNew E S (OrderComplex.observations O) p ∘ₗ restriction E Finset.univ M O f hf p ∘ₗ putNew E S M p
  cochainMap := (pack E S (OrderComplex.observations O) (p + 1)).symm.toLinearMap ∘ₗ restriction E S M O f hf (p + 1) ∘ₗ
    (pack E S M (p + 1)).toLinearMap
  correction := (pack E S (OrderComplex.observations O) p).symm.toLinearMap ∘ₗ takeOld E S (OrderComplex.observations O) p ∘ₗ
    restriction E Finset.univ M O f hf p ∘ₗ putNew E S M p
  old_comm := by
    intro u
    change (pack E S (OrderComplex.observations O) (p + 1)).symm (restriction E S M O f hf (p + 1) (differential E S M p (pack E S M p u))) =
      (pack E S (OrderComplex.observations O) (p + 1)).symm (differential E S (OrderComplex.observations O) p (restriction E S M O f hf p (pack E S M p u)))
    rw [restriction_differential]
  closed := by
    intro c hc
    have hh : differential E S M (p + 1) (pack E S M (p + 1) c) = 0 :=
      (pack E S M (p + 2)).symm.injective (by exact hc)
    change (pack E S (OrderComplex.observations O) (p + 2)).symm (differential E S (OrderComplex.observations O) (p + 1)
      (restriction E S M O f hf (p + 1) (pack E S M (p + 1) c))) = 0
    rw [restriction_differential, hh, map_zero, map_zero]
  new_closed := by
    intro v hv
    change takeNew E S (OrderComplex.observations O) (p + 1) (differential E Finset.univ (OrderComplex.observations O) p
      (putNew E S (OrderComplex.observations O) p (takeNew E S (OrderComplex.observations O) p (restriction E Finset.univ M O f hf p (putNew E S M p v))))) = 0
    rw [← differential_takeNew, restriction_differential,
      CechSupportNorm.closed_lift E S M o p v hv, restriction_extension, takeNew_extension]
  lift_comm := by
    intro v hv
    change (pack E S (OrderComplex.observations O) (p + 1)).symm
        (restriction E S M O f hf (p + 1) (takeOld E S M (p + 1)
          (differential E Finset.univ M p (putNew E S M p v)))) =
      (pack E S (OrderComplex.observations O) (p + 1)).symm (differential E S (OrderComplex.observations O) p
        (takeOld E S (OrderComplex.observations O) p (restriction E Finset.univ M O f hf p (putNew E S M p v)))) +
      (pack E S (OrderComplex.observations O) (p + 1)).symm (takeOld E S (OrderComplex.observations O) (p + 1) (differential E Finset.univ (OrderComplex.observations O) p
        (putNew E S (OrderComplex.observations O) p (takeNew E S (OrderComplex.observations O) p (restriction E Finset.univ M O f hf p (putNew E S M p v))))))
    rw [← map_add, ← differential_takeOld, restriction_differential,
      CechSupportNorm.closed_lift E S M o p v hv, restriction_extension, takeOld_extension, takeOld_extension]

lemma new_map_bound {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (v : NewCoordinate E S M p → ℝ) :
    weightedNorm (CechObstruction.newWeight E S (OrderComplex.observations O) q p) ((windowMap E S M o O f hf hO p).newMap v) ≤
      weightedNorm (CechObstruction.newWeight E S M q p) v :=
  (CechCoordinateNorm.takeNew_norm_le E S (OrderComplex.observations O) o hq p _).trans
    ((cochain_nonexpansive E Finset.univ M O f hf o hq p _).trans (CechCoordinateNorm.putNew_norm_le E S M o hq p v))

lemma cohomology_naturality (p : ℕ) (α : (window E S M o p).Cohomology) :
    OrderObstruction.cohomologyEquiv E S O o hO p ((windowMap E S M o O f hf hO p).cohomologyMap α) =
      cohomologyMap E S M O f hf p (cohomologyEquiv E S M o p α) := by
  induction α using Submodule.Quotient.induction_on with
  | H c => rfl

/-- Nonexpansion of the actual obstruction norm under arbitrary observation restriction. -/
theorem norm_nonexpansive {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : Cohomology E S M p) :
    OrderObstruction.norm E S O o hO q p (cohomologyMap E S M O f hf p α) ≤
      CechObstruction.norm E S M o q p α := by
  have he : (OrderObstruction.cohomologyEquiv E S O o hO p).symm (cohomologyMap E S M O f hf p α) =
      (windowMap E S M o O f hf hO p).cohomologyMap ((cohomologyEquiv E S M o p).symm α) := by
    apply (OrderObstruction.cohomologyEquiv E S O o hO p).injective
    rw [LinearEquiv.apply_symm_apply, cohomology_naturality, LinearEquiv.apply_symm_apply]
  unfold CechObstruction.norm OrderObstruction.norm
  rw [he]
  exact (windowMap E S M o O f hf hO p).obstruction_nonexpansive
    (CechObstruction.newWeight_positive E S M o hq p) (new_map_bound E S M o O f hf hO hq p) _

end OrderRestrictionNorm
end WeightedObstructionNorms
