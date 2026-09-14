import WeightedObstructionNorms.SlicePolytope
import WeightedObstructionNorms.CechObstruction

noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace WeightedObstructionNorms
namespace CechPolytope
open FiniteObservations CechAllDegrees CechSplitting
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

/-- Theorem 4.1: the actual obstruction unit ball is a polytope, expressed
without a new axiom or an alternative definition of polytope. -/
theorem unit_ball_finite_convexHull {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) :
    ∃ F : Set (Cohomology E S M p), F.Finite ∧ convexHull ℝ F =
      {α | CechObstruction.norm E S M o q p α ≤ 1} := by
  classical
  obtain ⟨F, hF, he⟩ := SlicePolytope.image_exists_finite_convexHull
    (LinearMap.ker (window E S M o p).relativeD) (CechObstruction.newWeight E S M q p)
    (CechObstruction.connecting E S M o p)
  refine ⟨F, hF, he.trans ?_⟩
  ext α
  exact (CechObstruction.unit_ball E S M o hq p α).symm

theorem unit_ball_centrally_symmetric {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (p : ℕ) (α : Cohomology E S M p) :
    CechObstruction.norm E S M o q p (-α) ≤ 1 ↔ CechObstruction.norm E S M o q p α ≤ 1 := by
  have hh := CechObstruction.norm_smul E S M o hq p (-1) α
  simpa using congrArg (fun v : ℝ => v ≤ 1) hh

end CechPolytope
end WeightedObstructionNorms
