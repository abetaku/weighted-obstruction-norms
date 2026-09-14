import WeightedObstructionNorms.CechObstruction
import WeightedObstructionNorms.RelativeCohomology

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace WeightedObstructionNorms
namespace CechRelative
open FiniteObservations CechAllDegrees CechSplitting
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

def predecessor (n : ℕ) : RelativePredecessor (window E S M o (n + 1))
    (Coordinate E Finset.univ M n) where
  oldPrevious := (pack E S M (n + 1)).symm.toLinearMap ∘ₗ takeOld E S M (n + 1) ∘ₗ
    differential E Finset.univ M n ∘ₗ (pack E Finset.univ M n).toLinearMap
  newPrevious := takeNew E S M (n + 1) ∘ₗ differential E Finset.univ M n ∘ₗ
    (pack E Finset.univ M n).toLinearMap
  old_square := by
    intro z
    change (pack E S M (n + 2)).symm
        (differential E S M (n + 1) (takeOld E S M (n + 1)
          (differential E Finset.univ M n (pack E Finset.univ M n z)))) +
      (pack E S M (n + 2)).symm (takeOld E S M (n + 2)
        (differential E Finset.univ M (n + 1) (putNew E S M (n + 1)
          (takeNew E S M (n + 1) (differential E Finset.univ M n (pack E Finset.univ M n z)))))) = 0
    rw [← map_add, ← differential_takeOld, differential_squared, map_zero, map_zero]
  new_square := by
    intro z
    change takeNew E S M (n + 2)
      (differential E Finset.univ M (n + 1) (putNew E S M (n + 1)
        (takeNew E S M (n + 1) (differential E Finset.univ M n (pack E Finset.univ M n z))))) = 0
    rw [← differential_takeNew, differential_squared, map_zero]

lemma parts_injective (n : ℕ) (x y : Cochain E Finset.univ M n)
    (ho : takeOld E S M n x = takeOld E S M n y)
    (hn : takeNew E S M n x = takeNew E S M n y) : x = y := by
  calc
    x = _ := (split_identity E S M n x).symm
    _ = _ := by rw [ho, hn]
    _ = y := split_identity E S M n y

lemma predecessor_exact (n : ℕ) : (predecessor E S M o n).ExactAtPrevious := by
  intro u v hu hv
  let x : Cochain E Finset.univ M (n + 1) :=
    extension E S M (Finset.subset_univ S) (n + 1) (pack E S M (n + 1) u) +
      putNew E S M (n + 1) v
  have hxo : takeOld E S M (n + 1) x = pack E S M (n + 1) u := by
    rw [show x = _ from rfl, map_add, takeOld_extension, takeOld_putNew, add_zero]
  have hxn : takeNew E S M (n + 1) x = v := by
    rw [show x = _ from rfl, map_add, takeNew_extension, takeNew_putNew, zero_add]
  have hclosed : differential E Finset.univ M (n + 1) x = 0 := by
    apply parts_injective E S M (n + 2)
    · rw [map_zero, differential_takeOld, hxo, hxn]
      apply (pack E S M (n + 2)).symm.injective
      rw [map_add, map_zero]
      exact hu
    · rw [map_zero, differential_takeNew, hxn]
      exact hv
  obtain ⟨z, hz⟩ := FullSupportAcyclicity.full_exists_primitive E o M n x hclosed
  refine ⟨(pack E Finset.univ M n).symm z, ?_, ?_⟩
  · change (pack E S M (n + 1)).symm (takeOld E S M (n + 1) (differential E Finset.univ M n z)) = u
    rw [hz, hxo, LinearEquiv.symm_apply_apply]
  · change takeNew E S M (n + 1) (differential E Finset.univ M n z) = v
    rw [hz, hxn]

/-- The relative-to-old cohomology isomorphism for every p ≥ 1. -/
def connectingEquiv (n : ℕ) : (predecessor E S M o n).Cohomology ≃ₗ[ℝ] Cohomology E S M (n + 1) :=
  ((predecessor E S M o n).connectingEquiv (predecessor_exact E S M o n)).trans
    (cohomologyEquiv E S M o (n + 1))

theorem connecting_preserves_norm (q : State E → ℝ) (n : ℕ)
    (β : (predecessor E S M o n).Cohomology) :
    CechObstruction.norm E S M o q (n + 1) (connectingEquiv E S M o n β) =
      (predecessor E S M o n).relativeValue (CechObstruction.newWeight E S M q (n + 1)) β := by
  unfold CechObstruction.norm connectingEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (predecessor E S M o n).connecting_preserves_value (predecessor_exact E S M o n) _ β

/-- At augmented degree -1 the preceding cochain space is zero. -/
def predecessorZero : RelativePredecessor (window E S M o 0) Empty where
  oldPrevious := 0
  newPrevious := 0
  old_square := by intro z; simp
  new_square := by intro z; simp

/-- The additional quotient required in paper degree zero. -/
def quotientConnectingEquivZero :
    ((predecessorZero E S M o).Cohomology ⧸ LinearMap.ker (predecessorZero E S M o).connecting) ≃ₗ[ℝ]
      Cohomology E S M 0 :=
  (predecessorZero E S M o).quotientConnectingEquiv.trans (cohomologyEquiv E S M o 0)

theorem quotientConnecting_preserves_norm_zero (q : State E → ℝ)
    (γ : (predecessorZero E S M o).Cohomology ⧸ LinearMap.ker (predecessorZero E S M o).connecting) :
    CechObstruction.norm E S M o q 0 (quotientConnectingEquivZero E S M o γ) =
      (predecessorZero E S M o).quotientValue (CechObstruction.newWeight E S M q 0) γ := by
  unfold CechObstruction.norm quotientConnectingEquivZero
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (predecessorZero E S M o).quotientConnecting_preserves_value _ γ

end CechRelative
end WeightedObstructionNorms
