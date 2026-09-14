import WeightedObstructionNorms.CechObstruction
import WeightedObstructionNorms.WindowMap

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace WeightedObstructionNorms
namespace CechSupportNorm
open FiniteObservations CechAllDegrees CechSplitting
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S T : Finset (State E)) (M : K → Finset I) (o : State E) (h : S ⊆ T)

lemma takeOld_included (n : ℕ) (x : Cochain E S M n) :
    takeOld E T M n (extension E S M (Finset.subset_univ S) n x) = extension E S M h n x := by
  rw [← extension_comp E S M h (Finset.subset_univ T) n x, takeOld_extension]

include h in
lemma takeNew_included (n : ℕ) (x : Cochain E S M n) :
    takeNew E T M n (extension E S M (Finset.subset_univ S) n x) = 0 := by
  rw [← extension_comp E S M h (Finset.subset_univ T) n x, takeNew_extension]

lemma closed_lift (p : ℕ) (v : NewCoordinate E S M p → ℝ)
    (hv : (window E S M o p).relativeD v = 0) :
    differential E Finset.univ M p (putNew E S M p v) =
      extension E S M (Finset.subset_univ S) (p + 1)
        (takeOld E S M (p + 1) (differential E Finset.univ M p (putNew E S M p v))) := by
  have hs := split_identity E S M (p + 1) (differential E Finset.univ M p (putNew E S M p v))
  change takeNew E S M (p + 1) (differential E Finset.univ M p (putNew E S M p v)) = 0 at hv
  rw [hv, map_zero, add_zero] at hs
  exact hs.symm

def map (p : ℕ) : WindowMap (window E S M o p) (window E T M o p) where
  oldMap := (pack E T M p).symm.toLinearMap ∘ₗ extension E S M h p ∘ₗ (pack E S M p).toLinearMap
  newMap := takeNew E T M p ∘ₗ putNew E S M p
  cochainMap := (pack E T M (p + 1)).symm.toLinearMap ∘ₗ extension E S M h (p + 1) ∘ₗ
    (pack E S M (p + 1)).toLinearMap
  correction := (pack E T M p).symm.toLinearMap ∘ₗ takeOld E T M p ∘ₗ putNew E S M p
  old_comm := by
    intro u
    change (pack E T M (p + 1)).symm (extension E S M h (p + 1) (differential E S M p (pack E S M p u))) =
      (pack E T M (p + 1)).symm (differential E T M p (extension E S M h p (pack E S M p u)))
    rw [extension_differential]
  closed := by
    intro c hc
    have hh : differential E S M (p + 1) (pack E S M (p + 1) c) = 0 :=
      (pack E S M (p + 2)).symm.injective (by exact hc)
    change (pack E T M (p + 2)).symm (differential E T M (p + 1)
      (extension E S M h (p + 1) (pack E S M (p + 1) c))) = 0
    rw [extension_differential, hh, map_zero, map_zero]
  new_closed := by
    intro v hv
    change takeNew E T M (p + 1) (differential E Finset.univ M p
      (putNew E T M p (takeNew E T M p (putNew E S M p v)))) = 0
    rw [← differential_takeNew, closed_lift E S M o p v hv, takeNew_included E S T M h]
  lift_comm := by
    intro v hv
    change (pack E T M (p + 1)).symm
        (extension E S M h (p + 1) (takeOld E S M (p + 1)
          (differential E Finset.univ M p (putNew E S M p v)))) =
      (pack E T M (p + 1)).symm (differential E T M p (takeOld E T M p (putNew E S M p v))) +
        (pack E T M (p + 1)).symm (takeOld E T M (p + 1) (differential E Finset.univ M p
          (putNew E T M p (takeNew E T M p (putNew E S M p v)))))
    rw [← map_add, ← differential_takeOld, closed_lift E S M o p v hv, takeOld_included E S T M h, takeOld_extension]

lemma new_map_apply (p : ℕ) (v : NewCoordinate E S M p → ℝ) (j : NewCoordinate E T M p)
    (hj : j.2.val.val ∉ projected E S (observation M j.1)) :
    (map E S T M o h p).newMap v j = v ⟨j.1, ⟨j.2.val, hj⟩⟩ := by
  simp [map, takeNew, putNew, hj]

lemma new_map_bound {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (v : NewCoordinate E S M p → ℝ) :
    weightedNorm (CechObstruction.newWeight E T M q p) ((map E S T M o h p).newMap v) ≤
      weightedNorm (CechObstruction.newWeight E S M q p) v := by
  apply (weightedNorm_le_iff (CechObstruction.newWeight_positive E T M o hq p)
    (weightedNorm_nonneg _ _)).2
  intro j
  have hj : j.2.val.val ∉ projected E S (observation M j.1) := by
    intro hh
    exact j.2.property (supportInclude E h _ ⟨_, hh⟩).property
  rw [new_map_apply E S T M o h p v j hj]
  exact coordinate_le_weightedNorm (CechObstruction.newWeight_positive E S M o hq p) ⟨j.1, ⟨j.2.val, hj⟩⟩

lemma cohomology_naturality (p : ℕ) (α : (window E S M o p).Cohomology) :
    cohomologyEquiv E T M o p ((map E S T M o h p).cohomologyMap α) =
      cohomologyExtension E S M h p (cohomologyEquiv E S M o p α) := by
  induction α using Submodule.Quotient.induction_on with
  | H c => rfl

/-- Proposition 3.3 on the actual all-degree support-enlargement map. -/
theorem norm_nonexpansive {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : Cohomology E S M p) :
    CechObstruction.norm E T M o q p (cohomologyExtension E S M h p α) ≤
      CechObstruction.norm E S M o q p α := by
  have he : (cohomologyEquiv E T M o p).symm (cohomologyExtension E S M h p α) =
      (map E S T M o h p).cohomologyMap ((cohomologyEquiv E S M o p).symm α) := by
    apply (cohomologyEquiv E T M o p).injective
    rw [LinearEquiv.apply_symm_apply, cohomology_naturality, LinearEquiv.apply_symm_apply]
  unfold CechObstruction.norm
  rw [he]
  exact (map E S T M o h p).obstruction_nonexpansive
    (CechObstruction.newWeight_positive E S M o hq p) (new_map_bound E S T M o h hq p) _

end CechSupportNorm
end WeightedObstructionNorms
