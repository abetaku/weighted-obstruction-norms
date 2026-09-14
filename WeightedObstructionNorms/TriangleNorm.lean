import WeightedObstructionNorms.TriangleCost

noncomputable section
open Filter Topology
namespace WeightedObstructionNorms
namespace TriangleNorm
open FiniteObservations BinaryMarginals TriangleSetup CechAllDegrees TriangleCocycle TriangleCost

/-- The correction norm of the paper's actual degree-one class. -/
theorem obstruction_norm : CechObstruction.norm E S M (diagonal 0) q₁ 1 obstructionClass = 2/3 := by
  have h := CechReciprocal.norm_limit E S M (diagonal 0) q₀_nonneg
    (fun z hz => (q₀_positive z).2 hz) q₀_zero q₁_positive 1
    ((CechSplitting.cycleEquiv E S M (diagonal 0) 1).symm cycle)
  have he : (fun ε => ε * CechPrimitive.cost E S M (q ε) 1 c) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => (2/3 : ℝ)) := by
    have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 2/3 := Ioc_mem_nhdsGT (by norm_num)
    filter_upwards [hs] with ε hε
    rw [cost_eq hε.1 (le_trans hε.2 (by norm_num))]
    have hh : 1 ≤ 2 / (3*ε) := (le_div_iff₀ (mul_pos (by norm_num) hε.1)).2 (by linarith)
    rw [max_eq_right hh]
    field_simp [ne_of_gt hε.1]
    <;> ring
  exact tendsto_nhds_unique (h.congr' he) tendsto_const_nhds

lemma obstruction_nonzero : obstructionClass ≠ 0 := by
  intro h
  have hn := obstruction_norm
  rw [h, CechObstruction.norm_zero] at hn
  norm_num at hn

lemma unit_primitive_threshold {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∃ x : Cochain E Finset.univ M 1,
      differential E Finset.univ M 1 x = extension E S M (Finset.subset_univ S) 2 c ∧
      cochainNorm E Finset.univ M (q ε) 1 x ≤ 1) ↔ 2/3 ≤ ε := by
  rw [feasible_threshold hε hε₁ (by norm_num), max_le_iff]
  simp only [le_refl, true_and]
  rw [div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

end TriangleNorm
end WeightedObstructionNorms
