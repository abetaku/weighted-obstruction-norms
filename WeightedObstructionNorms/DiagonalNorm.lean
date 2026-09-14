import WeightedObstructionNorms.DiagonalCost

noncomputable section
open Filter Topology
namespace WeightedObstructionNorms
namespace DiagonalNorm
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees DiagonalCocycle DiagonalCost

lemma obstruction_norm : CechObstruction.norm E S M (diagonal 0) q₁ 0 obstructionClass = 2 := by
  have h := CechReciprocal.norm_limit E S M (diagonal 0) q₀_nonneg
    (fun z hz => (q₀_positive z).2 hz) q₀_zero q₁_positive 0
    ((CechSplitting.cycleEquiv E S M (diagonal 0) 0).symm cycle)
  have he : (fun ε => ε * CechPrimitive.cost E S M (q ε) 0 c) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => (2 : ℝ)) := by
    have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := Ioc_mem_nhdsGT (by norm_num)
    filter_upwards [hs] with ε hε
    rw [cost_eq hε.1 hε.2]
    field_simp [ne_of_gt hε.1]
  exact tendsto_nhds_unique (h.congr' he) tendsto_const_nhds

lemma obstruction_nonzero : obstructionClass ≠ 0 := by
  intro h
  have hn := obstruction_norm
  rw [h, CechObstruction.norm_zero] at hn
  norm_num at hn

/-- Proposition 6.1 on the actual Cech cohomology, with the uniform reference. -/
theorem norm_multiple (a : ℝ) :
    CechObstruction.norm E S M (diagonal 0) q₁ 0 (a • obstructionClass) = 2*|a| := by
  rw [CechObstruction.norm_smul E S M (diagonal 0) q₁_positive, obstruction_norm]
  ring

lemma unit_ball_multiple (a : ℝ) :
    CechObstruction.norm E S M (diagonal 0) q₁ 0 (a • obstructionClass) ≤ 1 ↔ |a| ≤ 1/2 := by
  rw [norm_multiple]
  constructor <;> intro h <;> linarith

end DiagonalNorm
end WeightedObstructionNorms
