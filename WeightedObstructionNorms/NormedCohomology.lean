import WeightedObstructionNorms.RelativeWindow

noncomputable section
namespace WeightedObstructionNorms
namespace RelativeWindow
variable {U X V Y Z : Type*} [Fintype U] [Fintype X]
    [Fintype V] [Fintype Y] [Fintype Z] (W : RelativeWindow U X V Y Z)

/-- A type copy carrying the obstruction norm, so that different reference
weights do not install conflicting norm instances on the original quotient. -/
def NormedCohomology (r : X → ℝ) (_hr : ∀ j, 0 < r j) := W.Cohomology

namespace NormedCohomology
variable {W} {r : X → ℝ} {hr : ∀ j, 0 < r j}

instance : AddCommGroup (W.NormedCohomology r hr) := inferInstanceAs (AddCommGroup W.Cohomology)
instance : Module ℝ (W.NormedCohomology r hr) := inferInstanceAs (Module ℝ W.Cohomology)
instance : Norm (W.NormedCohomology r hr) := ⟨W.obstructionValue r⟩

def normCore : NormedSpace.Core ℝ (W.NormedCohomology r hr) where
  norm_nonneg := W.obstruction_nonneg r
  norm_triangle := W.obstruction_add_le hr
  norm_smul a x := by
    change W.obstructionValue r (a • x) = |a| * W.obstructionValue r x
    exact W.obstruction_smul_eq hr a x
  norm_eq_zero_iff := W.obstruction_eq_zero_iff hr

instance : NormedAddCommGroup (W.NormedCohomology r hr) := NormedAddCommGroup.ofCore normCore
instance : NormedSpace ℝ (W.NormedCohomology r hr) := NormedSpace.ofCore normCore
instance : FiniteDimensional ℝ (W.NormedCohomology r hr) :=
  inferInstanceAs (FiniteDimensional ℝ W.Cohomology)

lemma norm_eq (α : W.NormedCohomology r hr) : ‖α‖ = W.obstructionValue r α := rfl

end NormedCohomology

/-- Comparison of reference weights on the actual old cohomology quotient. -/
theorem reference_comparison {r r' : X → ℝ} (hr : ∀ j, 0 < r j) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hl : ∀ j, a * r j ≤ r' j)
    (hu : ∀ j, r' j ≤ b * r j) (α : W.Cohomology) :
    W.obstructionValue r α / b ≤ W.obstructionValue r' α ∧
      W.obstructionValue r' α ≤ W.obstructionValue r α / a := by
  have hr' : ∀ j, 0 < r' j := fun j => (mul_pos ha (hr j)).trans_le (hl j)
  obtain ⟨x, hx, hxmin⟩ := W.obstruction_attained hr α
  obtain ⟨y, hy, hymin⟩ := W.obstruction_attained hr' α
  constructor
  · have hnorm : weightedNorm r y / b ≤ weightedNorm r' y := by
      rw [← weightedNorm_scale_weights r y hb]
      exact weightedNorm_mono_weights hr' hu
    exact (div_le_div_of_nonneg_right (minimum_le hy) hb.le).trans (hnorm.trans_eq hymin)
  · have hnorm : weightedNorm r' x ≤ weightedNorm r x / a := by
      rw [← weightedNorm_scale_weights r x ha]
      exact weightedNorm_mono_weights (fun j => mul_pos ha (hr j)) hl
    exact (minimum_le hx).trans (by simpa [hxmin] using hnorm)

end RelativeWindow
end WeightedObstructionNorms
