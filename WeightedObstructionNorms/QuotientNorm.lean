import Mathlib.Analysis.Normed.Module.FiniteDimension
import WeightedObstructionNorms.Minimum

/-! Quotient-norm results for a surjective linear map. The application to a
relative connecting map still requires constructing that map and identifying
its finite coordinate domain; these hypotheses are not asserted here. -/
noncomputable section
open Set
namespace WeightedObstructionNorms
namespace QuotientNorm
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [NormedSpace ℝ H]

def value (f : (J → ℝ) →ₗ[ℝ] H) (w : J → ℝ) (b : H) : ℝ :=
  minimum w {x | f x = b}

lemma attained (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (b : H) :
    ∃ x, f x = b ∧ weightedNorm w x = value f w b :=
  minimum_attained hw (isClosed_eq f.continuous_of_finiteDimensional continuous_const) (hf b)

lemma nonneg (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f) (w : J → ℝ) (b : H) :
    0 ≤ value f w b := minimum_nonneg (hf b)

lemma zero (f : (J → ℝ) →ₗ[ℝ] H) (w : J → ℝ) : value f w 0 = 0 := by
  have hz : (0 : J → ℝ) ∈ {x | f x = 0} := map_zero f
  exact le_antisymm (by simpa [value, weightedNorm_zero] using (minimum_le (w := w) hz))
    (minimum_nonneg ⟨0, hz⟩)

lemma eq_zero_iff (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (b : H) : value f w b = 0 ↔ b = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx, hmin⟩ := attained f hf hw b
    have hzero := (weightedNorm_eq_zero_iff hw).1 (hmin.trans h)
    simpa [hzero] using hx.symm
  · rintro rfl
    exact zero f w

lemma add_le (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (a b : H) :
    value f w (a + b) ≤ value f w a + value f w b := by
  obtain ⟨x, hx, hxmin⟩ := attained f hf hw a
  obtain ⟨y, hy, hymin⟩ := attained f hf hw b
  have hxy : x + y ∈ {z | f z = a + b} := by simp [hx, hy]
  exact (minimum_le hxy).trans (by simpa [hxmin, hymin] using (weightedNorm_add_le (w := w) (x := x) (y := y)))

lemma smul_le (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (a : ℝ) (b : H) :
    value f w (a • b) ≤ |a| * value f w b := by
  obtain ⟨x, hx, hmin⟩ := attained f hf hw b
  have hax : a • x ∈ {z | f z = a • b} := by simp [hx]
  exact (minimum_le hax).trans_eq (by rw [weightedNorm_smul, hmin])

lemma smul_eq (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (a : ℝ) (b : H) :
    value f w (a • b) = |a| * value f w b := by
  by_cases ha : a = 0
  · simp [ha, zero]
  apply le_antisymm (smul_le f hf hw a b)
  have h := smul_le f hf hw a⁻¹ (a • b)
  rw [inv_smul_smul₀ ha, abs_inv] at h
  have h' := mul_le_mul_of_nonneg_left h (abs_nonneg a)
  simpa [mul_assoc, abs_ne_zero.mpr ha] using h'

/-- Image-of-box formula for the unit ball, including attainment. -/
theorem unit_ball (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w : J → ℝ} (hw : ∀ j, 0 < w j) (b : H) :
    value f w b ≤ 1 ↔ ∃ x, f x = b ∧ ∀ j, |x j| ≤ w j := by
  constructor
  · intro hb
    obtain ⟨x, hx, hmin⟩ := attained f hf hw b
    refine ⟨x, hx, ?_⟩
    have h := (weightedNorm_le_iff hw (by norm_num : (0 : ℝ) ≤ 1)).1 (hmin.trans_le hb)
    simpa using h
  · rintro ⟨x, hx, hb⟩
    exact (minimum_le hx).trans ((weightedNorm_le_iff hw (by norm_num)).2 (by simpa using hb))

/-- Weighted reference-law comparison, before specializing to marginals. -/
theorem reference_comparison (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {w w' : J → ℝ} (hw : ∀ j, 0 < w j) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hl : ∀ j, a * w j ≤ w' j)
    (hu : ∀ j, w' j ≤ b * w j) (c : H) :
    value f w c / b ≤ value f w' c ∧ value f w' c ≤ value f w c / a := by
  have hw' : ∀ j, 0 < w' j := fun j => (mul_pos ha (hw j)).trans_le (hl j)
  obtain ⟨x, hx, hxmin⟩ := attained f hf hw c
  obtain ⟨y, hy, hymin⟩ := attained f hf hw' c
  constructor
  · have hnorm : weightedNorm w y / b ≤ weightedNorm w' y := by
      rw [← weightedNorm_scale_weights w y hb]
      exact weightedNorm_mono_weights hw' hu
    exact (div_le_div_of_nonneg_right (minimum_le hy) hb.le).trans (hnorm.trans_eq hymin)
  · have hnorm : weightedNorm w' x ≤ weightedNorm w x / a := by
      rw [← weightedNorm_scale_weights w x ha]
      exact weightedNorm_mono_weights (fun j => mul_pos ha (hw j)) hl
    exact (minimum_le hx).trans (by simpa [hxmin] using hnorm)

end QuotientNorm
end WeightedObstructionNorms
