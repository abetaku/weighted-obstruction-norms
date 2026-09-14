import WeightedObstructionNorms.LinearProblem

noncomputable section
namespace WeightedObstructionNorms
namespace LinearProblem
variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  (P : LinearProblem J₀ J₁ B)

/-- The positive-obstruction branch of Theorem 3.1. All minima are the
actual infima of the original coordinate optimization problems; attainment
has already been proved. The threshold is allowed to depend on the datum. -/
theorem affine_reciprocal {w₀ r₀ : J₀ → ℝ} {r₁ : J₁ → ℝ}
    (hw₀ : ∀ j, 0 < w₀ j) (hr₁ : ∀ j, 0 < r₁ j)
    (hk : 0 < P.coefficient r₁) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      (∀ j, 0 < w₀ j + ε * r₀ j) ∧
      P.gamma (fun j => w₀ j + ε * r₀ j) (fun j => ε * r₁ j) =
        P.coefficient r₁ / ε := by
  obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr₁
  obtain ⟨u, hu⟩ := (P.quotientFeasible_iff v).1 hv
  let R := weightedNorm w₀ r₀
  let M := weightedNorm w₀ u
  have hR : 0 ≤ R := weightedNorm_nonneg _ _
  have hM : 0 ≤ M := weightedNorm_nonneg _ _
  let η := min (1 / (2 * (R + 1))) (P.coefficient r₁ / (2 * (M + 1)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro ε hε heη
  have hεR : ε * (2 * (R + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * (R + 1))).1
      (heη.trans (min_le_left _ _))
  have hεM : ε * (2 * (M + 1)) ≤ P.coefficient r₁ :=
    (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).1
      (heη.trans (min_le_right _ _))
  have hεR' : ε * R ≤ 1 / 2 := by nlinarith
  have hεM' : ε * M ≤ P.coefficient r₁ / 2 := by nlinarith
  have hstable : ∀ j, w₀ j / 2 ≤ w₀ j + ε * r₀ j := by
    intro j
    have hj := coordinate_le_weightedNorm (x := r₀) hw₀ j
    change |r₀ j| ≤ R * w₀ j at hj
    have hlow := (abs_le.mp hj).1
    have hmul := mul_le_mul_of_nonneg_left hlow hε.le
    have hprod := mul_le_mul_of_nonneg_right hεR' (hw₀ j).le
    nlinarith
  have hpositive : ∀ j, 0 < w₀ j + ε * r₀ j :=
    fun j => (half_pos (hw₀ j)).trans_le (hstable j)
  refine ⟨hpositive, P.reciprocal_eq_of_lift hr₁ hpositive hε hu hmin ?_⟩
  intro j
  have hj := coordinate_le_weightedNorm (x := u) hw₀ j
  change |u j| ≤ M * w₀ j at hj
  have hMw : ε * |u j| ≤ P.coefficient r₁ * (w₀ j / 2) := by
    have h₁ := mul_le_mul_of_nonneg_left hj hε.le
    have h₂ := mul_le_mul_of_nonneg_right hεM' (hw₀ j).le
    nlinarith
  have hkw := mul_le_mul_of_nonneg_left (hstable j) hk.le
  have hb : |u j| * ε ≤ P.coefficient r₁ * (w₀ j + ε * r₀ j) := by nlinarith
  calc
    |u j| ≤ (P.coefficient r₁ * (w₀ j + ε * r₀ j)) / ε := (le_div_iff₀ hε).2 hb
    _ = (P.coefficient r₁ / ε) * (w₀ j + ε * r₀ j) := by ring

end LinearProblem
end WeightedObstructionNorms
