import Mathlib.Analysis.Normed.Module.FiniteDimension
import WeightedObstructionNorms.Minimum

noncomputable section
open Set
namespace WeightedObstructionNorms

variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Coordinates in the original support and newly available coordinates. -/
structure LinearProblem (J₀ J₁ B : Type*) [Fintype J₀] [Fintype J₁]
    [NormedAddCommGroup B] [NormedSpace ℝ B] where
  A₀ : (J₀ → ℝ) →ₗ[ℝ] B
  A₁ : (J₁ → ℝ) →ₗ[ℝ] B
  b : B
  feasible : ∃ u v, A₀ u + A₁ v = b

namespace LinearProblem
variable (P : LinearProblem J₀ J₁ B)

def quotientFeasible : Set (J₁ → ℝ) := {v | P.b - P.A₁ v ∈ LinearMap.range P.A₀}

def fullFeasible : Set (J₀ ⊕ J₁ → ℝ) :=
  {x | P.A₀ (fun j => x (.inl j)) + P.A₁ (fun j => x (.inr j)) = P.b}

def coefficient (r : J₁ → ℝ) : ℝ := minimum r P.quotientFeasible

def gamma (w₀ : J₀ → ℝ) (w₁ : J₁ → ℝ) : ℝ :=
  minimum (Sum.elim w₀ w₁) P.fullFeasible

lemma quotientFeasible_iff (v : J₁ → ℝ) :
    v ∈ P.quotientFeasible ↔ ∃ u, P.A₀ u + P.A₁ v = P.b := by
  change (∃ u, P.A₀ u = P.b - P.A₁ v) ↔ _
  simp only [eq_sub_iff_add_eq]

lemma quotientFeasible_nonempty : P.quotientFeasible.Nonempty := by
  obtain ⟨u, v, h⟩ := P.feasible
  exact ⟨v, (P.quotientFeasible_iff v).2 ⟨u, h⟩⟩

lemma fullFeasible_nonempty : P.fullFeasible.Nonempty := by
  obtain ⟨u, v, h⟩ := P.feasible
  exact ⟨Sum.elim u v, h⟩

lemma quotientFeasible_closed : IsClosed P.quotientFeasible := by
  exact (LinearMap.range P.A₀).closed_of_finiteDimensional.preimage
    (continuous_const.sub P.A₁.continuous_of_finiteDimensional)

lemma fullFeasible_closed : IsClosed P.fullFeasible := by
  apply isClosed_eq _ continuous_const
  exact (P.A₀.continuous_of_finiteDimensional.comp
    (continuous_pi fun j => continuous_apply (Sum.inl j : J₀ ⊕ J₁))).add
    (P.A₁.continuous_of_finiteDimensional.comp
      (continuous_pi fun j => continuous_apply (Sum.inr j : J₀ ⊕ J₁)))

lemma coefficient_nonneg (r : J₁ → ℝ) : 0 ≤ P.coefficient r :=
  minimum_nonneg P.quotientFeasible_nonempty

lemma coefficient_attained {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    ∃ v ∈ P.quotientFeasible, weightedNorm r v = P.coefficient r :=
  minimum_attained hr P.quotientFeasible_closed P.quotientFeasible_nonempty

lemma gamma_attained {w₀ : J₀ → ℝ} {w₁ : J₁ → ℝ}
    (h₀ : ∀ j, 0 < w₀ j) (h₁ : ∀ j, 0 < w₁ j) :
    ∃ x ∈ P.fullFeasible, weightedNorm (Sum.elim w₀ w₁) x = P.gamma w₀ w₁ := by
  apply minimum_attained _ P.fullFeasible_closed P.fullFeasible_nonempty
  exact Sum.rec h₀ h₁

/-- The positivity assertion of Theorem 3.1, including attained zero. -/
theorem coefficient_eq_zero_iff {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    P.coefficient r = 0 ↔ P.b ∈ LinearMap.range P.A₀ := by
  constructor
  · intro h
    obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr
    have hz : v = 0 := (weightedNorm_eq_zero_iff hr).1 (hmin.trans h)
    simpa [quotientFeasible, hz] using hv
  · intro h
    have hz : (0 : J₁ → ℝ) ∈ P.quotientFeasible := by simpa [quotientFeasible] using h
    exact le_antisymm (by simpa [coefficient, weightedNorm_zero] using (minimum_le (w := r) hz))
      (P.coefficient_nonneg r)

lemma coefficient_pos_iff {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    0 < P.coefficient r ↔ P.b ∉ LinearMap.range P.A₀ := by
  rw [lt_iff_le_and_ne]
  simp only [P.coefficient_nonneg r, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    P.coefficient_eq_zero_iff hr]

/-- Lower bound for every feasible primitive, before minimizing. -/
lemma reciprocal_lower_pointwise {r : J₁ → ℝ} (hr : ∀ j, 0 < r j)
    {w₀ : J₀ → ℝ} (h₀ : ∀ j, 0 < w₀ j) {t : ℝ} (ht : 0 < t)
    {x : J₀ ⊕ J₁ → ℝ} (hx : x ∈ P.fullFeasible) :
    P.coefficient r / t ≤ weightedNorm (Sum.elim w₀ (fun j => t * r j)) x := by
  let L := weightedNorm (Sum.elim w₀ (fun j => t * r j)) x
  have hL : 0 ≤ L := weightedNorm_nonneg _ _
  have hv : (fun j => x (.inr j)) ∈ P.quotientFeasible :=
    (P.quotientFeasible_iff _).2 ⟨fun j => x (.inl j), hx⟩
  have hvbound : weightedNorm r (fun j => x (.inr j)) ≤ t * L := by
    apply (weightedNorm_le_iff hr (mul_nonneg ht.le hL)).2
    intro j
    have h := coordinate_le_weightedNorm
      (x := x) (w := Sum.elim w₀ (fun j => t * r j)) (Sum.rec h₀ (fun j => mul_pos ht (hr j))) (.inr j)
    dsimp at h
    dsimp [L]
    nlinarith [h]
  exact (div_le_iff₀ ht).2 (by
    have hk : P.coefficient r ≤ weightedNorm r (fun j => x (.inr j)) := minimum_le hv
    nlinarith)

lemma reciprocal_lower {r : J₁ → ℝ} (hr : ∀ j, 0 < r j)
    {w₀ : J₀ → ℝ} (h₀ : ∀ j, 0 < w₀ j) {t : ℝ} (ht : 0 < t) :
    P.coefficient r / t ≤ P.gamma w₀ (fun j => t * r j) :=
  le_minimum P.fullFeasible_nonempty (fun _ hx => P.reciprocal_lower_pointwise hr h₀ ht hx)

/-- Exact saturation once an optimal new-coordinate vector has a bounded old lift. -/
theorem reciprocal_eq_of_lift {r : J₁ → ℝ} (hr : ∀ j, 0 < r j)
    {w₀ : J₀ → ℝ} (h₀ : ∀ j, 0 < w₀ j) {t : ℝ} (ht : 0 < t)
    {u : J₀ → ℝ} {v : J₁ → ℝ} (hfeas : P.A₀ u + P.A₁ v = P.b)
    (hv : weightedNorm r v = P.coefficient r)
    (hu : ∀ j, |u j| ≤ (P.coefficient r / t) * w₀ j) :
    P.gamma w₀ (fun j => t * r j) = P.coefficient r / t := by
  apply le_antisymm _ (P.reciprocal_lower hr h₀ ht)
  apply (minimum_le (x := Sum.elim u v) hfeas).trans
  apply (weightedNorm_le_iff (Sum.rec h₀ (fun j => mul_pos ht (hr j)))
    (div_nonneg (P.coefficient_nonneg r) ht.le)).2
  intro j
  cases j with
  | inl j => exact hu j
  | inr j =>
    have hb := coordinate_le_weightedNorm (x := v) hr j
    rw [hv] at hb
    dsimp
    rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']
    exact hb

end LinearProblem
end WeightedObstructionNorms
