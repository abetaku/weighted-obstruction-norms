import WeightedObstructionNorms.LinearProblem
import Mathlib.Tactic.Abel

noncomputable section
open Set
namespace WeightedObstructionNorms
namespace LinearProblem
variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  (P : LinearProblem J₀ J₁ B)

/-- Coordinate-box form of the coefficient sublevel set. The geometric
application must still identify the quotient equation with a relative cocycle. -/
theorem coefficient_unit_ball {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    P.coefficient r ≤ 1 ↔
      ∃ v, P.b - P.A₁ v ∈ LinearMap.range P.A₀ ∧ ∀ j, |v j| ≤ r j := by
  constructor
  · intro hk
    obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr
    refine ⟨v, hv, ?_⟩
    have h := (weightedNorm_le_iff hr (by norm_num : (0 : ℝ) ≤ 1)).1 (hmin.trans_le hk)
    simpa using h
  · rintro ⟨v, hv, hb⟩
    exact (minimum_le hv).trans ((weightedNorm_le_iff hr (by norm_num)).2 (by simpa using hb))

/-- Add an old-coordinate boundary to the prescribed datum. -/
def shift (u : J₀ → ℝ) : LinearProblem J₀ J₁ B where
  A₀ := P.A₀
  A₁ := P.A₁
  b := P.b + P.A₀ u
  feasible := by
    obtain ⟨x, v, hv⟩ := P.feasible
    refine ⟨x + u, v, ?_⟩
    rw [map_add]
    calc
      P.A₀ x + P.A₀ u + P.A₁ v = (P.A₀ x + P.A₁ v) + P.A₀ u := by abel
      _ = P.b + P.A₀ u := by rw [hv]

lemma shift_quotientFeasible (u : J₀ → ℝ) : (P.shift u).quotientFeasible = P.quotientFeasible := by
  ext v
  rw [(P.shift u).quotientFeasible_iff, P.quotientFeasible_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x - u, ?_⟩
    change P.A₀ x + P.A₁ v = P.b + P.A₀ u at hx
    rw [map_sub]
    calc
      P.A₀ x - P.A₀ u + P.A₁ v = (P.A₀ x + P.A₁ v) - P.A₀ u := by abel
      _ = P.b := by rw [hx]; abel
  · rintro ⟨x, hx⟩
    refine ⟨x + u, ?_⟩
    change P.A₀ (x + u) + P.A₁ v = P.b + P.A₀ u
    rw [map_add]
    calc
      P.A₀ x + P.A₀ u + P.A₁ v = (P.A₀ x + P.A₁ v) + P.A₀ u := by abel
      _ = P.b + P.A₀ u := by rw [hx]

/-- The algebraic representative-independence used in Corollary 3.2. -/
theorem coefficient_shift (u : J₀ → ℝ) (r : J₁ → ℝ) :
    (P.shift u).coefficient r = P.coefficient r := by
  simp only [coefficient, P.shift_quotientFeasible u]

end LinearProblem

/-- Minimum norms contract along maps of feasible sets. This covers the
optimization step of support/observation comparison once its coordinate map
and its norm bound have been proved. -/
theorem minimum_nonexpansive {J K : Type*} [Fintype J] [Fintype K]
    {w : J → ℝ} {w' : K → ℝ} {s : Set (J → ℝ)} {t : Set (K → ℝ)}
    (hs : s.Nonempty) (F : (J → ℝ) → (K → ℝ))
    (hF : ∀ x ∈ s, F x ∈ t)
    (hbound : ∀ x ∈ s, weightedNorm w' (F x) ≤ weightedNorm w x) :
    minimum w' t ≤ minimum w s := by
  apply le_minimum hs
  intro x hx
  exact (minimum_le (hF x hx)).trans (hbound x hx)

end WeightedObstructionNorms
