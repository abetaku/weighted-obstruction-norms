import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.FieldSimp

/-! Finite weighted maximum norms, including empty coordinate sets.
The real function-space norm is the finite supremum norm. -/
noncomputable section
open Set
namespace WeightedObstructionNorms

variable {J : Type*} [Fintype J]

def weightedNorm (w x : J → ℝ) : ℝ := ‖fun j => x j / w j‖

lemma weightedNorm_nonneg (w x : J → ℝ) : 0 ≤ weightedNorm w x := norm_nonneg _

lemma weightedNorm_zero (w : J → ℝ) : weightedNorm w 0 = 0 := by
  simp only [weightedNorm, Pi.zero_apply, zero_div]
  exact norm_zero

lemma continuous_weightedNorm (w : J → ℝ) : Continuous (weightedNorm w) := by
  exact (continuous_pi fun j => (continuous_apply j).div_const (w j)).norm

lemma weightedNorm_le_iff {w x : J → ℝ} (hw : ∀ j, 0 < w j) {L : ℝ}
    (hL : 0 ≤ L) : weightedNorm w x ≤ L ↔ ∀ j, |x j| ≤ L * w j := by
  rw [weightedNorm, pi_norm_le_iff_of_nonneg hL]
  apply forall_congr'
  intro j
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hw j), div_le_iff₀ (hw j)]

lemma coordinate_le_weightedNorm {w x : J → ℝ} (hw : ∀ j, 0 < w j) (j : J) :
    |x j| ≤ weightedNorm w x * w j :=
  (weightedNorm_le_iff hw (weightedNorm_nonneg w x)).1 le_rfl j

lemma weightedNorm_eq_zero_iff {w x : J → ℝ} (hw : ∀ j, 0 < w j) :
    weightedNorm w x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj := coordinate_le_weightedNorm (x := x) hw j
    rw [h, zero_mul] at hj
    exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
  · rintro rfl
    exact weightedNorm_zero w

lemma weightedNorm_add_le {w x y : J → ℝ} :
    weightedNorm w (x + y) ≤ weightedNorm w x + weightedNorm w y := by
  simpa only [weightedNorm, Pi.add_apply, add_div] using
    (norm_add_le (fun j => x j / w j) (fun j => y j / w j))

lemma weightedNorm_smul (w x : J → ℝ) (a : ℝ) :
    weightedNorm w (a • x) = |a| * weightedNorm w x := by
  have heq : (fun j => (a • x) j / w j) = a • (fun j => x j / w j) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [weightedNorm, heq, norm_smul, Real.norm_eq_abs]
  rfl

lemma weightedNorm_scale_weights (w x : J → ℝ) {t : ℝ} (ht : 0 < t) :
    weightedNorm (fun j => t * w j) x = weightedNorm w x / t := by
  have heq : (fun j => x j / (t * w j)) = t⁻¹ • (fun j => x j / w j) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [weightedNorm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  simp only [weightedNorm, div_eq_mul_inv, mul_comm]

lemma weightedNorm_mono_weights {w w' x : J → ℝ}
    (hw : ∀ j, 0 < w j) (hww' : ∀ j, w j ≤ w' j) :
    weightedNorm w' x ≤ weightedNorm w x := by
  have hw' : ∀ j, 0 < w' j := fun j => (hw j).trans_le (hww' j)
  apply (weightedNorm_le_iff hw' (weightedNorm_nonneg _ _)).2
  intro j
  exact (coordinate_le_weightedNorm hw j).trans
    (mul_le_mul_of_nonneg_left (hww' j) (weightedNorm_nonneg _ _))

/-- Compactness/attainment, with no feasibility or coercivity hidden in an axiom. -/
theorem exists_weightedNorm_minimum {w : J → ℝ} (hw : ∀ j, 0 < w j)
    {s : Set (J → ℝ)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, weightedNorm w x ≤ weightedNorm w y := by
  obtain ⟨x₀, hx₀⟩ := hne
  let M := weightedNorm w x₀
  let K := s ∩ {x | weightedNorm w x ≤ M}
  have hKclosed : IsClosed K := hs.inter (isClosed_le (continuous_weightedNorm w) continuous_const)
  have hKcompact : IsCompact K := by
    apply (isCompact_Icc : IsCompact (Icc (fun j => -(M * w j)) (fun j => M * w j))).of_isClosed_subset hKclosed
    intro x hx
    have hb := (weightedNorm_le_iff hw (weightedNorm_nonneg w x₀)).1 hx.2
    exact ⟨fun j => (abs_le.mp (hb j)).1, fun j => (abs_le.mp (hb j)).2⟩
  obtain ⟨x, hx, hmin⟩ := hKcompact.exists_isMinOn
    (show K.Nonempty from ⟨x₀, hx₀, by dsimp [M]; exact le_rfl⟩) (continuous_weightedNorm w).continuousOn
  refine ⟨x, hx.1, ?_⟩
  intro y hy
  by_cases hb : weightedNorm w y ≤ M
  · exact hmin ⟨hy, hb⟩
  · exact hx.2.trans (le_of_not_ge hb)

end WeightedObstructionNorms
