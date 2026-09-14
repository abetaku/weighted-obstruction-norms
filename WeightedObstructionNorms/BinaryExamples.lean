import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic

/-! Exact real inequalities behind Section 6. These scalar optimization
lemmas do not by themselves establish the cohomology identifications. -/
noncomputable section
namespace WeightedObstructionNorms
namespace BinaryExamples

/-- The degree-zero relative two-coordinate minimization, Section 6.1. -/
theorem diagonal_lower {a s t : ℝ} (h : s - t = a) :
    2 * |a| ≤ 4 * max |s| |t| := by
  have habs : |a| ≤ |s| + |t| := by rw [← h]; exact abs_sub s t
  have hs := le_max_left |s| |t|
  have ht := le_max_right |s| |t|
  linarith

lemma diagonal_witness (a : ℝ) :
    a / 2 - (-a / 2) = a ∧ 4 * max |a / 2| |(-a / 2)| = 2 * |a| := by
  constructor
  · ring
  · simp [abs_div, abs_neg]
    ring

/-- Attained minimum, stated without an ambiguous infimum over an empty set. -/
theorem diagonal_minimum (a : ℝ) :
    (∃ s t : ℝ, s - t = a ∧ 4 * max |s| |t| = 2 * |a|) ∧
    (∀ s t : ℝ, s - t = a → 2 * |a| ≤ 4 * max |s| |t|) := by
  exact ⟨⟨a / 2, -a / 2, diagonal_witness a⟩, fun _ _ h => diagonal_lower h⟩

/-- Sharp lower bound derived from the moment conditions in Section 6.2. -/
theorem triangle_moment_lower {ε L a b t : ℝ} (hε : 0 < ε)
    (hb : |b| ≤ L) (hb' : |b + 2| ≤ L)
    (h₁ : |a - b| ≤ ε * L) (h₂ : |b + 2 - t| ≤ ε * L)
    (h₃ : |t - a| ≤ ε * L) : max 1 (2 / (3 * ε)) ≤ L := by
  apply max_le
  · have hb₀ := (abs_le.mp hb).1
    have hb₁ := (abs_le.mp hb').2
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 3 * ε)).2
    have h₁' := (abs_le.mp h₁).2
    have h₂' := (abs_le.mp h₂).2
    have h₃' := (abs_le.mp h₃).2
    nlinarith

/-- Norm of the zero-total-mass signed pair measure with moments (u,v). -/
def pairCost (ε u v : ℝ) : ℝ := max (|u + v| / (2 - ε)) (|u - v| / ε)

def tripleCost (ε a b t : ℝ) : ℝ :=
  max (pairCost ε a b) (max (pairCost ε (b + 2) t) (pairCost ε a t))

lemma pairCost_le_iff {ε u v L : ℝ} (hε : 0 < ε) (hε₂ : ε < 2) :
    pairCost ε u v ≤ L ↔ |u + v| ≤ L * (2 - ε) ∧ |u - v| ≤ L * ε := by
  simp only [pairCost, max_le_iff, div_le_iff₀ hε, div_le_iff₀ (sub_pos.mpr hε₂)]

/-- Explicit low-parameter witness from the paper, including the crossover. -/
theorem triangle_small_witness {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 2 / 3) :
    tripleCost ε (-1 / 3) (-1) (1 / 3) ≤ 2 / (3 * ε) := by
  have hε₂ : ε < 2 := by linarith
  have hcancel : (2 / (3 * ε)) * ε = 2 / 3 := by field_simp; ring
  have hdiag : (4 : ℝ) / 3 ≤ (2 / (3 * ε)) * (2 - ε) := by
    have heq : (2 / (3 * ε)) * (3 * ε) = 2 := div_mul_cancel₀ _ (by positivity)
    have hp : 0 < 2 / (3 * ε) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsmall hp.le
    nlinarith
  have hoff : (2 : ℝ) / 3 ≤ (2 / (3 * ε)) * ε := hcancel.ge
  unfold tripleCost
  apply max_le
  · apply (pairCost_le_iff hε hε₂).2
    norm_num
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] using And.intro hdiag hoff
  · apply max_le
    · apply (pairCost_le_iff hε hε₂).2
      norm_num
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] using And.intro hdiag hoff
    · apply (pairCost_le_iff hε hε₂).2
      norm_num
      constructor
      · positivity
      · simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] using hoff

/-- Explicit high-parameter witness; no numerical optimization is used. -/
theorem triangle_large_witness {ε : ℝ} (hε : 0 < ε) (hlarge : 2 / 3 ≤ ε)
    (hε₁ : ε ≤ 1) : tripleCost ε (-(1 - ε)) (-1) (1 - ε) ≤ 1 := by
  have hε₂ : ε < 2 := by linarith
  unfold tripleCost
  apply max_le
  · apply (pairCost_le_iff hε hε₂).2
    rw [abs_le, abs_le]
    constructor <;> constructor <;> nlinarith
  · apply max_le
    · apply (pairCost_le_iff hε hε₂).2
      rw [abs_le, abs_le]
      constructor <;> constructor <;> nlinarith
    · apply (pairCost_le_iff hε hε₂).2
      rw [abs_le, abs_le]
      constructor <;> constructor <;> nlinarith


lemma pair_moments_le {ε u v L : ℝ} (hε : 0 < ε) (hε₂ : ε < 2)
    (h : pairCost ε u v ≤ L) : |u| ≤ L ∧ |v| ≤ L := by
  obtain ⟨hs, hd⟩ := (pairCost_le_iff hε hε₂).1 h
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

lemma triangle_cost_lower {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (a b t : ℝ) :
    max 1 (2 / (3 * ε)) ≤ tripleCost ε a b t := by
  let L := tripleCost ε a b t
  have hε₂ : ε < 2 := by linarith
  have hx : pairCost ε a b ≤ L := le_max_left _ _
  have hy : pairCost ε (b + 2) t ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hz : pairCost ε a t ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hb := (pair_moments_le hε hε₂ hx).2
  have hb' := (pair_moments_le hε hε₂ hy).1
  have h₁ := ((pairCost_le_iff hε hε₂).1 hx).2
  have h₂ := ((pairCost_le_iff hε hε₂).1 hy).2
  have h₃ := ((pairCost_le_iff hε hε₂).1 hz).2
  apply triangle_moment_lower hε hb hb'
  · simpa [mul_comm] using h₁
  · simpa [mul_comm] using h₂
  · simpa [abs_sub_comm, mul_comm] using h₃

/-- Exact attained minimum of the real moment optimization in Section 6.2. -/
theorem triangle_moment_minimum {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∃ a b t : ℝ, tripleCost ε a b t = max 1 (2 / (3 * ε))) ∧
    (∀ a b t : ℝ, max 1 (2 / (3 * ε)) ≤ tripleCost ε a b t) := by
  refine ⟨?_, triangle_cost_lower hε hε₁⟩
  by_cases hs : ε ≤ 2 / 3
  · refine ⟨-1 / 3, -1, 1 / 3, le_antisymm ?_ (triangle_cost_lower hε hε₁ _ _ _)⟩
    exact (triangle_small_witness hε hs).trans (le_max_right _ _)
  · refine ⟨-(1 - ε), -1, 1 - ε, le_antisymm ?_ (triangle_cost_lower hε hε₁ _ _ _)⟩
    exact (triangle_large_witness hε (le_of_not_ge hs) hε₁).trans (le_max_left _ _)


/-- Pair coordinates ordered (++,+-,-+,--), exactly as in Section 6.2. -/
structure PairMeasure where
  pp : ℝ
  pm : ℝ
  mp : ℝ
  mm : ℝ

structure TriangleMeasure where
  x12 : PairMeasure
  x23 : PairMeasure
  x13 : PairMeasure

def PairBox (ε L : ℝ) (x : PairMeasure) : Prop :=
  |x.pp| ≤ L * (2 - ε) / 4 ∧ |x.pm| ≤ L * ε / 4 ∧
  |x.mp| ≤ L * ε / 4 ∧ |x.mm| ≤ L * (2 - ε) / 4

def TriangleBox (ε L : ℝ) (x : TriangleMeasure) : Prop :=
  PairBox ε L x.x12 ∧ PairBox ε L x.x23 ∧ PairBox ε L x.x13

/-- All six signed marginal equations, without a zero-mass restriction. -/
def TriangleFeasible (x : TriangleMeasure) : Prop :=
  (x.x23.pp + x.x23.pm) - (x.x12.pp + x.x12.mp) = 1 ∧
  (x.x23.mp + x.x23.mm) - (x.x12.pm + x.x12.mm) = -1 ∧
  (x.x13.pp + x.x13.pm) - (x.x12.pp + x.x12.pm) = 0 ∧
  (x.x13.mp + x.x13.mm) - (x.x12.mp + x.x12.mm) = 0 ∧
  (x.x13.pp + x.x13.mp) - (x.x23.pp + x.x23.mp) = 0 ∧
  (x.x13.pm + x.x13.mm) - (x.x23.pm + x.x23.mm) = 0

def fromMoments (u v : ℝ) : PairMeasure :=
  ⟨(u + v) / 4, (u - v) / 4, (-u + v) / 4, (-u - v) / 4⟩

def triangleFromMoments (a b t : ℝ) : TriangleMeasure :=
  ⟨fromMoments a b, fromMoments (b + 2) t, fromMoments a t⟩

lemma triangleFromMoments_feasible (a b t : ℝ) :
    TriangleFeasible (triangleFromMoments a b t) := by
  dsimp [TriangleFeasible, triangleFromMoments, fromMoments]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma pairBox_fromMoments {ε L u v : ℝ} (hε : 0 < ε) (hε₂ : ε < 2)
    (h : pairCost ε u v ≤ L) : PairBox ε L (fromMoments u v) := by
  obtain ⟨hs, hd⟩ := (pairCost_le_iff hε hε₂).1 h
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd
  dsimp [PairBox, fromMoments]
  rw [abs_le, abs_le, abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

lemma triangleBox_fromMoments {ε L a b t : ℝ} (hε : 0 < ε) (hε₂ : ε < 2)
    (h : tripleCost ε a b t ≤ L) : TriangleBox ε L (triangleFromMoments a b t) := by
  obtain ⟨hx, hrest⟩ := max_le_iff.mp h
  obtain ⟨hy, hz⟩ := max_le_iff.mp hrest
  exact ⟨pairBox_fromMoments hε hε₂ hx, pairBox_fromMoments hε hε₂ hy,
    pairBox_fromMoments hε hε₂ hz⟩

/-- Lower bounds for all 12 real entries, including nonzero-total-mass primitives. -/
theorem triangle_full_lower {ε L : ℝ} (hε : 0 < ε) {x : TriangleMeasure}
    (hf : TriangleFeasible x) (hb : TriangleBox ε L x) : max 1 (2 / (3 * ε)) ≤ L := by
  obtain ⟨f₁, f₂, f₃, f₄, f₅, f₆⟩ := hf
  obtain ⟨⟨xpp, xpm, xmp, xmm⟩, ⟨ypp, ypm, ymp, ymm⟩, ⟨zpp, zpm, zmp, zmm⟩⟩ := hb
  apply max_le
  · have h₁ := (abs_le.mp xpp).1
    have h₂ := (abs_le.mp xmp).1
    have h₃ := (abs_le.mp ypp).2
    have h₄ := (abs_le.mp ypm).2
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 3 * ε)).2
    have h₁ := (abs_le.mp xpm).2
    have h₂ := (abs_le.mp xmp).1
    have h₃ := (abs_le.mp ypm).2
    have h₄ := (abs_le.mp ymp).1
    have h₅ := (abs_le.mp zpm).1
    have h₆ := (abs_le.mp zmp).2
    nlinarith

/-- Exact box-feasibility threshold for the complete 12-coordinate system
of Proposition 6.2. This is stronger than testing individual ε values. -/
theorem triangle_full_threshold {ε L : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∃ x : TriangleMeasure, TriangleFeasible x ∧ TriangleBox ε L x) ↔
      max 1 (2 / (3 * ε)) ≤ L := by
  constructor
  · rintro ⟨x, hf, hb⟩
    exact triangle_full_lower hε hf hb
  · intro hL
    obtain ⟨⟨a, b, t, heq⟩, _⟩ := triangle_moment_minimum hε hε₁
    exact ⟨triangleFromMoments a b t, triangleFromMoments_feasible a b t,
      triangleBox_fromMoments hε (by linarith) (heq.trans_le hL)⟩

end BinaryExamples
end WeightedObstructionNorms
