import WeightedObstructionNorms.QuotientNorm
import WeightedObstructionNorms.LinearProblem
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Group.Quotient

noncomputable section
open Set
open scoped BigOperators
namespace WeightedObstructionNorms
namespace QuotientNorm
variable {J H : Type*} [Fintype J] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A norming algebraic functional for the weighted quotient norm. The norm
used in Hahn--Banach is constructed from the proved minimum-norm axioms. -/
theorem supporting_functional (f : (J → ℝ) →ₗ[ℝ] H) (hf : Function.Surjective f)
    {r : J → ℝ} (hr : ∀ j, 0 < r j) (b : H) :
    ∃ a : H →ₗ[ℝ] ℝ, a b = value f r b ∧ ∀ y, |a y| ≤ value f r y := by
  letI moduleH : Module ℝ H := inferInstance
  let N : H → ℝ := value f r
  have hn := nonneg f hf r
  have hz := eq_zero_iff f hf hr
  have ha := add_le f hf hr
  have hs := smul_eq f hf hr
  letI : Norm H := ⟨N⟩
  have core : NormedSpace.Core ℝ H :=
    { norm_nonneg := hn
      norm_smul := by intro c x; change N (c • x) = |c| * N x; exact hs c x
      norm_triangle := ha
      norm_eq_zero_iff := hz }
  letI : NormedAddCommGroup H := NormedAddCommGroup.ofCore core
  letI : NormedSpace ℝ H := NormedSpace.ofCore core
  obtain ⟨a, ha, hb⟩ := exists_dual_vector'' ℝ b
  refine ⟨a.toLinearMap, hb, ?_⟩
  intro y
  exact (a.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg y))

end QuotientNorm

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma linear_coordinate_expansion (a : (J → ℝ) →ₗ[ℝ] ℝ) (x : J → ℝ) :
    a x = ∑ j, x j * a (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • (Pi.single j 1 : J → ℝ) := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul]

lemma linear_weighted_bound (a : (J → ℝ) →ₗ[ℝ] ℝ) {r : J → ℝ}
    (hr : ∀ j, 0 < r j) (x : J → ℝ) :
    |a x| ≤ (∑ j, r j * |a (Pi.single j 1)|) * weightedNorm r x := by
  classical
  rw [linear_coordinate_expansion]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_right (coordinate_le_weightedNorm hr j (x := x))
    (abs_nonneg (a (Pi.single j 1)))
  nlinarith

/-- Weighted infinity/l1 duality, with the empty index set allowed. -/
theorem linear_box_dual_iff (a : (J → ℝ) →ₗ[ℝ] ℝ) {r : J → ℝ}
    (hr : ∀ j, 0 < r j) :
    (∀ x, |a x| ≤ weightedNorm r x) ↔ ∑ j, r j * |a (Pi.single j 1)| ≤ 1 := by
  classical
  constructor
  · intro h
    let x : J → ℝ := fun j => if 0 ≤ a (Pi.single j 1) then r j else -r j
    have hx : weightedNorm r x ≤ 1 := by
      apply (weightedNorm_le_iff hr (by norm_num)).2
      intro j
      dsimp [x]
      split_ifs <;> simp [abs_of_pos (hr j)]
    have heq : a x = ∑ j, r j * |a (Pi.single j 1)| := by
      rw [linear_coordinate_expansion]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [x]
      split_ifs with hj
      · rw [abs_of_nonneg hj]
      · rw [abs_of_neg (lt_of_not_ge hj)]
        ring
    rw [← heq]
    exact (le_abs_self _).trans ((h x).trans hx)
  · intro h x
    exact (linear_weighted_bound a hr x).trans
      (by simpa using mul_le_mul_of_nonneg_right h (weightedNorm_nonneg r x))

namespace LinearProblem
variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁] [DecidableEq J₁]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (P : LinearProblem J₀ J₁ B)

/-- Algebraic transpose constraints of the manuscript. -/
def dualFeasible (r : J₁ → ℝ) : Set (B →ₗ[ℝ] ℝ) :=
  {a | (∀ u, a (P.A₀ u) = 0) ∧ ∑ j, r j * |a (P.A₁ (Pi.single j 1))| ≤ 1}

lemma dual_weak_bound {r : J₁ → ℝ} (hr : ∀ j, 0 < r j)
    {a : B →ₗ[ℝ] ℝ} (ha : a ∈ P.dualFeasible r) : a P.b ≤ P.coefficient r := by
  apply le_minimum P.quotientFeasible_nonempty
  intro v hv
  obtain ⟨u, hu⟩ := (P.quotientFeasible_iff v).1 hv
  have hab : a P.b = a (P.A₁ v) := by rw [← hu, map_add, ha.1, zero_add]
  rw [hab]
  exact (le_abs_self _).trans ((linear_box_dual_iff (a.comp P.A₁) hr).2 ha.2 v)

/-- A maximizer for the dual problem, including zero obstruction. -/
theorem dual_attained {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    ∃ a ∈ P.dualFeasible r, a P.b = P.coefficient r := by
  let O := LinearMap.range P.A₀
  letI : IsClosed (O : Set B) := O.closed_of_finiteDimensional
  let Q := B ⧸ O
  let π : B →ₗ[ℝ] Q := O.mkQ
  let F : (J₁ → ℝ) →ₗ[ℝ] Q := π.comp P.A₁
  let H := LinearMap.range F
  let f : (J₁ → ℝ) →ₗ[ℝ] H := F.rangeRestrict
  obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr
  obtain ⟨u, hu⟩ := (P.quotientFeasible_iff v).1 hv
  have hπ : π P.b = F v := by
    rw [← hu, map_add]
    have hz : π (P.A₀ u) = 0 := (Submodule.Quotient.mk_eq_zero O).2 ⟨u, rfl⟩
    rw [hz, zero_add]
    rfl
  have hset : {x | f x = f v} = P.quotientFeasible := by
    ext x
    change f x = f v ↔ _
    rw [P.quotientFeasible_iff]
    constructor
    · intro hx
      have heq : π P.b = π (P.A₁ x) := hπ.trans (congrArg Subtype.val hx).symm
      have hm : P.b - P.A₁ x ∈ O := (Submodule.Quotient.eq O).1 heq
      obtain ⟨y, hy⟩ := hm
      exact ⟨y, (eq_sub_iff_add_eq).1 hy⟩
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      change π (P.A₁ x) = F v
      rw [← hπ, ← hy, map_add]
      have hz : π (P.A₀ y) = 0 := (Submodule.Quotient.mk_eq_zero O).2 ⟨y, rfl⟩
      rw [hz, zero_add]
  have hval : QuotientNorm.value f r (f v) = P.coefficient r := by
    unfold QuotientNorm.value coefficient
    rw [hset]
  obtain ⟨ℓ, hℓ, hbound⟩ := QuotientNorm.supporting_functional f F.surjective_rangeRestrict hr (f v)
  obtain ⟨p, hp⟩ := H.subtype.exists_leftInverse_of_injective H.ker_subtype
  let a : B →ₗ[ℝ] ℝ := ℓ.comp (p.comp π)
  have hpF (x : J₁ → ℝ) : p (F x) = f x := LinearMap.congr_fun hp (f x)
  have haF (x : J₁ → ℝ) : a (P.A₁ x) = ℓ (f x) := congrArg ℓ (hpF x)
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · intro y
    have hz : π (P.A₀ y) = 0 := (Submodule.Quotient.mk_eq_zero O).2 ⟨y, rfl⟩
    change ℓ (p (π (P.A₀ y))) = 0
    rw [hz, map_zero, map_zero]
  · apply (linear_box_dual_iff (a.comp P.A₁) hr).1
    intro x
    change |a (P.A₁ x)| ≤ weightedNorm r x
    rw [haF]
    exact (hbound (f x)).trans (minimum_le (show x ∈ {y | f y = f x} from rfl))
  · change ℓ (p (π P.b)) = P.coefficient r
    rw [hπ, hpF, hℓ, hval]

/-- The supremum formula of Theorem 3.1, in fact attained as a maximum. -/
theorem dual_formula {r : J₁ → ℝ} (hr : ∀ j, 0 < r j) :
    P.coefficient r = sSup ((fun a : B →ₗ[ℝ] ℝ => a P.b) '' P.dualFeasible r) := by
  let S : Set ℝ := (fun a : B →ₗ[ℝ] ℝ => a P.b) '' P.dualFeasible r
  change P.coefficient r = sSup S
  obtain ⟨a, ha, hval⟩ := P.dual_attained hr
  have hmem : a P.b ∈ S := ⟨a, ha, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨P.coefficient r, ?_⟩
    rintro x ⟨a', ha', rfl⟩
    exact P.dual_weak_bound hr ha'
  apply le_antisymm
  · rw [← hval]
    exact le_csSup hbdd hmem
  · apply csSup_le (show S.Nonempty from ⟨_, hmem⟩)
    rintro x ⟨a', ha', rfl⟩
    exact P.dual_weak_bound hr ha'

end LinearProblem
end WeightedObstructionNorms
