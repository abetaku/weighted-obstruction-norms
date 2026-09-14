import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms

/-- Pairwise cancellation for two successive alternating face sums. The
bijection sends (i,j), j ≤ i, to (j,i+1); the latter has the opposite sign. -/
theorem alternating_cancellation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (T : Fin (n + 1) → Fin (n + 2) → V)
    (hT : ∀ i j (h : j.val ≤ i.val),
      T i j = T (j.castLT (lt_of_le_of_lt h i.is_lt)) i.succ) :
    ∑ i, ∑ j, ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val) • T i j = 0 := by
  classical
  let P := Fin (n + 1) × Fin (n + 2)
  let S : Finset P := {ij | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_product', Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (ij.2.castLT (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [S, φ, Finset.mem_univ, Finset.compl_filter, Finset.mem_filter, true_and,
      Fin.val_succ, Fin.coe_castLT] at hij ⊢
    omega
  · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i',j'⟩ hij'
    simp only [S, Finset.mem_univ, forall_true_left, Prod.forall, Finset.compl_filter,
      not_le, Finset.mem_filter, true_and] at hij'
    refine ⟨(j'.pred ?_, i'.castSucc), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero'] at hij'
    · simpa only [S, Finset.mem_univ, forall_true_left, Prod.forall, Finset.mem_filter,
        Fin.coe_castSucc, Fin.coe_pred, true_and] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i,j⟩ hij
    have hji : j.val ≤ i.val := (Finset.mem_filter.mp hij).2
    dsimp [φ]
    rw [hT i j hji, ← neg_smul]
    congr 1
    simp only [Fin.val_succ, Fin.coe_castLT, pow_succ, mul_neg, mul_one, neg_neg]
    exact mul_comm _ _

end WeightedObstructionNorms
