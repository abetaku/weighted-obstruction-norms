import WeightedObstructionNorms.CechAllDegrees
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Order

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace SimplexContraction
open CechAllDegrees
section General
variable {K V : Type*} [PartialOrder K] [OrderBot K] [AddCommGroup V] [Module ℝ V]

abbrev Cochain (n : ℕ) := Tuple (K := K) n → V

def positive {n : ℕ} (t : Tuple (K := K) n) : Prop := ∀ i, (⊥ : K) < t i

def prepend {n : ℕ} (t : Tuple (K := K) n) (ht : positive t) : Tuple (K := K) (n + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons ⊥ t) (by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact False.elim (lt_irrefl _ hab)
      | succ b => exact ht b
    | succ a =>
      cases b using Fin.cases with
      | zero => exact False.elim (Fin.not_lt_zero _ hab)
      | succ b => exact t.strictMono (Fin.succ_lt_succ_iff.mp hab))

lemma face_zero_prepend {n : ℕ} (t : Tuple (K := K) n) (ht : positive t) :
    face 0 (prepend t ht) = t := by
  ext i
  rfl

lemma positive_face {n : ℕ} (t : Tuple (K := K) (n + 1)) (ht : positive t) (i : Fin (n + 1)) :
    positive (face i t) := fun j => ht (i.succAbove j)

lemma face_succ_prepend {n : ℕ} (t : Tuple (K := K) (n + 1)) (ht : positive t) (i : Fin (n + 1)) :
    face i.succ (prepend t ht) = prepend (face i t) (positive_face t ht i) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [face, prepend]
  | succ j => simp [face, prepend, Fin.succ_succAbove_succ]

lemma head_bot_of_not_positive {n : ℕ} (t : Tuple (K := K) (n + 1)) (ht : ¬ positive t) :
    t 0 = ⊥ := by
  by_contra h
  apply ht
  intro i
  exact (bot_lt_iff_ne_bot.mpr h).trans_le (t.monotone (Fin.zero_le i))

lemma positive_tail {n : ℕ} (t : Tuple (K := K) (n + 1)) (h : t 0 = ⊥) : positive (face 0 t) := by
  intro i
  change (⊥ : K) < t i.succ
  rw [← h]
  exact t.strictMono (by change 0 < i.val + 1; omega)

lemma prepend_tail {n : ℕ} (t : Tuple (K := K) (n + 1)) (h : t 0 = ⊥) :
    prepend (face 0 t) (positive_tail t h) = t := by
  ext i
  cases i using Fin.cases with
  | zero => exact h.symm
  | succ i => rfl

lemma not_positive_other_face {n : ℕ} (t : Tuple (K := K) (n + 2)) (h : t 0 = ⊥) (i : Fin (n + 1)) :
    ¬ positive (face i.succ t) := by
  intro hp
  have hh := hp 0
  have hf : face i.succ t 0 = t 0 := by simp [face]
  rw [hf, h] at hh
  exact lt_irrefl _ hh

def differential (n : ℕ) (x : Cochain (K := K) (V := V) n) : Cochain (K := K) (V := V) (n + 1) :=
  fun t => ∑ i : Fin (n + 1), ((-1 : ℝ) ^ i.val) • x (face i t)

def contraction (n : ℕ) (x : Cochain (K := K) (V := V) (n + 1)) : Cochain (K := K) (V := V) n := by
  classical
  exact fun t => if ht : positive t then x (prepend t ht) else 0

lemma contraction_positive (n : ℕ) (x : Cochain (K := K) (V := V) (n + 1))
    (t : Tuple (K := K) n) (ht : positive t) : contraction n x t = x (prepend t ht) := by
  simp [contraction, ht]

lemma contraction_not_positive (n : ℕ) (x : Cochain (K := K) (V := V) (n + 1))
    (t : Tuple (K := K) n) (ht : ¬ positive t) : contraction n x t = 0 := by
  simp [contraction, ht]

/-- The augmented simplex with constant coefficients has no positive-index
cohomology. The primitive is an explicitly defined insertion operator. -/
theorem primitive_of_closed (n : ℕ) (x : Cochain (K := K) (V := V) (n + 1))
    (hx : differential (n + 1) x = 0) : differential n (contraction n x) = x := by
  classical
  funext t
  by_cases ht : positive t
  · have hc := congrFun hx (prepend t ht)
    have hform : differential (n + 1) x (prepend t ht) = x t - differential n (contraction n x) t := by
      have heval (i : Fin (n + 1)) : contraction n x (face i t) =
          x (prepend (face i t) (positive_face t ht i)) :=
        contraction_positive n x (face i t) (positive_face t ht i)
      simp only [differential, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul,
        face_zero_prepend, face_succ_prepend, Fin.val_succ, pow_succ, mul_neg, mul_one,
        neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, heval]
    rw [hform] at hc
    exact (sub_eq_zero.mp hc).symm
  · have hhead := head_bot_of_not_positive t ht
    cases n with
    | zero =>
      simp only [differential, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, pow_zero,
        one_smul, add_zero]
      rw [contraction_positive 0 x (face 0 t) (positive_tail t hhead), prepend_tail t hhead]
    | succ n =>
      simp only [differential, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul]
      rw [contraction_positive (n + 1) x (face 0 t) (positive_tail t hhead), prepend_tail t hhead]
      have hz : ∀ i : Fin (n + 1), contraction (n + 1) x (face i.succ t) = 0 :=
        fun i => contraction_not_positive _ x _ (not_positive_other_face t hhead i)
      simp only [hz, smul_zero, Finset.sum_const_zero, add_zero]

end General
section Linear
variable {K V : Type*} [LinearOrder K] [AddCommGroup V] [Module ℝ V]
/-- Empty vertex sets and nonempty finite vertex sets are both covered. -/
theorem exists_primitive [Fintype K] (n : ℕ) (x : Cochain (K := K) (V := V) (n + 1))
    (hx : differential (n + 1) x = 0) : ∃ u, differential n u = x := by
  classical
  cases isEmpty_or_nonempty K with
  | inl h =>
    letI := h
    refine ⟨0, ?_⟩
    funext t
    exact isEmptyElim (t 0)
  | inr h =>
    letI := h
    letI := Fintype.toOrderBot K
    exact ⟨contraction n x, primitive_of_closed n x hx⟩

end Linear
end SimplexContraction
end WeightedObstructionNorms
