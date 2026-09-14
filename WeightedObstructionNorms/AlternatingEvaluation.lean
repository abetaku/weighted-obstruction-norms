import WeightedObstructionNorms.CechWeights
import WeightedObstructionNorms.SimplexContraction
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace AlternatingEvaluation
open CechAllDegrees
variable {K V : Type*} [Fintype K] [LinearOrder K] [AddCommGroup V] [Module ℝ V]

local instance {n : ℕ} : DecidableEq (Tuple (K := K) n) := Classical.decEq _

def orientation {n : ℕ} (v : Fin n → K) (t : Tuple (K := K) n) : ℝ :=
  Matrix.det (fun i j => if v i = t j then 1 else 0)

def evaluate {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin n → K) : V :=
  ∑ t, orientation v t • x t

lemma ordered_eq_of_containment {n : ℕ} (s t : Tuple (K := K) n)
    (h : ∀ i, ∃ j, s i = t j) : s = t := by
  classical
  let A := Finset.univ.image t
  have hcard : A.card = n := by simp [A, Finset.card_image_of_injective, t.injective]
  have hs : (s : Fin n → K) = A.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun i => by
      obtain ⟨j, hj⟩ := h i
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩) s.strictMono
  have ht : (t : Fin n → K) = A.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) t.strictMono
  exact DFunLike.coe_injective (hs.trans ht.symm)

lemma orientation_ordered {n : ℕ} (s t : Tuple (K := K) n) :
    orientation s t = if s = t then 1 else 0 := by
  classical
  by_cases h : s = t
  · subst t
    have hm : (fun i j => if s i = s j then (1 : ℝ) else 0) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.one_apply, s.injective.eq_iff]
    unfold orientation
    rw [hm, Matrix.det_one]
    simp
  · rw [if_neg h]
    have hi : ∃ i, ∀ j, s i ≠ t j := by
      by_contra hh
      push_neg at hh
      exact h (ordered_eq_of_containment s t hh)
    obtain ⟨i, hi⟩ := hi
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hi j))

lemma evaluate_ordered {n : ℕ} (x : Tuple (K := K) n → V) (t : Tuple (K := K) n) :
    evaluate x t = x t := by
  classical
  simp [evaluate, orientation_ordered]

lemma orientation_perm {n : ℕ} (v : Fin n → K) (t : Tuple (K := K) n) (σ : Equiv.Perm (Fin n)) :
    orientation (v ∘ σ) t = ((Equiv.Perm.sign σ : ℤ) : ℝ) * orientation v t :=
  Matrix.det_permute σ (fun i j => if v i = t j then (1 : ℝ) else 0)

lemma evaluate_perm {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    evaluate x (v ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) • evaluate x v := by
  simp only [evaluate, orientation_perm, mul_smul, Finset.smul_sum]

lemma evaluate_not_injective {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin n → K)
    (hv : ¬ Function.Injective v) : evaluate x v = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, v i = v j ∧ i ≠ j := by simpa [Function.Injective] using hv
  have hh (t : Tuple (K := K) n) : orientation v t = 0 := by
    exact Matrix.det_zero_of_row_eq hne (by funext k; rw [hij])
  simp [evaluate, hh]

lemma decompose_injective {n : ℕ} (v : Fin n → K) (hv : Function.Injective v) :
    ∃ t : Tuple (K := K) n, ∃ σ : Equiv.Perm (Fin n), v = t ∘ σ := by
  classical
  let A := Finset.univ.image v
  have hcard : A.card = n := by simp [A, Finset.card_image_of_injective, hv]
  let e := A.orderIsoOfFin hcard
  let f : Fin n → Fin n := fun i => e.symm ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hv
    exact congrArg Subtype.val (e.symm.injective hij)
  let σ := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩)
  refine ⟨A.orderEmbOfFin hcard, σ, ?_⟩
  funext i
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)).symm

/-- Alternating functions are determined by their increasing-tuple values. -/
lemma alternating_ext {n : ℕ} (f g : (Fin n → K) → V)
    (hf : ∀ v (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) • f v)
    (hg : ∀ v (σ : Equiv.Perm (Fin n)), g (v ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) • g v)
    (hf0 : ∀ v, ¬ Function.Injective v → f v = 0)
    (hg0 : ∀ v, ¬ Function.Injective v → g v = 0)
    (hord : ∀ t : Tuple (K := K) n, f t = g t) : f = g := by
  funext v
  by_cases hv : Function.Injective v
  · obtain ⟨t, σ, rfl⟩ := decompose_injective v hv
    rw [hf, hg, hord]
  · rw [hf0 v hv, hg0 v hv]

def rawDifferential {n : ℕ} (f : (Fin n → K) → V) (v : Fin (n + 1) → K) : V :=
  ∑ i : Fin (n + 1), ((-1 : ℝ) ^ i.val) • f (v ∘ i.succAbove)

def augmentedMatrix {n : ℕ} (v : Fin (n + 1) → K) (t : Tuple (K := K) n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.cases 1 (fun k => if v i = t k then 1 else 0) j

lemma augmented_det {n : ℕ} (v : Fin (n + 1) → K) (t : Tuple (K := K) n) :
    (augmentedMatrix v t).det = ∑ i : Fin (n + 1), ((-1 : ℝ) ^ i.val) * orientation (v ∘ i.succAbove) t := by
  rw [Matrix.det_succ_column_zero]
  simp [augmentedMatrix, orientation, Matrix.submatrix, Function.comp_def]
  rfl

lemma rawDifferential_evaluate {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin (n + 1) → K) :
    rawDifferential (evaluate x) v = ∑ t, (augmentedMatrix v t).det • x t := by
  simp only [rawDifferential, evaluate, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [augmented_det, Finset.sum_smul]

lemma rawDifferential_evaluate_perm {n : ℕ} (x : Tuple (K := K) n → V)
    (v : Fin (n + 1) → K) (σ : Equiv.Perm (Fin (n + 1))) :
    rawDifferential (evaluate x) (v ∘ σ) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) • rawDifferential (evaluate x) v := by
  have hh (t : Tuple (K := K) n) : (augmentedMatrix (v ∘ σ) t).det =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (augmentedMatrix v t).det :=
    Matrix.det_permute σ (augmentedMatrix v t)
  simp only [rawDifferential_evaluate, hh, Finset.smul_sum, mul_smul]

lemma rawDifferential_evaluate_not_injective {n : ℕ} (x : Tuple (K := K) n → V)
    (v : Fin (n + 1) → K) (hv : ¬ Function.Injective v) : rawDifferential (evaluate x) v = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, v i = v j ∧ i ≠ j := by simpa [Function.Injective] using hv
  have hh (t : Tuple (K := K) n) : (augmentedMatrix v t).det = 0 := by
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp only [augmentedMatrix, hij]
  simp [rawDifferential_evaluate, hh]

/-- Alternating extension commutes with the augmented differential on every
ordered or repeated tuple. The determinant proof handles all signs. -/
theorem evaluate_differential {n : ℕ} (x : Tuple (K := K) n → V) :
    evaluate (SimplexContraction.differential n x) = rawDifferential (evaluate x) := by
  apply alternating_ext
  · exact evaluate_perm _
  · exact rawDifferential_evaluate_perm x
  · exact evaluate_not_injective _
  · exact rawDifferential_evaluate_not_injective x
  · intro t
    rw [evaluate_ordered]
    unfold SimplexContraction.differential rawDifferential
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (evaluate_ordered x (face i t)).symm

lemma evaluate_add {n : ℕ} (x y : Tuple (K := K) n → V) (v : Fin n → K) :
    evaluate (x + y) v = evaluate x v + evaluate y v := by
  simp [evaluate, smul_add, Finset.sum_add_distrib]

lemma evaluate_smul {n : ℕ} (a : ℝ) (x : Tuple (K := K) n → V) (v : Fin n → K) :
    evaluate (a • x) v = a • evaluate x v := by
  simp only [evaluate, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact smul_comm _ _ _

lemma evaluate_linear {W : Type*} [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W)
    {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin n → K) :
    f (evaluate x v) = evaluate (fun t => f (x t)) v := by
  simp [evaluate, map_sum, map_smul]

variable {L : Type*} [Fintype L] [LinearOrder L]

def pull (f : L → K) {n : ℕ} (x : Tuple (K := K) n → V) (t : Tuple (K := L) n) : V :=
  evaluate x (f ∘ t)

lemma evaluate_pull (f : L → K) {n : ℕ} (x : Tuple (K := K) n → V) :
    evaluate (pull f x) = fun v => evaluate x (f ∘ v) := by
  apply alternating_ext
  · exact evaluate_perm _
  · intro v σ
    exact evaluate_perm x (f ∘ v) σ
  · exact evaluate_not_injective _
  · intro v hv
    exact evaluate_not_injective x (f ∘ v) (fun h => hv h.of_comp)
  · intro t
    exact evaluate_ordered (pull f x) t

/-- Arbitrary vertex selections give cochain maps, including repeated and
out-of-order selected vertices. -/
theorem pull_differential (f : L → K) {n : ℕ} (x : Tuple (K := K) n → V) :
    SimplexContraction.differential n (pull f x) =
      pull f (SimplexContraction.differential n x) := by
  funext t
  unfold pull
  rw [evaluate_differential]
  rfl

lemma pull_id {n : ℕ} (x : Tuple (K := K) n → V) : pull id x = x := by
  funext t
  exact evaluate_ordered x t

lemma pull_comp {P : Type*} [Fintype P] [LinearOrder P] (f : L → K) (g : P → L)
    {n : ℕ} (x : Tuple (K := K) n → V) : pull g (pull f x) = pull (f ∘ g) x := by
  funext t
  exact congrFun (evaluate_pull f x) (g ∘ t)

lemma evaluate_orderEmbedding (f : K ↪o L) {n : ℕ} (x : Tuple (K := L) n → V) (v : Fin n → K) :
    evaluate x (f ∘ v) = evaluate (fun t : Tuple (K := K) n => x (t.trans f)) v := by
  have hh : pull f x = fun t : Tuple (K := K) n => x (t.trans f) := by
    funext t
    exact evaluate_ordered x (t.trans f)
  rw [← hh]
  exact (congrFun (evaluate_pull f x) v).symm

end AlternatingEvaluation
end WeightedObstructionNorms
