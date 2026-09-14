import WeightedObstructionNorms.ListPrism
import WeightedObstructionNorms.AlternatingEvaluation

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace PrismEvaluation
open CechAllDegrees AlternatingEvaluation ListPrism
variable {K V : Type*} [Fintype K] [LinearOrder K] [AddCommGroup V] [Module ℝ V]

lemma boundary_ofFn {K : Type*} {n : ℕ} (v : Fin (n + 1) → K) :
    boundaryBasis (List.ofFn v) = ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • atom (List.ofFn (v ∘ i.succAbove)) := by
  induction n with
  | zero => simp [List.ofFn_succ, boundaryBasis]
  | succ n ih =>
    rw [List.ofFn_succ, boundaryBasis, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one]
    rw [map_sum]
    have h0 : v ∘ (0 : Fin (n + 2)).succAbove = fun i => v i.succ := rfl
    rw [h0]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_smul, map_smul]
    congr 2
    rw [cone_atom, List.ofFn_succ]
    simp [Function.comp_def, Fin.succ_succAbove_succ]

def onList {n : ℕ} (x : Tuple (K := K) n → V) (l : List K) : V :=
  if h : l.length = n then evaluate x (fun i => l.get (Fin.cast h.symm i)) else 0

def pair {n : ℕ} (x : Tuple (K := K) n → V) : Chain K →ₗ[ℝ] V :=
  Finsupp.linearCombination ℝ (onList x)

@[simp] lemma pair_atom {n : ℕ} (x : Tuple (K := K) n → V) (l : List K) :
    pair x (atom l) = onList x l := by simp [pair, atom]

@[simp] lemma onList_ofFn {n m : ℕ} (x : Tuple (K := K) n → V) (v : Fin m → K) :
    onList x (List.ofFn v) = if h : m = n then evaluate x (fun i => v (Fin.cast h.symm i)) else 0 := by
  simp only [onList, List.length_ofFn]
  split_ifs with h
  · subst m; simp
  · rfl

@[simp] lemma pair_atom_ofFn {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin n → K) :
    pair x (atom (List.ofFn v)) = evaluate x v := by simp

lemma pair_boundary_ofFn {n : ℕ} (x : Tuple (K := K) n → V) (v : Fin (n + 1) → K) :
    pair x (boundary (atom (List.ofFn v))) = evaluate (SimplexContraction.differential n x) v := by
  rw [boundary_atom, boundary_ofFn, map_sum, evaluate_differential]
  simp [rawDifferential, Function.comp_def]

lemma pair_differential_atom {n : ℕ} (x : Tuple (K := K) n → V) (l : List K) :
    pair (SimplexContraction.differential n x) (atom l) = pair x (boundary (atom l)) := by
  have aux : ∀ (m : ℕ) (v : Fin m → K),
      pair (SimplexContraction.differential n x) (atom (List.ofFn v)) =
        pair x (boundary (atom (List.ofFn v))) := by
    intro m v
    cases m with
    | zero => simp [onList, boundaryBasis]
    | succ m =>
      by_cases h : m = n
      · subst m
        simpa only [pair_atom_ofFn] using (pair_boundary_ofFn x v).symm
      · rw [boundary_atom, boundary_ofFn, map_sum]
        simp only [map_smul, pair_atom, onList_ofFn, dif_neg h, smul_zero, Finset.sum_const_zero]
        simp [onList, h]
  simpa only [List.ofFn_get] using aux l.length l.get

lemma pair_differential {n : ℕ} (x : Tuple (K := K) n → V) (c : Chain K) :
    pair (SimplexContraction.differential n x) c = pair x (boundary c) := by
  have h : pair (SimplexContraction.differential n x) = (pair x).comp boundary := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp only [map_smul, LinearMap.comp_apply, pair_differential_atom]
  exact congrArg (fun F : Chain K →ₗ[ℝ] V => F c) h

lemma pair_linear {W : Type*} [AddCommGroup W] [Module ℝ W]
    (F : V →ₗ[ℝ] W) {n : ℕ} (x : Tuple (K := K) n → V) (c : Chain K) :
    F (pair x c) = pair (fun t => F (x t)) c := by
  have h : F.comp (pair x) = pair (fun t => F (x t)) := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp only [LinearMap.comp_apply, map_smul, pair_atom]
    congr 1
    unfold onList
    split_ifs
    · exact evaluate_linear F x _
    · exact map_zero F
  exact congrArg (fun G : Chain K →ₗ[ℝ] W => G c) h

lemma pair_map_orderEmbedding {L : Type*} [Fintype L] [LinearOrder L]
    (a : L ↪o K) {n : ℕ} (x : Tuple (K := K) n → V) (c : Chain L) :
    pair x (ListPrism.map a c) = pair (fun t => x (t.trans a)) c := by
  have h : (pair x).comp (ListPrism.map a) = pair (fun t => x (t.trans a)) := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp only [LinearMap.comp_apply, map_smul, map_atom, pair_atom]
    congr 1
    unfold onList
    simp only [List.length_map]
    split_ifs with h
    · simpa only [List.get_eq_getElem, List.getElem_map, Function.comp_def] using evaluate_orderEmbedding a x (fun i => l.get (Fin.cast h.symm i))
    · rfl
  exact congrArg (fun G : Chain L →ₗ[ℝ] V => G c) h

variable {L : Type*} [Fintype L] [LinearOrder L]

def homotopy (f g : L → K) (n : ℕ) (x : Tuple (K := K) (n + 1) → V) : Tuple (K := L) n → V :=
  fun t => pair x (prism f g (atom (List.ofFn t)))

lemma homotopy_identity (f g : L → K) (n : ℕ) (x : Tuple (K := K) (n + 1) → V) :
    SimplexContraction.differential n (homotopy f g n x) +
      homotopy f g (n + 1) (SimplexContraction.differential (n + 1) x) =
        pull g x - pull f x := by
  funext t
  have h := congrArg (pair x) (prism_identity f g (atom (List.ofFn t)))
  rw [map_add, map_sub, map_atom, map_atom, ← pair_differential] at h
  rw [boundary_atom, boundary_ofFn, map_sum, map_sum] at h
  simp only [map_smul, List.map_ofFn, pair_atom_ofFn] at h
  change (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • homotopy f g n x (face i t)) + _ = _
  simpa only [homotopy, pull, Function.comp_def, face, RelEmbedding.trans_apply,
    Fin.succAboveOrderEmb_apply] using (add_comm _ _).trans h

end PrismEvaluation
end WeightedObstructionNorms
