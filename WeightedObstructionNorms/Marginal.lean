import WeightedObstructionNorms.WeightedNorm

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace Marginal
variable {A B C : Type*} [Fintype A]

/-- Pushforward of a signed measure along a finite map. Coordinate
restriction and support-extension are special cases of this operation. -/
def push (f : A → B) (x : A → ℝ) (b : B) : ℝ := by
  classical
  exact ∑ a, if f a = b then x a else 0

lemma push_add (f : A → B) (x y : A → ℝ) : push f (x + y) = push f x + push f y := by
  classical
  funext b
  simp only [push, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma push_smul (f : A → B) (t : ℝ) (x : A → ℝ) : push f (t • x) = t • push f x := by
  classical
  funext b
  simp only [push, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

def linear (f : A → B) : (A → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun := push f
  map_add' := push_add f
  map_smul' := push_smul f

lemma push_id (x : A → ℝ) : push id x = x := by
  classical
  funext a
  simp [push]

lemma push_comp [Fintype B] (f : A → B) (g : B → C) (x : A → ℝ) :
    push g (push f x) = push (g ∘ f) x := by
  classical
  funext c
  simp only [push]
  have hdist : ∀ b : B,
      (if g b = c then ∑ a, if f a = b then x a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then x a else 0) else 0 := by
    intro b
    by_cases h : g b = c <;> simp [h]
  simp_rw [hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hswap : ∀ b : B,
      (if g b = c then if f a = b then x a else 0 else 0) =
      (if f a = b then if g b = c then x a else 0 else 0) := by
    intro b
    split_ifs <;> rfl
  simp_rw [hswap]
  simp

lemma push_injective_apply (f : A → B) (hf : Function.Injective f) (x : A → ℝ) (a : A) :
    push f x (f a) = x a := by
  classical
  simp [push, hf.eq_iff]

lemma push_injective (f : A → B) (hf : Function.Injective f) : Function.Injective (push f) := by
  intro x y h
  funext a
  have h' := congrFun h (f a)
  simpa [push_injective_apply f hf] using h'

/-- Equation (5.2): marginalization maps the weighted box into the
marginal weighted box. This is valid even without positivity assumptions. -/
theorem box_contraction (f : A → B) {q x : A → ℝ} {L : ℝ}
    (hx : ∀ a, |x a| ≤ L * q a) (b : B) :
    |push f x b| ≤ L * push f q b := by
  classical
  calc
    |push f x b| ≤ ∑ a, |if f a = b then x a else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, if f a = b then L * q a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> simp [hx a]
    _ = L * push f q b := by
      simp only [push, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

theorem weightedNorm_contraction [Fintype B] (f : A → B) {q x : A → ℝ}
    (hq : ∀ a, 0 < q a) (hmq : ∀ b, 0 < push f q b) :
    weightedNorm (push f q) (push f x) ≤ weightedNorm q x := by
  apply (weightedNorm_le_iff hmq (weightedNorm_nonneg q x)).2
  exact box_contraction f (coordinate_le_weightedNorm hq)

end Marginal
end WeightedObstructionNorms
