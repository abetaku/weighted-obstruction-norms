import WeightedObstructionNorms.FiniteObservations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace InteractionCoordinates

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The base coordinate records total mass; all other coordinates are retained. -/
def forwardEntry (o y z : A) : ℝ := if y = o then 1 else if z = y then 1 else 0

/-- Inverse change of coordinates: the base atom is total mass minus the others. -/
def inverseEntry (o y z : A) : ℝ :=
  if y = o then (if z = o then 1 else -1) else if z = y then 1 else 0

lemma inverse_forward (o y w : A) :
    ∑ z, inverseEntry o y z * forwardEntry o z w = if y = w then 1 else 0 := by
  classical
  by_cases hy : y = o
  · subst y
    by_cases hw : w = o
    · subst w
      rw [Finset.sum_eq_single o]
      · simp [inverseEntry, forwardEntry]
      · intro b hb hbo
        simp [inverseEntry, forwardEntry, hbo, Ne.symm hbo]
      · simp
    · rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ o)]
      simp only [inverseEntry, forwardEntry, if_pos rfl, one_mul, if_neg hw, ↓reduceIte]
      have hh : ∑ z ∈ Finset.univ \ {o},
          (if z = o then (1 : ℝ) else -1) * (if z = o then 1 else if w = z then 1 else 0) = -1 := by
        rw [Finset.sum_eq_single w]
        · simp [hw]
        · intro b hb hbw
          have hbo : b ≠ o := by simpa using (Finset.mem_sdiff.mp hb).2
          simp [hbo, Ne.symm hbw]
        · simp [hw]
      rw [hh]
      simp [Ne.symm hw]
  · rw [Finset.sum_eq_single y]
    · simp [inverseEntry, forwardEntry, hy, eq_comm]
    · intro b hb hby
      simp [inverseEntry, hy, hby]
    · simp

variable {I : Type*} [Fintype I] [DecidableEq I] (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Product basis matrix on a finite family of finite spaces. -/
def forward (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) (y : ∀ i, E i) : ℝ :=
  ∑ z, (∏ i, forwardEntry (o i) (y i) (z i)) * x z

def inverse (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) (y : ∀ i, E i) : ℝ :=
  ∑ z, (∏ i, inverseEntry (o i) (y i) (z i)) * x z

lemma product_inverse_forward (o y w : ∀ i, E i) :
    ∑ z : ∀ i, E i, (∏ i, inverseEntry (o i) (y i) (z i)) *
      (∏ i, forwardEntry (o i) (z i) (w i)) = if y = w then 1 else 0 := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i z => inverseEntry (o i) (y i) z * forwardEntry (o i) z (w i))]
  simp_rw [inverse_forward]
  by_cases h : y = w
  · subst w
    simp
  · have hi : ∃ i, y i ≠ w i := by simpa only [funext_iff, not_forall] using h
    obtain ⟨i, hi⟩ := hi
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma inverse_forward_apply (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) :
    inverse E o (forward E o x) = x := by
  classical
  funext y
  simp only [inverse, forward, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, product_inverse_forward]
  simp

/-- The interaction coordinates form a genuine linear change of basis. -/
def forwardLinear (o : ∀ i, E i) : ((∀ i, E i) → ℝ) →ₗ[ℝ] ((∀ i, E i) → ℝ) where
  toFun := forward E o
  map_add' x z := by
    funext y
    simp [forward, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext y
    simp [forward, Finset.mul_sum, mul_left_comm]

lemma forward_injective (o : ∀ i, E i) : Function.Injective (forward E o) :=
  Function.LeftInverse.injective (inverse_forward_apply E o)

lemma forward_surjective (o : ∀ i, E i) : Function.Surjective (forward E o) :=
  (LinearMap.injective_iff_surjective (f := forwardLinear E o)).mp (forward_injective E o)

lemma forward_inverse_apply (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) :
    forward E o (inverse E o x) = x := by
  obtain ⟨z, rfl⟩ := forward_surjective E o x
  rw [inverse_forward_apply]

def equiv (o : ∀ i, E i) : ((∀ i, E i) → ℝ) ≃ₗ[ℝ] ((∀ i, E i) → ℝ) :=
  LinearEquiv.ofBijective (forwardLinear E o) ⟨forward_injective E o, forward_surjective E o⟩

lemma equiv_apply (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) : equiv E o x = forward E o x := rfl

lemma equiv_symm_apply (o : ∀ i, E i) (x : (∀ i, E i) → ℝ) :
    (equiv E o).symm x = inverse E o x := by
  apply (equiv E o).injective
  rw [LinearEquiv.apply_symm_apply, equiv_apply, forward_inverse_apply]

open FiniteObservations

lemma sum_mul_push {P Q : Type*} [Fintype P] [Fintype Q]
    (f : P → Q) (x : P → ℝ) (g : Q → ℝ) :
    ∑ y, g y * Marginal.push f x y = ∑ z, g (f z) * x z := by
  classical
  simp only [Marginal.push, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite]

lemma product_supported (o y z : ∀ i, E i) (A : Finset I)
    (hy : ∀ i, i ∉ A → y i = o i) :
    (∏ i : A, forwardEntry (o i.val) (y i.val) (z i.val)) =
      ∏ i, forwardEntry (o i) (y i) (z i) := by
  classical
  rw [Finset.prod_coe_sort A (fun i => forwardEntry (o i) (y i) (z i))]
  exact Finset.prod_subset (Finset.subset_univ A) (by
    intro i _ hi
    simp [forwardEntry, hy i hi])

/-- Marginalization retains precisely the interaction coordinates supported on
its observation. This is proved for arbitrary signed measures. -/
theorem forward_project (o y : ∀ i, E i) (A : Finset I)
    (hy : ∀ i, i ∉ A → y i = o i) (x : (∀ i, E i) → ℝ) :
    forward (fun i : A => E i.val) (project E A o)
      (Marginal.push (project E A) x) (project E A y) = forward E o x y := by
  classical
  unfold forward
  rw [sum_mul_push]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  exact product_supported E o y z A hy

def complete (o : ∀ i, E i) (A : Finset I) (z : LocalState E A) : ∀ i, E i :=
  fun i => if hi : i ∈ A then z ⟨i, hi⟩ else o i

lemma complete_mem (o : ∀ i, E i) (A : Finset I) (z : LocalState E A)
    (i : I) (hi : i ∈ A) : complete E o A z i = z ⟨i, hi⟩ := by
  simp [complete, hi]

lemma project_complete (o : ∀ i, E i) (A : Finset I) (z : LocalState E A) :
    project E A (complete E o A z) = z := by
  funext i
  exact complete_mem E o A z i.val i.property

lemma complete_supported (o : ∀ i, E i) (A : Finset I) (z : LocalState E A) :
    ∀ i, i ∉ A → complete E o A z i = o i := by
  intro i hi
  simp [complete, hi]

lemma complete_project (o y : ∀ i, E i) (A : Finset I)
    (hy : ∀ i, i ∉ A → y i = o i) : complete E o A (project E A y) = y := by
  funext i
  by_cases hi : i ∈ A
  · simp [complete, project, hi]
  · simp [complete, hi, hy i hi]

lemma product_restrict (o y : ∀ i, E i) {A B : Finset I} (hAB : A ⊆ B)
    (hy : ∀ i, i ∉ A → y i = o i) (z : LocalState E B) :
    (∏ i : A, forwardEntry (o i.val) (y i.val) (restrict E hAB z i)) =
      ∏ i : B, forwardEntry (o i.val) (y i.val) (z i) := by
  have ha := product_supported E o y (complete E o B z) A hy
  have hb := product_supported E o y (complete E o B z) B
    (fun i hi => hy i (fun h => hi (hAB h)))
  calc
    _ = ∏ i : A, forwardEntry (o i.val) (y i.val) (complete E o B z i.val) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [complete_mem E o B z i.val (hAB i.property)]
      rfl
    _ = _ := ha.trans hb.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [complete_mem E o B z i.val i.property]

/-- In interaction coordinates every marginal map is a coordinate restriction. -/
theorem forward_restrict (o y : ∀ i, E i) {A B : Finset I} (hAB : A ⊆ B)
    (hy : ∀ i, i ∉ A → y i = o i) (x : LocalState E B → ℝ) :
    forward (fun i : A => E i.val) (project E A o)
      (Marginal.push (restrict E hAB) x) (project E A y) =
    forward (fun i : B => E i.val) (project E B o) x (project E B y) := by
  classical
  unfold forward
  rw [sum_mul_push]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  exact product_restrict E o y hAB hy z

end InteractionCoordinates
end WeightedObstructionNorms
