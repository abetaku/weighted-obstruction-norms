import WeightedObstructionNorms.CechAllDegrees

noncomputable section
namespace WeightedObstructionNorms
namespace Marginal

/-- Extension by zero preserves coordinate boxes when the weights agree on
the embedded coordinates. Points outside the image contribute zero. -/
lemma box_extension {A B : Type*} [Fintype A] (f : A → B) (hf : Function.Injective f)
    {x : A → ℝ} {w : B → ℝ} {L : ℝ} (hL : 0 ≤ L) (hw : ∀ b, 0 ≤ w b)
    (hx : ∀ a, |x a| ≤ L * w (f a)) (b : B) : |push f x b| ≤ L * w b := by
  classical
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a,rfl⟩ := hb
    rw [push_injective_apply f hf]
    exact hx a
  · have hz : push f x b = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp only [if_neg (show f a ≠ b from fun h => hb ⟨a,h⟩)]
    rw [hz, abs_zero]
    exact mul_nonneg hL (hw b)

end Marginal
namespace CechAllDegrees
open FiniteObservations
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

instance tupleFintype (n : ℕ) : Fintype (Tuple (K := K) n) := Fintype.ofFinite _

/-- Finite coordinates, keeping each tuple's projected-support type. -/
abbrev Coordinate (n : ℕ) := Σ t : Tuple (K := K) n, SupportState E S (observation M t)

def coordinateWeight (q : State E → ℝ) (n : ℕ) (a : Coordinate E S M n) : ℝ :=
  weight E q (observation M a.1) a.2.val

/-- Exactly the manuscript's maximum over tuples and local states, with zero
for the empty coordinate set. The index n corresponds to paper degree n-1. -/
def cochainNorm (q : State E → ℝ) (n : ℕ) (x : Cochain E S M n) : ℝ :=
  weightedNorm (coordinateWeight E S M q n) (fun a => x a.1 a.2)

lemma coordinateWeight_positive [∀ i, Nonempty (E i)] {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (n : ℕ) : ∀ a, 0 < coordinateWeight E S M q n a := by
  intro a
  exact weight_positive E hq _ _

lemma cochainNorm_nonneg (q : State E → ℝ) (n : ℕ) (x : Cochain E S M n) :
    0 ≤ cochainNorm E S M q n x := weightedNorm_nonneg _ _

lemma cochainNorm_eq_zero_iff [∀ i, Nonempty (E i)] {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (n : ℕ) (x : Cochain E S M n) : cochainNorm E S M q n x = 0 ↔ x = 0 := by
  rw [cochainNorm, weightedNorm_eq_zero_iff (coordinateWeight_positive E S M hq n)]
  constructor
  · intro h
    funext t a
    exact congrFun h ⟨t,a⟩
  · rintro rfl
    rfl

lemma cochainNorm_add_le (q : State E → ℝ) (n : ℕ) (x y : Cochain E S M n) :
    cochainNorm E S M q n (x + y) ≤ cochainNorm E S M q n x + cochainNorm E S M q n y :=
  weightedNorm_add_le

lemma cochainNorm_smul (q : State E → ℝ) (n : ℕ) (a : ℝ) (x : Cochain E S M n) :
    cochainNorm E S M q n (a • x) = |a| * cochainNorm E S M q n x := weightedNorm_smul _ _ _

/-- Support extension is isometric for the original cochain norms. This is
not the separate assertion about the obstruction norm on cohomology. -/
theorem extension_norm [∀ i, Nonempty (E i)] {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    {T : Finset (State E)} (hST : S ⊆ T) (n : ℕ) (x : Cochain E S M n) :
    cochainNorm E T M q n (extension E S M hST n x) = cochainNorm E S M q n x := by
  apply le_antisymm
  · apply (weightedNorm_le_iff (coordinateWeight_positive E T M hq n)
      (cochainNorm_nonneg E S M q n x)).2
    rintro ⟨t,b⟩
    apply Marginal.box_extension (supportInclude E hST (observation M t))
      (supportInclude_injective E hST _) (cochainNorm_nonneg E S M q n x)
      (fun b => (weight_positive E hq (observation M t) b.val).le)
    intro a
    exact coordinate_le_weightedNorm (x := fun b : Coordinate E S M n => x b.1 b.2)
      (coordinateWeight_positive E S M hq n) ⟨t,a⟩
  · apply (weightedNorm_le_iff (coordinateWeight_positive E S M hq n)
      (cochainNorm_nonneg E T M q n (extension E S M hST n x))).2
    rintro ⟨t,a⟩
    have h := coordinate_le_weightedNorm
      (x := fun b : Coordinate E T M n => extension E S M hST n x b.1 b.2)
      (coordinateWeight_positive E T M hq n) ⟨t, supportInclude E hST _ a⟩
    change |Marginal.push (supportInclude E hST _) (x t) (supportInclude E hST _ a)| ≤ _ at h
    rw [Marginal.push_injective_apply _ (supportInclude_injective E hST _)] at h
    exact h

end CechAllDegrees
end WeightedObstructionNorms
