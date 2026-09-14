import WeightedObstructionNorms.ObservationRestriction
import WeightedObstructionNorms.CechSupportNorm

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace ObservationRestrictionNorm
open FiniteObservations CechAllDegrees AlternatingEvaluation
variable {I K L : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [LinearOrder K] [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)
    (o : State E)

include o in
lemma marginal_box {q : State E → ℝ} (hq : ∀ z, 0 < q z) {A B : Finset I} (hAB : A ⊆ B)
    {x : SupportState E S B → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ b, |x b| ≤ C * weight E q B b.val) (a : SupportState E S A) :
    |marginal E S hAB x a| ≤ C * weight E q A a.val := by
  classical
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  have hb : ∀ b, |Marginal.push Subtype.val x b| ≤ C * weight E q B b :=
    Marginal.box_extension Subtype.val Subtype.val_injective hC (fun b => (weight_positive E hq B b).le) hx
  have hh := Marginal.box_contraction (restrict E hAB) hb a.val
  rw [weight_marginal] at hh
  have he : Marginal.push (restrict E hAB) (Marginal.push Subtype.val x) a.val = marginal E S hAB x a := by
    calc
      _ = Marginal.push Subtype.val (marginal E S hAB x) a.val := by
        change Marginal.push _ (Marginal.push _ x) _ = Marginal.push _ (Marginal.push _ x) _
        rw [Marginal.push_comp, Marginal.push_comp]
        rfl
      _ = _ := Marginal.push_injective_apply _ Subtype.val_injective _ a
  rwa [he] at hh

include o in
lemma project_box {q : State E → ℝ} (hq : ∀ z, 0 < q z) (A : Finset I) (n : ℕ)
    (x : Cochain E S M n) (t : Tuple (K := ObservationRestriction.Vertex M A) n)
    (a : SupportState E S A) :
    |ObservationRestriction.project E S M A n x t a| ≤
      cochainNorm E S M q n x * weight E q A a.val := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply marginal_box E S o hq (ObservationRestriction.contains M t) (cochainNorm_nonneg E S M q n x)
  intro b
  exact coordinate_le_weightedNorm (x := fun a => x a.1 a.2)
    (coordinateWeight_positive E S M hq n) ⟨ObservationRestriction.forget M t, b⟩

include o in
lemma evaluate_box {q : State E → ℝ} (hq : ∀ z, 0 < q z) (A : Finset I) (n : ℕ)
    (x : Cochain E S M n) (v : Fin n → ObservationRestriction.Vertex M A) (a : SupportState E S A) :
    |evaluate (ObservationRestriction.project E S M A n x) v a| ≤
      cochainNorm E S M q n x * weight E q A a.val := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  by_cases hv : Function.Injective v
  · obtain ⟨t, σ, rfl⟩ := decompose_injective v hv
    rw [evaluate_perm, evaluate_ordered]
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_unit_intCast, one_mul] using project_box E S M o hq A n x t a
  · rw [evaluate_not_injective _ v hv]
    simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (cochainNorm_nonneg E S M q n x) (weight_positive E hq A a.val).le

include o in
/-- The actual alternating restriction is nonexpansive for the manuscript's
weighted maximum norm, in every degree and for arbitrary selections. -/
theorem cochain_nonexpansive (N : L → Finset I) (f : L → K) (hf : ∀ a, N a ⊆ M (f a))
    {q : State E → ℝ} (hq : ∀ z, 0 < q z) (n : ℕ) (x : Cochain E S M n) :
    cochainNorm E S N q n (ObservationRestriction.restriction E S M N f hf n x) ≤ cochainNorm E S M q n x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (coordinateWeight_positive E S N hq n) (cochainNorm_nonneg E S M q n x)).2
  intro j
  exact evaluate_box E S M o hq _ n x _ j.2

open CechSplitting ObservationRestriction
variable [∀ i, DecidableEq (E i)]
    (N : L → Finset I) (f : L → K) (hf : ∀ a, N a ⊆ M (f a))

def windowMap (p : ℕ) : WindowMap (window E S M o p) (window E S N o p) where
  oldMap := (pack E S N p).symm.toLinearMap ∘ₗ restriction E S M N f hf p ∘ₗ (pack E S M p).toLinearMap
  newMap := takeNew E S N p ∘ₗ restriction E Finset.univ M N f hf p ∘ₗ putNew E S M p
  cochainMap := (pack E S N (p + 1)).symm.toLinearMap ∘ₗ restriction E S M N f hf (p + 1) ∘ₗ
    (pack E S M (p + 1)).toLinearMap
  correction := (pack E S N p).symm.toLinearMap ∘ₗ takeOld E S N p ∘ₗ
    restriction E Finset.univ M N f hf p ∘ₗ putNew E S M p
  old_comm := by
    intro u
    change (pack E S N (p + 1)).symm (restriction E S M N f hf (p + 1) (differential E S M p (pack E S M p u))) =
      (pack E S N (p + 1)).symm (differential E S N p (restriction E S M N f hf p (pack E S M p u)))
    rw [restriction_differential]
  closed := by
    intro c hc
    have hh : differential E S M (p + 1) (pack E S M (p + 1) c) = 0 :=
      (pack E S M (p + 2)).symm.injective (by exact hc)
    change (pack E S N (p + 2)).symm (differential E S N (p + 1)
      (restriction E S M N f hf (p + 1) (pack E S M (p + 1) c))) = 0
    rw [restriction_differential, hh, map_zero, map_zero]
  new_closed := by
    intro v hv
    change takeNew E S N (p + 1) (differential E Finset.univ N p
      (putNew E S N p (takeNew E S N p (restriction E Finset.univ M N f hf p (putNew E S M p v))))) = 0
    rw [← differential_takeNew, restriction_differential,
      CechSupportNorm.closed_lift E S M o p v hv, restriction_extension, takeNew_extension]
  lift_comm := by
    intro v hv
    change (pack E S N (p + 1)).symm
        (restriction E S M N f hf (p + 1) (takeOld E S M (p + 1)
          (differential E Finset.univ M p (putNew E S M p v)))) =
      (pack E S N (p + 1)).symm (differential E S N p
        (takeOld E S N p (restriction E Finset.univ M N f hf p (putNew E S M p v)))) +
      (pack E S N (p + 1)).symm (takeOld E S N (p + 1) (differential E Finset.univ N p
        (putNew E S N p (takeNew E S N p (restriction E Finset.univ M N f hf p (putNew E S M p v))))))
    rw [← map_add, ← differential_takeOld, restriction_differential,
      CechSupportNorm.closed_lift E S M o p v hv, restriction_extension, takeOld_extension, takeOld_extension]

include o in
lemma putNew_norm_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (v : NewCoordinate E S M p → ℝ) :
    cochainNorm E Finset.univ M q p (putNew E S M p v) ≤ weightedNorm (CechObstruction.newWeight E S M q p) v := by
  classical
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (coordinateWeight_positive E Finset.univ M hq p) (weightedNorm_nonneg _ _)).2
  intro j
  by_cases hz : j.2.val ∈ projected E S (observation M j.1)
  · simp only [putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hz, abs_zero]
    exact mul_nonneg (weightedNorm_nonneg _ _) (coordinateWeight_positive E Finset.univ M hq p j).le
  · simp only [putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hz]
    exact coordinate_le_weightedNorm (x := v) (CechObstruction.newWeight_positive E S M o hq p) ⟨j.1, ⟨j.2, hz⟩⟩

include o in
lemma takeNew_norm_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (x : Cochain E Finset.univ M p) :
    weightedNorm (CechObstruction.newWeight E S M q p) (takeNew E S M p x) ≤ cochainNorm E Finset.univ M q p x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (CechObstruction.newWeight_positive E S M o hq p) (cochainNorm_nonneg E Finset.univ M q p x)).2
  intro j
  exact coordinate_le_weightedNorm (x := fun a => x a.1 a.2)
    (coordinateWeight_positive E Finset.univ M hq p) ⟨j.1, j.2.val⟩

lemma new_map_bound {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (v : NewCoordinate E S M p → ℝ) :
    weightedNorm (CechObstruction.newWeight E S N q p) ((windowMap E S M o N f hf p).newMap v) ≤
      weightedNorm (CechObstruction.newWeight E S M q p) v :=
  (takeNew_norm_le E S N o hq p _).trans
    ((cochain_nonexpansive E Finset.univ M o N f hf hq p _).trans (putNew_norm_le E S M o hq p v))

lemma cohomology_naturality (p : ℕ) (α : (window E S M o p).Cohomology) :
    cohomologyEquiv E S N o p ((windowMap E S M o N f hf p).cohomologyMap α) =
      cohomologyMap E S M N f hf p (cohomologyEquiv E S M o p α) := by
  induction α using Submodule.Quotient.induction_on with
  | H c => rfl

/-- Nonexpansion of the actual obstruction norm under arbitrary observation restriction. -/
theorem norm_nonexpansive {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : Cohomology E S M p) :
    CechObstruction.norm E S N o q p (cohomologyMap E S M N f hf p α) ≤
      CechObstruction.norm E S M o q p α := by
  have he : (cohomologyEquiv E S N o p).symm (cohomologyMap E S M N f hf p α) =
      (windowMap E S M o N f hf p).cohomologyMap ((cohomologyEquiv E S M o p).symm α) := by
    apply (cohomologyEquiv E S N o p).injective
    rw [LinearEquiv.apply_symm_apply, cohomology_naturality, LinearEquiv.apply_symm_apply]
  unfold CechObstruction.norm
  rw [he]
  exact (windowMap E S M o N f hf p).obstruction_nonexpansive
    (CechObstruction.newWeight_positive E S M o hq p) (new_map_bound E S M o N f hf hq p) _

end ObservationRestrictionNorm
end WeightedObstructionNorms
