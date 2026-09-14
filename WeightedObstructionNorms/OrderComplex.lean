import WeightedObstructionNorms.FullSupportAcyclicity
import WeightedObstructionNorms.CechWeights
import WeightedObstructionNorms.CechLowComparison

noncomputable section
namespace WeightedObstructionNorms
namespace OrderComplex
open FiniteObservations CechAllDegrees
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (O : Finset (Finset I))

abbrev Index := {A // A ∈ O}
instance indexFintype : Fintype (Index O) := Fintype.ofFinite _
def observations : Index O → Finset I := Subtype.val

/-- The inclusion-chain complex. Index n corresponds to paper degree n-1. -/
abbrev Cochain (S : Finset (State E)) (n : ℕ) := CechAllDegrees.Cochain E S (observations O) n
abbrev differential (S : Finset (State E)) (n : ℕ) := CechAllDegrees.differential E S (observations O) n
abbrev Cohomology (S : Finset (State E)) (p : ℕ) := CechAllDegrees.Cohomology E S (observations O) p

/-- The intersection on an inclusion chain is exactly its least observation. -/
lemma observation_head {n : ℕ} (t : Tuple (K := Index O) (n + 1)) :
    observation (observations O) t = (t 0).val := by
  ext a
  rw [mem_observation]
  constructor
  · intro h; exact h 0
  · intro h i
    exact (t.monotone (Fin.zero_le i)) h

theorem differential_squared (S : Finset (State E)) (n : ℕ) (x : Cochain E O S n) :
    differential E O S (n + 1) (differential E O S n x) = 0 :=
  CechAllDegrees.differential_squared E S (observations O) n x

lemma observation_face_zero {n : ℕ} (t : Tuple (K := Index O) (n + 2)) :
    observation (observations O) (face 0 t) = (t 1).val := observation_head O (face 0 t)

lemma observation_face_succ {n : ℕ} (t : Tuple (K := Index O) (n + 2)) (i : Fin (n + 1)) :
    observation (observations O) (face i.succ t) = (t 0).val := by
  rw [observation_head]
  have h : face i.succ t 0 = t 0 := by simp [face]
  rw [h]

/-- Exactly equation (A.1): only the first face marginalizes; all other faces keep the least observation. -/
theorem differential_formula (S : Finset (State E)) (n : ℕ) (x : Cochain E O S (n + 1))
    (t : Tuple (K := Index O) (n + 2)) :
    CechLowComparison.coefficientCongr E S (observation_head O t) (differential E O S (n + 1) x t) =
      marginal E S (t.monotone (Fin.zero_le 1))
        (CechLowComparison.coefficientCongr E S (observation_face_zero O t) (x (face 0 t))) +
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i.val + 1) •
        CechLowComparison.coefficientCongr E S (observation_face_succ O t i) (x (face i.succ t)) := by
  simp only [differential, CechAllDegrees.differential, coface, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fin.sum_univ_succ, map_add, map_sum]
  simp only [Fin.val_zero, pow_zero, one_smul, map_smul, Fin.val_succ]
  apply congrArg₂ (· + ·)
  · exact CechLowComparison.coefficientCongr_marginal E S (observation_head O t)
      (observation_face_zero O t) _ _ (x (face 0 t))
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    have h := CechLowComparison.coefficientCongr_marginal E S (observation_head O t)
      (observation_face_succ O t i) (observation_face (observations O) i.succ t) (Finset.Subset.refl (t 0).val) (x (face i.succ t))
    exact h.trans (Marginal.push_id _)

variable (o : State E) (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

include hO in
/-- Each nonempty interaction component has its interaction support as least element. -/
lemma component_exact : FullSupportAcyclicity.ComponentExact E o (observations O) := by
  classical
  intro y n x hx
  let V := FullSupportAcyclicity.Vertex E o (observations O) y
  cases isEmpty_or_nonempty V with
  | inl hempty =>
    letI := hempty
    refine ⟨0, ?_⟩
    funext t
    exact isEmptyElim (t 0)
  | inr hnonempty =>
    let B := Finset.univ.filter (fun i => y i ≠ o i)
    have hB : B ∈ O := by
      obtain ⟨v⟩ := hnonempty
      apply hO v.val.val v.val.property B
      intro i hi
      exact v.property i (Finset.mem_filter.mp hi).2
    let b : V := ⟨⟨B, hB⟩, fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    letI : OrderBot V := {
      bot := b
      bot_le := by
        intro v i hi
        exact v.property i (Finset.mem_filter.mp hi).2 }
    exact ⟨SimplexContraction.contraction n x, SimplexContraction.primitive_of_closed n x hx⟩

include o hO in
/-- Full-support acyclicity for the actual order-complex marginal differential. -/
theorem full_exists_primitive (n : ℕ) (x : Cochain E O Finset.univ (n + 1))
    (hx : differential E O Finset.univ (n + 1) x = 0) :
    ∃ u, differential E O Finset.univ n u = x :=
  FullSupportAcyclicity.full_exists_primitive_of_components E o (observations O)
    (component_exact E O o hO) n x hx

include o hO in
theorem full_cohomology_eq_zero (p : ℕ) (α : Cohomology E O Finset.univ p) : α = 0 := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply (Submodule.Quotient.mk_eq_zero _).2
    obtain ⟨u, hu⟩ := full_exists_primitive E O o hO p c.val c.property
    exact ⟨u, Subtype.ext hu⟩

end OrderComplex
end WeightedObstructionNorms
