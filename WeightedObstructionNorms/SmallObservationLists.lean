import WeightedObstructionNorms.CechLowComparison

noncomputable section
namespace WeightedObstructionNorms
namespace SmallObservationLists
open FiniteObservations CechAllDegrees CechLowComparison

lemma push_surjective {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (hf : Function.Surjective f) :
    Function.Surjective (Marginal.push f : (A → ℝ) → B → ℝ) := by
  obtain ⟨g,hg⟩ := hf.hasRightInverse
  intro x
  refine ⟨Marginal.push g x, ?_⟩
  rw [Marginal.push_comp, show f ∘ g = id from funext hg, Marginal.push_id]

variable {I : Type*} [Fintype I] [DecidableEq I] (E : I → Type*)
  [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)] (S : Finset (State E))

lemma marginal_surjective {A B : Finset I} (h : A ⊆ B) : Function.Surjective (marginal E S h) := by
  apply push_surjective
  intro y
  obtain ⟨z,hz,he⟩ := (projected_mem E S A y.val).1 y.property
  refine ⟨⟨project E B z, (projected_mem E S B _).2 ⟨z,hz,rfl⟩⟩, ?_⟩
  exact Subtype.ext he

lemma single_augmentation_surjective (M : Fin 1 → Finset I) :
    Function.Surjective (CechLowDegrees.augmentation E S M) := by
  intro x
  have hp : Function.Surjective (CechLowDegrees.globalProject E S (M 0)) := by
    intro y
    obtain ⟨z,hz,he⟩ := (projected_mem E S (M 0) y.val).1 y.property
    exact ⟨⟨z,hz⟩,Subtype.ext he⟩
  obtain ⟨u,hu⟩ := push_surjective _ hp (x 0)
  refine ⟨u, ?_⟩
  funext i
  fin_cases i
  exact hu

/-- A single observation has no degree-zero obstruction, for every support. -/
theorem single_cohomology_zero (M : Fin 1 → Finset I) (α : Cohomology E S M 0) : α = 0 := by
  apply (cohomologyZero E S M).injective
  rw [map_zero]
  generalize cohomologyZero E S M α = β
  induction β using Submodule.Quotient.induction_on with
  | H c =>
    apply (Submodule.Quotient.mk_eq_zero _).2
    obtain ⟨u,hu⟩ := single_augmentation_surjective E S M c.val
    exact ⟨u,Subtype.ext hu⟩

lemma two_differential_surjective (M : Fin 2 → Finset I) :
    Function.Surjective (CechLowDegrees.d0 E S M) := by
  intro y
  let p : CechLowDegrees.Pair (K := Fin 2) := ⟨(0,1),by decide⟩
  obtain ⟨u,hu⟩ := marginal_surjective E S (Finset.inter_subset_right (s₁ := M 0)) (y p)
  let x : CechLowDegrees.C0 E S M := fun i => Fin.cases 0 (Fin.cases u (fun k => Fin.elim0 k)) i
  refine ⟨x, ?_⟩
  funext t
  have ht : t = p := by
    rcases t with ⟨⟨i,j⟩,h⟩
    fin_cases i <;> fin_cases j <;> try (exfalso; exact (by decide : ¬ _) h)
    rfl
  subst t
  change marginal E S (Finset.inter_subset_right (s₁ := M 0)) u -
    marginal E S (Finset.inter_subset_left (s₂ := M 1)) 0 = y p
  rw [map_zero, sub_zero]
  exact hu

/-- Any two-observation list has no degree-one obstruction, for every support. -/
theorem two_cohomology_zero (M : Fin 2 → Finset I) (α : Cohomology E S M 1) : α = 0 := by
  apply (cohomologyOne E S M).injective
  rw [map_zero]
  generalize cohomologyOne E S M α = β
  induction β using Submodule.Quotient.induction_on with
  | H c =>
    apply (Submodule.Quotient.mk_eq_zero _).2
    obtain ⟨u,hu⟩ := two_differential_surjective E S M c.val
    exact ⟨u,Subtype.ext hu⟩

end SmallObservationLists
end WeightedObstructionNorms
