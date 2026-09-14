import WeightedObstructionNorms.Marginal
import Mathlib.Data.Fintype.Pi

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace FiniteObservations

variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)]

abbrev State := ∀ i, E i
abbrev LocalState (A : Finset I) := ∀ i : A, E i.val

def project (A : Finset I) (z : State E) : LocalState E A := fun i => z i.val

def restrict {A B : Finset I} (h : A ⊆ B) (x : LocalState E B) : LocalState E A :=
  fun i => x ⟨i.val, h i.property⟩

lemma restrict_project {A B : Finset I} (h : A ⊆ B) (z : State E) :
    restrict E h (project E B z) = project E A z := rfl

lemma restrict_comp {A B C : Finset I} (hAB : A ⊆ B) (hBC : B ⊆ C) (x : LocalState E C) :
    restrict E hAB (restrict E hBC x) = restrict E (hAB.trans hBC) x := rfl

/-- Projection of a prescribed support onto an observation. -/
def projected (S : Finset (State E)) (A : Finset I) : Finset (LocalState E A) := by
  classical
  exact S.image (project E A)

abbrev SupportState (S : Finset (State E)) (A : Finset I) := {x // x ∈ projected E S A}

lemma projected_mem (S : Finset (State E)) (A : Finset I) (x : LocalState E A) :
    x ∈ projected E S A ↔ ∃ z ∈ S, project E A z = x := by
  classical
  exact Finset.mem_image

def supportRestrict (S : Finset (State E)) {A B : Finset I} (h : A ⊆ B)
    (x : SupportState E S B) : SupportState E S A := ⟨restrict E h x.val, by
  obtain ⟨z, hz, hzx⟩ := (projected_mem E S B x.val).1 x.property
  apply (projected_mem E S A _).2
  exact ⟨z, hz, congrArg (restrict E h) hzx⟩⟩

def supportInclude {S T : Finset (State E)} (h : S ⊆ T) (A : Finset I)
    (x : SupportState E S A) : SupportState E T A := ⟨x.val, by
  obtain ⟨z, hz, hzx⟩ := (projected_mem E S A x.val).1 x.property
  exact (projected_mem E T A x.val).2 ⟨z, h hz, hzx⟩⟩

lemma supportInclude_injective {S T : Finset (State E)} (h : S ⊆ T) (A : Finset I) :
    Function.Injective (supportInclude E h A) := by
  intro x y hxy
  exact Subtype.ext (congrArg (fun x : SupportState E T A => x.val) hxy)

lemma supportRestrict_comp (S : Finset (State E)) {A B C : Finset I}
    (hAB : A ⊆ B) (hBC : B ⊆ C) :
    supportRestrict E S hAB ∘ supportRestrict E S hBC = supportRestrict E S (hAB.trans hBC) := rfl

lemma support_square {S T : Finset (State E)} (hST : S ⊆ T) {A B : Finset I} (hAB : A ⊆ B) :
    supportRestrict E T hAB ∘ supportInclude E hST B =
      supportInclude E hST A ∘ supportRestrict E S hAB := rfl

/-- Signed local measures and their marginal map. -/
def marginal (S : Finset (State E)) {A B : Finset I} (h : A ⊆ B) :
    (SupportState E S B → ℝ) →ₗ[ℝ] (SupportState E S A → ℝ) :=
  Marginal.linear (supportRestrict E S h)

def extend {S T : Finset (State E)} (h : S ⊆ T) (A : Finset I) :
    (SupportState E S A → ℝ) →ₗ[ℝ] (SupportState E T A → ℝ) :=
  Marginal.linear (supportInclude E h A)

lemma marginal_comp (S : Finset (State E)) {A B C : Finset I}
    (hAB : A ⊆ B) (hBC : B ⊆ C) (x : SupportState E S C → ℝ) :
    marginal E S hAB (marginal E S hBC x) = marginal E S (hAB.trans hBC) x := by
  change Marginal.push _ (Marginal.push _ x) = Marginal.push _ x
  rw [Marginal.push_comp]
  rfl

/-- The support extension square for the actual projected supports. -/
theorem extension_commutes {S T : Finset (State E)} (hST : S ⊆ T) {A B : Finset I}
    (hAB : A ⊆ B) (x : SupportState E S B → ℝ) :
    marginal E T hAB (extend E hST B x) = extend E hST A (marginal E S hAB x) := by
  change Marginal.push _ (Marginal.push _ x) = Marginal.push _ (Marginal.push _ x)
  rw [Marginal.push_comp, Marginal.push_comp]
  rfl

lemma extension_injective {S T : Finset (State E)} (hST : S ⊆ T) (A : Finset I) :
    Function.Injective (extend E hST A) :=
  Marginal.push_injective _ (supportInclude_injective E hST A)

/-- Full-support marginal weights are the pushforwards of the reference law. -/
def weight (q : State E → ℝ) (A : Finset I) : LocalState E A → ℝ :=
  Marginal.push (project E A) q

lemma weight_marginal (q : State E → ℝ) {A B : Finset I} (h : A ⊆ B) :
    Marginal.push (restrict E h) (weight E q B) = weight E q A := by
  rw [weight, Marginal.push_comp]
  rfl

lemma project_surjective [∀ i, Nonempty (E i)] (A : Finset I) :
    Function.Surjective (project E A) := by
  classical
  intro x
  let z : State E := fun i => if hi : i ∈ A then x ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty (E i))
  refine ⟨z, ?_⟩
  funext i
  simp [project, z, i.property]

lemma weight_positive [∀ i, Nonempty (E i)] {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (A : Finset I) (x : LocalState E A) : 0 < weight E q A x := by
  classical
  obtain ⟨z, hz⟩ := project_surjective E A x
  apply Finset.sum_pos'
  · intro y _
    split_ifs
    · exact (hq y).le
    · exact le_rfl
  · refine ⟨z, Finset.mem_univ z, ?_⟩
    simpa [hz] using hq z

/-- Equation (5.2) with the reference weights derived from the actual product
state space, rather than supplied as unrelated coordinate weights. -/
theorem weighted_marginal_contraction [∀ i, Nonempty (E i)] {q : State E → ℝ}
    (hq : ∀ z, 0 < q z) {A B : Finset I} (h : A ⊆ B) (x : LocalState E B → ℝ) :
    weightedNorm (weight E q A) (Marginal.push (restrict E h) x) ≤ weightedNorm (weight E q B) x := by
  have hnorm := Marginal.weightedNorm_contraction (restrict E h)
    (weight_positive E hq B) (by rw [weight_marginal]; exact weight_positive E hq A) (x := x)
  simpa [weight_marginal] using hnorm

end FiniteObservations
end WeightedObstructionNorms
