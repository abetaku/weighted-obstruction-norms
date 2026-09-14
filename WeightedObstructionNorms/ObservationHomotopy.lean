import WeightedObstructionNorms.PrismEvaluation
import WeightedObstructionNorms.ObservationRestriction

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace WeightedObstructionNorms
namespace ObservationHomotopy
open FiniteObservations CechAllDegrees ObservationRestriction PrismEvaluation
variable {I K L : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [LinearOrder K] [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

def eligible {n : ℕ} (t : Tuple (K := K) n) : Tuple (K := Vertex M (observation M t)) n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨t i, fun a ha => (mem_observation M t a).1 ha i⟩) t.strictMono

lemma project_self (n : ℕ) (x : Cochain E S M n) (t : Tuple (K := K) n) :
    project E S M (observation M t) n x (eligible M t) = x t := by
  change Marginal.push (supportRestrict E S (contains M (eligible M t))) (x t) = x t
  exact Marginal.push_id _

lemma project_ext (n : ℕ) (x y : Cochain E S M n)
    (h : ∀ A, project E S M A n x = project E S M A n y) : x = y := by
  funext t
  simpa only [project_self] using congrFun (h (observation M t)) (eligible M t)

lemma pair_naturality {A B : Finset I} (h : A ⊆ B) (n : ℕ) (x : Cochain E S M n)
    (c : ListPrism.Chain (Vertex M B)) :
    marginal E S h (pair (project E S M B n x) c) =
      pair (project E S M A n x) (ListPrism.map (vertexInclude M h) c) := by
  rw [pair_linear, pair_map_orderEmbedding]
  congr 2
  funext t
  exact project_naturality E S M h n x t

variable (N : L → Finset I) (f g : L → K)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ a, N a ⊆ M (g a))

def homotopy (n : ℕ) (x : Cochain E S M (n + 1)) : Cochain E S N n := fun t =>
  PrismEvaluation.homotopy (vertexSelect M N f hf (observation N t))
    (vertexSelect M N g hg (observation N t)) n
    (project E S M (observation N t) (n + 1) x) (eligible N t)

lemma project_homotopy (A : Finset I) (n : ℕ) (x : Cochain E S M (n + 1)) :
    project E S N A n (homotopy E S M N f g hf hg n x) =
      PrismEvaluation.homotopy (vertexSelect M N f hf A) (vertexSelect M N g hg A) n
        (project E S M A (n + 1) x) := by
  funext t
  change marginal E S (contains N t) (pair _ (ListPrism.prism _ _ (ListPrism.atom _))) = _
  rw [pair_naturality]
  rw [ListPrism.prism_naturality (vertexInclude M (contains N t)) (vertexInclude N (contains N t))
    _ _ (vertexSelect M N f hf A) (vertexSelect M N g hg A) (fun _ => rfl) (fun _ => rfl)]
  rw [ListPrism.map_atom, List.map_ofFn]
  rfl

/-- The choice homotopy on the actual marginal complex, in all nonnegative degrees. -/
theorem homotopy_identity (n : ℕ) (x : Cochain E S M (n + 1)) :
    differential E S N n (homotopy E S M N f g hf hg n x) +
      homotopy E S M N f g hf hg (n + 1) (differential E S M (n + 1) x) =
        restriction E S M N g hg (n + 1) x - restriction E S M N f hf (n + 1) x := by
  apply project_ext E S N (n + 1)
  intro A
  rw [map_add, map_sub, project_differential, project_homotopy, project_homotopy,
    project_differential, project_restriction, project_restriction]
  exact PrismEvaluation.homotopy_identity _ _ n _

lemma homotopy_zero (n : ℕ) : homotopy E S M N f g hf hg n 0 = 0 := by
  funext t
  unfold homotopy PrismEvaluation.homotopy
  rw [map_zero]
  have hp : pair (0 : Tuple (K := Vertex M (observation N t)) (n + 1) → SupportState E S (observation N t) → ℝ) = 0 := by
    apply Finsupp.lhom_ext
    intro l r
    simp [pair, onList, AlternatingEvaluation.evaluate]
  rw [hp]
  rfl

/-- Different selections induce exactly the same map on the original cohomology. -/
theorem cohomologyMap_choice_independent (p : ℕ) (α : Cohomology E S M p) :
    cohomologyMap E S M N f hf p α = cohomologyMap E S M N g hg p α := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    rw [cohomologyMap_class, cohomologyMap_class]
    apply (Submodule.Quotient.eq _).2
    refine ⟨-homotopy E S M N f g hf hg p c.val, ?_⟩
    apply Subtype.ext
    have hh := homotopy_identity E S M N f g hf hg p c.val
    rw [c.property, homotopy_zero, add_zero] at hh
    change differential E S N p (-homotopy E S M N f g hf hg p c.val) = _
    rw [map_neg, hh]
    exact neg_sub _ _

end ObservationHomotopy
end WeightedObstructionNorms
