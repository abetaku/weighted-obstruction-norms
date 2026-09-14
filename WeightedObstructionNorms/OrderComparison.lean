import WeightedObstructionNorms.OrderRestrictionNorm
import Mathlib.Order.Extension.Linear
import WeightedObstructionNorms.ObservationRestriction0
import WeightedObstructionNorms.CechLowComparison

noncomputable section
namespace WeightedObstructionNorms
namespace OrderComparison
open FiniteObservations CechAllDegrees AlternatingEvaluation
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I))

abbrev ListIndex := LinearExtension (OrderComplex.Index O)
instance listIndexFintype : Fintype (ListIndex O) := inferInstanceAs (Fintype (OrderComplex.Index O))
def list : ListIndex O → Finset I := fun a => (show OrderComplex.Index O from a).val

def selection : OrderComplex.Index O → ListIndex O := toLinearExtension
lemma selection_valid : ∀ a, a.val ⊆ list O (selection O a) := fun _ => Finset.Subset.refl _

def chainTuple {n : ℕ} (t : Tuple (K := OrderComplex.Index O) n) : Tuple (K := ListIndex O) n :=
  OrderEmbedding.ofStrictMono (selection O ∘ t) (by
    intro a b hab
    apply lt_of_le_of_ne
    · exact toLinearExtension.monotone (t.monotone hab.le)
    · intro h
      exact (ne_of_lt hab) (t.injective h))

/-- The actual comparison R from the manuscript's all-observation Cech list. -/
def restriction (n : ℕ) := OrderRestriction.restriction E S (list O) O (selection O) (selection_valid O) n

/-- Because the total order extends inclusion, R is literally restriction to chains. -/
lemma restriction_apply (n : ℕ) (x : Cochain E S (list O) n) (t : Tuple (K := OrderComplex.Index O) n) :
    restriction E S O n x t = x (chainTuple O t) := by
  let u : Tuple (K := ObservationRestriction.Vertex (list O) (observation (OrderComplex.observations O) t)) n :=
    OrderEmbedding.ofStrictMono (OrderRestriction.selected (list O) O (selection O) (selection_valid O) t)
      (chainTuple O t).strictMono
  change evaluate (ObservationRestriction.project E S (list O)
    (observation (OrderComplex.observations O) t) n x) u = _
  rw [evaluate_ordered]
  change Marginal.push (supportRestrict E S (ObservationRestriction.contains (list O) u)) (x (chainTuple O t)) = _
  exact Marginal.push_id _

lemma restriction_augmentation (x : {z // z ∈ S} → ℝ) :
    restriction E S O 0 (augmentationEquiv E S (list O) x) =
      augmentationEquiv E S (OrderComplex.observations O) x := by
  funext t
  rw [restriction_apply, augmentationEquiv_push, augmentationEquiv_push]
  rfl

def cohomologyMap (p : ℕ) := OrderRestriction.cohomologyMap E S (list O) O (selection O) (selection_valid O) p

lemma chainTuple_injective (n : ℕ) : Function.Injective (chainTuple O (n := n)) := by
  intro t u h
  apply DFunLike.ext
  intro i
  exact congrArg (fun v : Tuple (K := ListIndex O) n => v i) h

lemma chainTuple_surjective_zero : Function.Surjective (chainTuple O (n := 0)) := by
  intro t
  refine ⟨emptyTuple, ?_⟩
  ext i
  exact Fin.elim0 i

lemma chainTuple_surjective_one : Function.Surjective (chainTuple O (n := 1)) := by
  intro t
  refine ⟨CechLowComparison.oneTuple (t 0 : OrderComplex.Index O), ?_⟩
  ext i
  fin_cases i
  rfl

def cochainEquiv (n : ℕ) (h : Function.Surjective (chainTuple O (n := n))) :
    Cochain E S (list O) n ≃ₗ[ℝ] OrderComplex.Cochain E O S n :=
  CechLowComparison.cochainEquiv E S (list O)
    (Equiv.ofBijective (chainTuple O) ⟨chainTuple_injective O n, h⟩)
    (fun t => observation (OrderComplex.observations O) t) (fun _ => rfl)

lemma cochainEquiv_apply (n : ℕ) (h : Function.Surjective (chainTuple O (n := n)))
    (x : Cochain E S (list O) n) : cochainEquiv E S O n h x = restriction E S O n x := by
  funext t
  rw [restriction_apply]
  rfl

lemma cochain_norm_eq_of_surjective (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (n : ℕ) (h : Function.Surjective (chainTuple O (n := n))) (x : Cochain E S (list O) n) :
    cochainNorm E S (OrderComplex.observations O) q n (restriction E S O n x) =
      cochainNorm E S (list O) q n x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply le_antisymm (OrderRestriction.cochain_nonexpansive E S (list O) O (selection O) (selection_valid O) o hq n x)
  apply (weightedNorm_le_iff (coordinateWeight_positive E S (list O) hq n) (cochainNorm_nonneg _ _ _ _ _ _)).2
  intro j
  obtain ⟨t, ht⟩ := h j.1
  rcases j with ⟨s, z⟩
  dsimp only at ht
  subst s
  have hh := coordinate_le_weightedNorm (x := fun a => restriction E S O n x a.1 a.2)
    (coordinateWeight_positive E S (OrderComplex.observations O) hq n) ⟨t, z⟩
  rw [restriction_apply] at hh
  exact hh

variable (o : State E) (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

/-- Proposition A.1, its all-degree one-sided inequality. -/
theorem norm_nonexpansive {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : Cohomology E S (list O) p) :
    OrderObstruction.norm E S O o hO q p (cohomologyMap E S O p α) ≤
      CechObstruction.norm E S (list O) o q p α :=
  OrderRestrictionNorm.norm_nonexpansive E S (list O) o O (selection O) (selection_valid O) hO hq p α

include hO in
lemma generated_list : CechLowDegrees.generated (list O) = ↑O := by
  ext A
  constructor
  · rintro ⟨B, hAB⟩
    exact hO B.val B.property A hAB
  · intro hA
    exact ⟨(⟨A, hA⟩ : OrderComplex.Index O), Finset.Subset.refl _⟩

end OrderComparison
end WeightedObstructionNorms
