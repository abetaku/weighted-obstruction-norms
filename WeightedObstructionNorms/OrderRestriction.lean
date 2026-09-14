import WeightedObstructionNorms.OrderComplex
import WeightedObstructionNorms.ObservationRestrictionNorm

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace OrderRestriction
open FiniteObservations CechAllDegrees AlternatingEvaluation
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)
    (O : Finset (Finset I)) (f : OrderComplex.Index O → K) (hf : ∀ a, a.val ⊆ M (f a))

def selected {n : ℕ} (t : Tuple (K := OrderComplex.Index O) n) :
    Fin n → ObservationRestriction.Vertex M (observation (OrderComplex.observations O) t) :=
  fun i => ⟨f (t i), fun a ha => hf (t i) ((mem_observation _ t a).1 ha i)⟩

lemma selected_face {n : ℕ} (t : Tuple (K := OrderComplex.Index O) (n + 1)) (i : Fin (n + 1)) :
    ObservationRestriction.vertexInclude M (observation_face (OrderComplex.observations O) i t) ∘ selected M O f hf (face i t) =
      selected M O f hf t ∘ i.succAbove := rfl

/-- The Cech-to-inclusion-chain comparison with all coefficient maps explicit. -/
def restriction (n : ℕ) : Cochain E S M n →ₗ[ℝ] OrderComplex.Cochain E O S n where
  toFun x t := evaluate (ObservationRestriction.project E S M (observation (OrderComplex.observations O) t) n x)
    (selected M O f hf t)
  map_add' x y := by funext t; rw [map_add, evaluate_add]; rfl
  map_smul' a x := by funext t; rw [map_smul, evaluate_smul]; rfl

theorem restriction_differential (n : ℕ) (x : Cochain E S M n) :
    OrderComplex.differential E O S n (restriction E S M O f hf n x) =
      restriction E S M O f hf (n + 1) (differential E S M n x) := by
  funext t
  change _ = evaluate (ObservationRestriction.project E S M (observation (OrderComplex.observations O) t) (n + 1)
    (differential E S M n x)) (selected M O f hf t)
  rw [ObservationRestriction.project_differential, evaluate_differential]
  conv_lhs => simp only [OrderComplex.differential, differential, coface, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, restriction]
  unfold rawDifferential
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [ObservationRestriction.evaluate_naturality, selected_face]

theorem restriction_extension {T : Finset (State E)} (hST : S ⊆ T) (n : ℕ) (x : Cochain E S M n) :
    restriction E T M O f hf n (extension E S M hST n x) =
      extension E S (OrderComplex.observations O) hST n (restriction E S M O f hf n x) := by
  funext t
  change evaluate (ObservationRestriction.project E T M (observation (OrderComplex.observations O) t) n
    (extension E S M hST n x)) _ = _
  rw [ObservationRestriction.project_extension, ← evaluate_linear]
  rfl

include hf in
theorem cochain_nonexpansive (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (n : ℕ) (x : Cochain E S M n) :
    cochainNorm E S (OrderComplex.observations O) q n (restriction E S M O f hf n x) ≤ cochainNorm E S M q n x := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  apply (weightedNorm_le_iff (coordinateWeight_positive E S (OrderComplex.observations O) hq n)
    (cochainNorm_nonneg E S M q n x)).2
  intro j
  exact ObservationRestrictionNorm.evaluate_box E S M o hq _ n x _ j.2

def cycleMap (p : ℕ) : LinearMap.ker (differential E S M (p + 1)) →ₗ[ℝ]
    LinearMap.ker (OrderComplex.differential E O S (p + 1)) :=
  ((restriction E S M O f hf (p + 1)).domRestrict _).codRestrict _ (fun c => by
    change OrderComplex.differential E O S (p + 1) (restriction E S M O f hf (p + 1) c.val) = 0
    rw [restriction_differential, c.property, map_zero])

lemma boundaries_map (p : ℕ) : LinearMap.range (boundaries E S M p) ≤
    LinearMap.ker ((LinearMap.range (boundaries E S (OrderComplex.observations O) p)).mkQ.comp (cycleMap E S M O f hf p)) := by
  rintro c ⟨u, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨restriction E S M O f hf p u, Subtype.ext (restriction_differential E S M O f hf p u)⟩

def cohomologyMap (p : ℕ) : Cohomology E S M p →ₗ[ℝ] OrderComplex.Cohomology E O S p :=
  (LinearMap.range (boundaries E S M p)).liftQ
    ((LinearMap.range (boundaries E S (OrderComplex.observations O) p)).mkQ.comp (cycleMap E S M O f hf p))
    (boundaries_map E S M O f hf p)

end OrderRestriction
end WeightedObstructionNorms
