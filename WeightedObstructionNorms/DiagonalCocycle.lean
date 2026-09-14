import WeightedObstructionNorms.DiagonalCoordinates

noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalCocycle
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees CechSplitting
open CechLowComparison DiagonalCoordinates

lemma full_at_one (t : Tuple (K := Fin 2) 1) :
    projected E S (observation M t) = projected E Finset.univ (observation M t) := by
  obtain ⟨i,rfl⟩ := (oneEquiv (K := Fin 2)).surjective t
  rw [show oneEquiv i = oneTuple i from rfl, one_observation]
  exact singleton_support i
lemma extension_takeOld (x : Cochain E Finset.univ M 1) :
    extension E S M (Finset.subset_univ S) 1 (takeOld E S M 1 x) = x := by
  funext t z
  have hz : z.val ∈ projected E S (observation M t) := by rw [full_at_one]; exact z.property
  let w : SupportState E S (observation M t) := ⟨z.val,hz⟩
  have he : supportInclude E (Finset.subset_univ S) _ w = z := Subtype.ext rfl
  change Marginal.push (supportInclude E (Finset.subset_univ S) _) (takeOld E S M 1 x t) z = x t z
  rw [← he, Marginal.push_injective_apply _ (supportInclude_injective E (Finset.subset_univ S) _)]
  rfl

def primitiveMeasure : BinaryExamples.PairMeasure := ⟨1/2,1/2,-1/2,-1/2⟩
def witness : Cochain E Finset.univ M 0 := augmentationEquiv E Finset.univ M (decode primitiveMeasure)
def c : Cochain E S M 1 := takeOld E S M 1 (differential E Finset.univ M 0 witness)
lemma extension_c : extension E S M (Finset.subset_univ S) 1 c =
    differential E Finset.univ M 0 witness := extension_takeOld _
lemma c_closed : differential E S M 1 c = 0 := by
  apply extension_injective E S M (Finset.subset_univ S) 2
  rw [map_zero, ← extension_differential, extension_c, differential_squared]
def cycle : LinearMap.ker (differential E S M 1) := ⟨c,c_closed⟩
def obstructionClass : Cohomology E S M 0 := Submodule.Quotient.mk cycle

lemma eval_extension_c (i a : Bit) :
    eval (degreeZero E Finset.univ M (extension E S M (Finset.subset_univ S) 1 c)) i a =
      if i = 0 then if a = 1 then 1 else -1 else 0 := by
  rw [extension_c]
  change eval (degreeZero E Finset.univ M (differential E Finset.univ M 0
    (augmentationEquiv E Finset.univ M (decode primitiveMeasure)))) i a = _
  rw [CechLowComparison.augmentation]
  fin_cases i
  · refine (augmentation_first (decode primitiveMeasure) a).trans ?_
    fin_cases a <;> norm_num [primitiveMeasure]
  · refine (augmentation_second (decode primitiveMeasure) a).trans ?_
    fin_cases a <;> norm_num [primitiveMeasure]

def Feasible (y : BinaryExamples.PairMeasure) : Prop :=
  y.pp + y.pm = 1 ∧ y.mp + y.mm = -1 ∧ y.pp + y.mp = 0 ∧ y.pm + y.mm = 0

lemma four_values (f g : Bit → Bit → ℝ) : f = g ↔
    f 0 1 = g 0 1 ∧ f 0 0 = g 0 0 ∧ f 1 1 = g 1 1 ∧ f 1 0 = g 1 0 := by
  constructor
  · intro h; subst g; exact ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨h01,h00,h11,h10⟩
    funext i a
    fin_cases i <;> fin_cases a
    · exact h00
    · exact h01
    · exact h10
    · exact h11

lemma feasible_iff (u : Global) :
    differential E Finset.univ M 0 (augmentationEquiv E Finset.univ M u) =
      extension E S M (Finset.subset_univ S) 1 c ↔ Feasible (encode u) := by
  rw [← (degreeZero E Finset.univ M).injective.eq_iff, ← eval_injective.eq_iff, four_values]
  simp only [CechLowComparison.augmentation, eval_extension_c]
  rw [augmentation_first u 1,augmentation_first u 0,augmentation_second u 1,augmentation_second u 0]
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  norm_num only [ite_true, ite_false, Fin.isValue, zero_ne_one, one_ne_zero, OfNat.ofNat_ne_zero]
  simp only [encode, add_comm]

end DiagonalCocycle
end WeightedObstructionNorms
