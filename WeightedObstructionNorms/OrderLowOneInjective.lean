import WeightedObstructionNorms.OrderPrimitiveComparison

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace OrderLowOneInjective
open FiniteObservations CechAllDegrees CechLowComparison
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I))

def liftPair (p : CechLowDegrees.Pair (K := OrderComplex.Index O)) :
    CechLowDegrees.Pair (K := OrderComparison.ListIndex O) :=
  ⟨p.val, lt_of_le_of_ne (toLinearExtension.monotone p.property.le) (fun h => p.property.ne h)⟩

lemma restriction_degree_one (x : Cochain E S (OrderComparison.list O) 2)
    (p : CechLowDegrees.Pair (K := OrderComplex.Index O)) :
    degreeOne E S (OrderComplex.observations O) (OrderComparison.restriction E S O 2 x) p =
      degreeOne E S (OrderComparison.list O) x (liftPair O p) := by
  change coefficientCongr E S _ (OrderComparison.restriction E S O 2 x (twoTuple p)) = _
  rw [OrderComparison.restriction_apply]
  rfl

lemma marginal_injective_of_eq {A B : Finset I} (h : A ⊆ B) (he : A = B) :
    Function.Injective (marginal E S h) := by
  subst B
  intro x y hxy
  have hx : marginal E S h x = x := Marginal.push_id _
  have hy : marginal E S h y = y := Marginal.push_id _
  rwa [hx, hy] at hxy

variable (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

include hO in
/-- A closed Cech 1-cochain is determined by its values on inclusions. -/
lemma old_cycle_zero (y : CechLowDegrees.C1 E S (OrderComparison.list O))
    (hy : CechLowDegrees.d1 E S (OrderComparison.list O) y = 0)
    (hz : ∀ p, y (liftPair O p) = 0) : y = 0 := by
  funext q
  let A : OrderComplex.Index O := q.val.1
  let B : OrderComplex.Index O := q.val.2
  by_cases hAB : A.val ⊆ B.val
  · let p : CechLowDegrees.Pair (K := OrderComplex.Index O) :=
      ⟨(A, B), lt_of_le_of_ne hAB (fun he => q.property.ne he)⟩
    exact hz p
  · let T : OrderComplex.Index O := ⟨A.val ∩ B.val, hO A.val A.property _ Finset.inter_subset_left⟩
    have hTA : T < A := lt_iff_le_not_le.mpr ⟨Finset.inter_subset_left,
      fun h => hAB (h.trans Finset.inter_subset_right)⟩
    have hTB : T < B := by
      apply lt_iff_le_not_le.mpr
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro h
      have hBA : B ≤ A := h.trans Finset.inter_subset_left
      have hBA' := (toLinearExtension (α := OrderComplex.Index O)).monotone hBA
      exact not_le_of_gt q.property hBA' 
    let pTA : CechLowDegrees.Pair (K := OrderComplex.Index O) := ⟨(T, A), hTA⟩
    let pTB : CechLowDegrees.Pair (K := OrderComplex.Index O) := ⟨(T, B), hTB⟩
    let w : CechLowDegrees.Triple (K := OrderComparison.ListIndex O) :=
      ⟨(T, A, B), (liftPair O pTA).property, q.property⟩
    have hc := congrFun hy w
    change marginal E S (CechLowDegrees.subset12 (OrderComparison.list O) w) (y q) -
        marginal E S (CechLowDegrees.subset02 (OrderComparison.list O) w) (y (liftPair O pTB)) +
        marginal E S (CechLowDegrees.subset01 (OrderComparison.list O) w) (y (liftPair O pTA)) = 0 at hc
    rw [hz pTB, hz pTA, map_zero, map_zero, sub_zero, add_zero] at hc
    have he : CechLowDegrees.tripleObservation (OrderComparison.list O) w =
        CechLowDegrees.pairObservation (OrderComparison.list O) q := by
      change ((T.val ∩ A.val) ∩ B.val) = A.val ∩ B.val
      rw [Finset.inter_eq_left.mpr hTA.le, Finset.inter_eq_left.mpr hTB.le]
    apply marginal_injective_of_eq E S (CechLowDegrees.subset12 (OrderComparison.list O) w) he
    simpa only [Pi.zero_apply, map_zero] using hc

include hO in
theorem cycle_zero (z : Cochain E S (OrderComparison.list O) 2)
    (hz : differential E S (OrderComparison.list O) 2 z = 0)
    (hR : OrderComparison.restriction E S O 2 z = 0) : z = 0 := by
  apply (degreeOne E S (OrderComparison.list O)).injective
  rw [map_zero]
  apply old_cycle_zero E S O hO
  · rw [← differential_one, hz, map_zero]
  · intro p
    rw [← restriction_degree_one, hR, map_zero]
    rfl

variable (o : State E)

include o hO in
/-- The primitive minimum is unchanged in degree one, for every positive reference weight. -/
theorem cost_eq_one {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (c : LinearMap.ker (differential E S (OrderComparison.list O) 2)) :
    CechPrimitive.cost E S (OrderComplex.observations O) q 1 (OrderComparison.restriction E S O 2 c.val) =
      CechPrimitive.cost E S (OrderComparison.list O) q 1 c.val :=
  OrderPrimitiveComparison.cost_eq E S O o hq 1 (OrderComparison.chainTuple_surjective_one O)
    (cycle_zero E Finset.univ O hO) c

/-- Equality of the actual degree-one obstruction norms under R. -/
theorem norm_eq_one {q : State E → ℝ} (hq : ∀ z, 0 < q z) (α : Cohomology E S (OrderComparison.list O) 1) :
    OrderObstruction.norm E S O o hO q 1 (OrderComparison.cohomologyMap E S O 1 α) =
      CechObstruction.norm E S (OrderComparison.list O) o q 1 α :=
  OrderPrimitiveComparison.norm_eq E S O o hO 1 (OrderComparison.chainTuple_surjective_one O)
    (cycle_zero E Finset.univ O hO) hq α

end OrderLowOneInjective
end WeightedObstructionNorms
