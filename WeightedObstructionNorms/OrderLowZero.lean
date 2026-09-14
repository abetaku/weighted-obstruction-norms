import WeightedObstructionNorms.OrderComparison

noncomputable section
namespace WeightedObstructionNorms
namespace OrderLowZero
open FiniteObservations CechAllDegrees CechLowComparison
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I))

lemma closed_marginal_inclusion (x : CechLowDegrees.C0 E S (OrderComplex.observations O))
    (hx : CechLowDegrees.d0 E S (OrderComplex.observations O) x = 0)
    (A B : OrderComplex.Index O) (h : A.val ⊆ B.val) : marginal E S h (x B) = x A := by
  by_cases he : A = B
  · subst B
    exact Marginal.push_id _
  · let p : CechLowDegrees.Pair (K := OrderComplex.Index O) := ⟨(A, B), lt_of_le_of_ne h he⟩
    have hc := congrArg (coefficientCongr E S (Finset.inter_eq_left.mpr h)) (congrFun hx p)
    change coefficientCongr E S (Finset.inter_eq_left.mpr h)
      (marginal E S Finset.inter_subset_right (x B) - marginal E S Finset.inter_subset_left (x A)) = _ at hc
    rw [map_sub, Pi.zero_apply, map_zero] at hc
    have hb : coefficientCongr E S (Finset.inter_eq_left.mpr h)
        (marginal E S Finset.inter_subset_right (x B)) = marginal E S h (x B) :=
      coefficientCongr_marginal E S (Finset.inter_eq_left.mpr h) (rfl : B.val = B.val)
        Finset.inter_subset_right h (x B)
    have ha : coefficientCongr E S (Finset.inter_eq_left.mpr h)
        (marginal E S Finset.inter_subset_left (x A)) = x A := by
      have hh := coefficientCongr_marginal E S (Finset.inter_eq_left.mpr h) (rfl : A.val = A.val)
        Finset.inter_subset_left (Finset.Subset.refl A.val) (x A)
      exact hh.trans (Marginal.push_id _)
    exact sub_eq_zero.mp ((congrArg₂ (· - ·) hb.symm ha.symm).trans hc)

variable (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

include hO in
/-- Compatibility on inclusions implies compatibility on every intersection. -/
lemma closed_from_order (x : CechLowDegrees.C0 E S (OrderComplex.observations O))
    (hx : CechLowDegrees.d0 E S (OrderComplex.observations O) x = 0) :
    CechLowDegrees.d0 E S (OrderComparison.list O) x = 0 := by
  funext p
  let A : OrderComplex.Index O := p.val.1
  let B : OrderComplex.Index O := p.val.2
  let T : OrderComplex.Index O := ⟨A.val ∩ B.val, hO A.val A.property _ Finset.inter_subset_left⟩
  change marginal E S Finset.inter_subset_right (x B) - marginal E S Finset.inter_subset_left (x A) = 0
  exact sub_eq_zero.mpr ((closed_marginal_inclusion E S O x hx T B Finset.inter_subset_right).trans
    (closed_marginal_inclusion E S O x hx T A Finset.inter_subset_left).symm)

lemma closed_to_order (x : CechLowDegrees.C0 E S (OrderComparison.list O))
    (hx : CechLowDegrees.d0 E S (OrderComparison.list O) x = 0) :
    CechLowDegrees.d0 E S (OrderComplex.observations O) x = 0 := by
  funext p
  let q : CechLowDegrees.Pair (K := OrderComparison.ListIndex O) :=
    ⟨p.val, lt_of_le_of_ne (toLinearExtension.monotone p.property.le) (fun h => p.property.ne h)⟩
  exact congrFun hx q

include hO in
lemma closed_iff (x : CechLowDegrees.C0 E S (OrderComparison.list O)) :
    CechLowDegrees.d0 E S (OrderComparison.list O) x = 0 ↔
      CechLowDegrees.d0 E S (OrderComplex.observations O) x = 0 :=
  ⟨closed_to_order E S O x, closed_from_order E S O hO x⟩

def cycles : LinearMap.ker (CechLowDegrees.d0 E S (OrderComparison.list O)) ≃ₗ[ℝ]
    LinearMap.ker (CechLowDegrees.d0 E S (OrderComplex.observations O)) where
  toFun c := ⟨c.val, closed_to_order E S O c.val c.property⟩
  invFun c := ⟨c.val, closed_from_order E S O hO c.val c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma boundaries : (LinearMap.range (CechLowDegrees.boundaries0 E S (OrderComparison.list O))).map
    (cycles E S O hO).toLinearMap = LinearMap.range (CechLowDegrees.boundaries0 E S (OrderComplex.observations O)) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨CechLowDegrees.boundaries0 E S (OrderComparison.list O) u, ⟨u, rfl⟩, rfl⟩

def oldCohomologyEquiv : CechLowDegrees.H0 E S (OrderComparison.list O) ≃ₗ[ℝ]
    CechLowDegrees.H0 E S (OrderComplex.observations O) :=
  Submodule.Quotient.equiv _ _ (cycles E S O hO) (boundaries E S O hO)

def cohomologyEquiv : Cohomology E S (OrderComparison.list O) 0 ≃ₗ[ℝ] OrderComplex.Cohomology E O S 0 :=
  (CechLowComparison.cohomologyZero E S (OrderComparison.list O)).trans
    ((oldCohomologyEquiv E S O hO).trans (CechLowComparison.cohomologyZero E S (OrderComplex.observations O)).symm)

lemma restriction_degree_zero (x : Cochain E S (OrderComparison.list O) 1) :
    degreeZero E S (OrderComplex.observations O) (OrderComparison.restriction E S O 1 x) =
      degreeZero E S (OrderComparison.list O) x := by
  funext a
  change coefficientCongr E S _ (OrderComparison.restriction E S O 1 x (oneTuple a)) = _
  rw [OrderComparison.restriction_apply]
  rfl

lemma cohomologyEquiv_eq_comparison (α : Cohomology E S (OrderComparison.list O) 0) :
    cohomologyEquiv E S O hO α = OrderComparison.cohomologyMap E S O 0 α := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply (degreeZero E S (OrderComplex.observations O)).injective
    change degreeZero E S (OrderComplex.observations O)
        ((degreeZero E S (OrderComplex.observations O)).symm (degreeZero E S (OrderComparison.list O) c.val)) =
      degreeZero E S (OrderComplex.observations O) (OrderComparison.restriction E S O 1 c.val)
    rw [LinearEquiv.apply_symm_apply, restriction_degree_zero]

end OrderLowZero
end WeightedObstructionNorms
