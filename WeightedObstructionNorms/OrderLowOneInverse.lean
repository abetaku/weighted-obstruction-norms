import WeightedObstructionNorms.OrderLowOneInjective

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace OrderLowOneInverse
open FiniteObservations CechAllDegrees CechLowComparison OrderLowOneInjective
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I))

/-- Extend an inclusion cochain to equal endpoints by zero. -/
def value (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (A B : OrderComplex.Index O) (h : A ≤ B) : SupportState E S A.val → ℝ :=
  if he : A = B then 0 else coefficientCongr E S (Finset.inter_eq_left.mpr h)
    (u ⟨(A, B), lt_of_le_of_ne h he⟩)

lemma value_self (u : CechLowDegrees.C1 E S (OrderComplex.observations O)) (A : OrderComplex.Index O) :
    value E S O u A A le_rfl = 0 := by simp [value]

lemma value_strict (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (A B : OrderComplex.Index O) (h : A < B) :
    value E S O u A B h.le = coefficientCongr E S (Finset.inter_eq_left.mpr h.le) (u ⟨(A, B), h⟩) := by
  simp only [value, dif_neg h.ne]

lemma value_comp (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (hu : CechLowDegrees.d1 E S (OrderComplex.observations O) u = 0)
    (T A B : OrderComplex.Index O) (hTA : T ≤ A) (hAB : A ≤ B) :
    value E S O u T B (hTA.trans hAB) = value E S O u T A hTA + marginal E S hTA (value E S O u A B hAB) := by
  by_cases heTA : T = A
  · subst A
    rw [value_self, zero_add]
    exact (Marginal.push_id _).symm
  by_cases heAB : A = B
  · subst B
    rw [value_self, map_zero, add_zero]
  have hTA' : T < A := lt_of_le_of_ne hTA heTA
  have hAB' : A < B := lt_of_le_of_ne hAB heAB
  have hTB' := hTA'.trans hAB'
  let w : CechLowDegrees.Triple (K := OrderComplex.Index O) := ⟨(T, A, B), hTA', hAB'⟩
  have ht : CechLowDegrees.tripleObservation (OrderComplex.observations O) w = T.val := by
    change (T.val ∩ A.val) ∩ B.val = T.val
    rw [Finset.inter_eq_left.mpr hTA, Finset.inter_eq_left.mpr (hTA.trans hAB)]
  have hc := congrArg (coefficientCongr E S ht) (congrFun hu w)
  change coefficientCongr E S ht
    (marginal E S (CechLowDegrees.subset12 (OrderComplex.observations O) w) (u ⟨(A, B), hAB'⟩) -
      marginal E S (CechLowDegrees.subset02 (OrderComplex.observations O) w) (u ⟨(T, B), hTB'⟩) +
      marginal E S (CechLowDegrees.subset01 (OrderComplex.observations O) w) (u ⟨(T, A), hTA'⟩)) = _ at hc
  rw [map_add, map_sub, Pi.zero_apply, map_zero] at hc
  have eAB := coefficientCongr_marginal E S ht (Finset.inter_eq_left.mpr hAB)
    (CechLowDegrees.subset12 (OrderComplex.observations O) w) hTA (u ⟨(A, B), hAB'⟩)
  have eTB := coefficientCongr_marginal E S ht (Finset.inter_eq_left.mpr (hTA.trans hAB))
    (CechLowDegrees.subset02 (OrderComplex.observations O) w) (Finset.Subset.refl T.val) (u ⟨(T, B), hTB'⟩)
  have eTA := coefficientCongr_marginal E S ht (Finset.inter_eq_left.mpr hTA)
    (CechLowDegrees.subset01 (OrderComplex.observations O) w) (Finset.Subset.refl T.val) (u ⟨(T, A), hTA'⟩)
  have idTB : marginal E S (Finset.Subset.refl T.val)
      (coefficientCongr E S (Finset.inter_eq_left.mpr (hTA.trans hAB)) (u ⟨(T, B), hTB'⟩)) =
      value E S O u T B (hTA.trans hAB) := by rw [value_strict E S O u T B hTB']; exact Marginal.push_id _
  have idTA : marginal E S (Finset.Subset.refl T.val)
      (coefficientCongr E S (Finset.inter_eq_left.mpr hTA) (u ⟨(T, A), hTA'⟩)) =
      value E S O u T A hTA := by rw [value_strict E S O u T A hTA']; exact Marginal.push_id _
  have eAB' : coefficientCongr E S ht (marginal E S (CechLowDegrees.subset12 (OrderComplex.observations O) w)
      (u ⟨(A, B), hAB'⟩)) = marginal E S hTA (value E S O u A B hAB) := by
    rw [value_strict E S O u A B hAB']
    exact eAB
  have hh := (congrArg₂ (· + ·) (congrArg₂ (· - ·) eAB' (eTB.trans idTB)) (eTA.trans idTA)).symm.trans hc
  apply sub_eq_zero.mp
  calc
    _ = -(marginal E S hTA (value E S O u A B hAB) - value E S O u T B (hTA.trans hAB) + value E S O u T A hTA) := by abel
    _ = 0 := by rw [hh, neg_zero]

lemma value_difference_marginal (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (hu : CechLowDegrees.d1 E S (OrderComplex.observations O) u = 0)
    (T P A B : OrderComplex.Index O) (hTP : T ≤ P) (hPA : P ≤ A) (hPB : P ≤ B) :
    marginal E S hTP (value E S O u P B hPB - value E S O u P A hPA) =
      value E S O u T B (hTP.trans hPB) - value E S O u T A (hTP.trans hPA) := by
  have hb : marginal E S hTP (value E S O u P B hPB) =
      value E S O u T B (hTP.trans hPB) - value E S O u T P hTP := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (value_comp E S O u hu T P B hTP hPB).symm
  have ha : marginal E S hTP (value E S O u P A hPA) =
      value E S O u T A (hTP.trans hPA) - value E S O u T P hTP := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (value_comp E S O u hu T P A hTP hPA).symm
  rw [map_sub, hb, ha]
  abel

lemma value_congr_left (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    {T T' : OrderComplex.Index O} (he : T = T') (B : OrderComplex.Index O)
    (h : T ≤ B) (h' : T' ≤ B) :
    coefficientCongr E S (congrArg Subtype.val he) (value E S O u T B h) = value E S O u T' B h' := by
  subst T'
  rfl

variable (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

def meetIndex (A B : OrderComplex.Index O) : OrderComplex.Index O :=
  ⟨A.val ∩ B.val, hO A.val A.property _ Finset.inter_subset_left⟩

/-- The inverse formula from the manuscript: u_(A∩B,B) - u_(A∩B,A). -/
def inverse (u : CechLowDegrees.C1 E S (OrderComplex.observations O)) :
    CechLowDegrees.C1 E S (OrderComparison.list O) := fun p =>
  value E S O u (meetIndex O hO p.val.1 p.val.2) p.val.2 Finset.inter_subset_right -
    value E S O u (meetIndex O hO p.val.1 p.val.2) p.val.1 Finset.inter_subset_left

lemma inverse_liftPair (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (p : CechLowDegrees.Pair (K := OrderComplex.Index O)) : inverse E S O hO u (liftPair O p) = u p := by
  have hT : meetIndex O hO p.val.1 p.val.2 = p.val.1 :=
    Subtype.ext (Finset.inter_eq_left.mpr p.property.le)
  apply (coefficientCongr E S (Finset.inter_eq_left.mpr p.property.le)).injective
  change coefficientCongr E S (Finset.inter_eq_left.mpr p.property.le)
    (value E S O u (meetIndex O hO p.val.1 p.val.2) p.val.2 Finset.inter_subset_right -
      value E S O u (meetIndex O hO p.val.1 p.val.2) p.val.1 Finset.inter_subset_left) = _
  rw [map_sub]
  have hb := value_congr_left E S O u hT p.val.2 Finset.inter_subset_right p.property.le
  have ha := value_congr_left E S O u hT p.val.1 Finset.inter_subset_left le_rfl
  calc
    _ = value E S O u p.val.1 p.val.2 p.property.le - value E S O u p.val.1 p.val.1 le_rfl := congrArg₂ (· - ·) hb ha
    _ = _ := by rw [value_self, sub_zero, value_strict E S O u p.val.1 p.val.2 p.property]

lemma inverse_closed (u : CechLowDegrees.C1 E S (OrderComplex.observations O))
    (hu : CechLowDegrees.d1 E S (OrderComplex.observations O) u = 0) :
    CechLowDegrees.d1 E S (OrderComparison.list O) (inverse E S O hO u) = 0 := by
  funext w
  let A : OrderComplex.Index O := w.val.1
  let B : OrderComplex.Index O := w.val.2.1
  let C : OrderComplex.Index O := w.val.2.2
  let PAB := meetIndex O hO A B
  let PAC := meetIndex O hO A C
  let PBC := meetIndex O hO B C
  let T := meetIndex O hO PAB C
  have hBC : T ≤ PBC := CechLowDegrees.subset12 (OrderComparison.list O) w
  have hAC : T ≤ PAC := CechLowDegrees.subset02 (OrderComparison.list O) w
  have hAB : T ≤ PAB := CechLowDegrees.subset01 (OrderComparison.list O) w
  change marginal E S hBC (value E S O u PBC C Finset.inter_subset_right - value E S O u PBC B Finset.inter_subset_left) -
    marginal E S hAC (value E S O u PAC C Finset.inter_subset_right - value E S O u PAC A Finset.inter_subset_left) +
    marginal E S hAB (value E S O u PAB B Finset.inter_subset_right - value E S O u PAB A Finset.inter_subset_left) = 0
  rw [value_difference_marginal E S O u hu T PBC B C hBC Finset.inter_subset_left Finset.inter_subset_right,
    value_difference_marginal E S O u hu T PAC A C hAC Finset.inter_subset_left Finset.inter_subset_right,
    value_difference_marginal E S O u hu T PAB A B hAB Finset.inter_subset_left Finset.inter_subset_right]
  abel

def oldRestriction : CechLowDegrees.C1 E S (OrderComparison.list O) →ₗ[ℝ]
    CechLowDegrees.C1 E S (OrderComplex.observations O) where
  toFun x p := x (liftPair O p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma oldRestriction_closed (x : CechLowDegrees.C1 E S (OrderComparison.list O))
    (hx : CechLowDegrees.d1 E S (OrderComparison.list O) x = 0) :
    CechLowDegrees.d1 E S (OrderComplex.observations O) (oldRestriction E S O x) = 0 := by
  funext t
  let w : CechLowDegrees.Triple (K := OrderComparison.ListIndex O) :=
    ⟨t.val, (liftPair O (CechLowDegrees.face01 t)).property, (liftPair O (CechLowDegrees.face12 t)).property⟩
  exact congrFun hx w

lemma inverse_oldRestriction (x : CechLowDegrees.C1 E S (OrderComparison.list O))
    (hx : CechLowDegrees.d1 E S (OrderComparison.list O) x = 0) :
    inverse E S O hO (oldRestriction E S O x) = x := by
  apply sub_eq_zero.mp
  apply old_cycle_zero E S O hO
  · rw [map_sub, inverse_closed E S O hO _ (oldRestriction_closed E S O x hx), hx, sub_self]
  · intro p
    change inverse E S O hO (oldRestriction E S O x) (liftPair O p) - x (liftPair O p) = 0
    rw [inverse_liftPair]
    exact sub_self _

def cyclesEquiv : LinearMap.ker (CechLowDegrees.d1 E S (OrderComparison.list O)) ≃ₗ[ℝ]
    LinearMap.ker (CechLowDegrees.d1 E S (OrderComplex.observations O)) where
  toFun c := ⟨oldRestriction E S O c.val, oldRestriction_closed E S O c.val c.property⟩
  invFun c := ⟨inverse E S O hO c.val, inverse_closed E S O hO c.val c.property⟩
  left_inv c := Subtype.ext (inverse_oldRestriction E S O hO c.val c.property)
  right_inv c := by apply Subtype.ext; funext p; exact inverse_liftPair E S O hO c.val p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma boundaries : (LinearMap.range (CechLowDegrees.boundaries1 E S (OrderComparison.list O))).map
    (cyclesEquiv E S O hO).toLinearMap = LinearMap.range (CechLowDegrees.boundaries1 E S (OrderComplex.observations O)) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨CechLowDegrees.boundaries1 E S (OrderComparison.list O) u, ⟨u, rfl⟩, rfl⟩

def oldCohomologyEquiv : CechLowDegrees.H1 E S (OrderComparison.list O) ≃ₗ[ℝ]
    CechLowDegrees.H1 E S (OrderComplex.observations O) :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv E S O hO) (boundaries E S O hO)

def cohomologyEquiv : Cohomology E S (OrderComparison.list O) 1 ≃ₗ[ℝ] OrderComplex.Cohomology E O S 1 :=
  (CechLowComparison.cohomologyOne E S (OrderComparison.list O)).trans
    ((oldCohomologyEquiv E S O hO).trans (CechLowComparison.cohomologyOne E S (OrderComplex.observations O)).symm)

lemma cohomologyEquiv_eq_comparison (α : Cohomology E S (OrderComparison.list O) 1) :
    cohomologyEquiv E S O hO α = OrderComparison.cohomologyMap E S O 1 α := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply (degreeOne E S (OrderComplex.observations O)).injective
    change degreeOne E S (OrderComplex.observations O)
        ((degreeOne E S (OrderComplex.observations O)).symm (oldRestriction E S O (degreeOne E S (OrderComparison.list O) c.val))) =
      degreeOne E S (OrderComplex.observations O) (OrderComparison.restriction E S O 2 c.val)
    rw [LinearEquiv.apply_symm_apply]
    funext p
    exact (restriction_degree_one E S O c.val p).symm

end OrderLowOneInverse
end WeightedObstructionNorms
