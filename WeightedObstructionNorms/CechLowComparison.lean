import WeightedObstructionNorms.CechWeights
import WeightedObstructionNorms.CechLowDegrees
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
namespace WeightedObstructionNorms
namespace CechLowComparison
open FiniteObservations CechAllDegrees
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

def oneTuple (i : K) : Tuple (K := K) 1 :=
  OrderEmbedding.ofStrictMono (fun _ => i) (by intro a b h; exact False.elim (by omega))

def twoTuple (p : CechLowDegrees.Pair (K := K)) : Tuple (K := K) 2 :=
  OrderEmbedding.ofStrictMono ![p.val.1, p.val.2] (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [p.property])

def threeTuple (t : CechLowDegrees.Triple (K := K)) : Tuple (K := K) 3 :=
  OrderEmbedding.ofStrictMono ![t.val.1, t.val.2.1, t.val.2.2] (by
    intro a b h
    have h01 := t.property.1
    have h12 := t.property.2
    have h02 := h01.trans h12
    fin_cases a <;> fin_cases b <;> simp_all)

def oneEquiv : K ≃ Tuple (K := K) 1 where
  toFun := oneTuple
  invFun t := t 0
  left_inv _ := rfl
  right_inv t := by ext i; fin_cases i; rfl

def twoEquiv : CechLowDegrees.Pair (K := K) ≃ Tuple (K := K) 2 where
  toFun := twoTuple
  invFun t := ⟨(t 0, t 1), t.strictMono (by decide)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv t := by ext i; fin_cases i <;> rfl

def threeEquiv : CechLowDegrees.Triple (K := K) ≃ Tuple (K := K) 3 where
  toFun := threeTuple
  invFun t := ⟨(t 0, t 1, t 2), t.strictMono (by decide), t.strictMono (by decide)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv t := by ext i; fin_cases i <;> rfl

lemma one_observation (i : K) : observation M (oneTuple i) = M i := by
  ext a
  simp [mem_observation, oneTuple]
lemma two_observation (p : CechLowDegrees.Pair (K := K)) :
    observation M (twoTuple p) = CechLowDegrees.pairObservation M p := by
  ext a
  simp [mem_observation, twoTuple, CechLowDegrees.pairObservation, Fin.forall_fin_two]
lemma three_observation (t : CechLowDegrees.Triple (K := K)) :
    observation M (threeTuple t) = CechLowDegrees.tripleObservation M t := by
  ext a
  simp [mem_observation, threeTuple, CechLowDegrees.tripleObservation, Fin.forall_fin_succ, and_assoc]

def coefficientCongr {A B : Finset I} (h : A = B) :
    (SupportState E S A → ℝ) ≃ₗ[ℝ] (SupportState E S B → ℝ) := by
  subst B
  exact LinearEquiv.refl ℝ _

lemma coefficientCongr_marginal {A B A' B' : Finset I} (hA : A = A') (hB : B = B')
    (h : A ⊆ B) (h' : A' ⊆ B') (x : SupportState E S B → ℝ) :
    coefficientCongr E S hA (marginal E S h x) = marginal E S h' (coefficientCongr E S hB x) := by
  subst A'; subst B'; rfl

def cochainEquiv {n : ℕ} {J : Type*} (e : J ≃ Tuple (K := K) n) (A : J → Finset I)
    (h : ∀ j, observation M (e j) = A j) :
    Cochain E S M n ≃ₗ[ℝ] (∀ j, SupportState E S (A j) → ℝ) :=
  (LinearEquiv.piCongrLeft ℝ (fun t => SupportState E S (observation M t) → ℝ) e).symm.trans
    (LinearEquiv.piCongrRight (fun j => coefficientCongr E S (h j)))

lemma cochainEquiv_apply {n : ℕ} {J : Type*} (e : J ≃ Tuple (K := K) n) (A : J → Finset I)
    (h : ∀ j, observation M (e j) = A j) (x : Cochain E S M n) (j : J) :
    cochainEquiv E S M e A h x j = coefficientCongr E S (h j) (x (e j)) := rfl

def degreeZero : Cochain E S M 1 ≃ₗ[ℝ] CechLowDegrees.C0 E S M :=
  cochainEquiv E S M oneEquiv M (one_observation M)
def degreeOne : Cochain E S M 2 ≃ₗ[ℝ] CechLowDegrees.C1 E S M :=
  cochainEquiv E S M twoEquiv (CechLowDegrees.pairObservation M) (two_observation M)
def degreeTwo : Cochain E S M 3 ≃ₗ[ℝ] CechLowDegrees.C2 E S M :=
  cochainEquiv E S M threeEquiv (CechLowDegrees.tripleObservation M) (three_observation M)

lemma component_marginal {n : ℕ} (x : Cochain E S M n)
    {A A' B : Finset I} (hA : A = A') {t t' : Tuple (K := K) n} (ht : t = t')
    (hB : observation M t' = B) (h : A ⊆ observation M t) (h' : A' ⊆ B) :
    coefficientCongr E S hA (marginal E S h (x t)) =
      marginal E S h' (coefficientCongr E S hB (x t')) := by
  subst t'
  exact coefficientCongr_marginal E S hA hB h h' (x t)

lemma face_zero_two (p : CechLowDegrees.Pair (K := K)) : face 0 (twoTuple p) = oneTuple p.val.2 := by
  ext i; fin_cases i; rfl
lemma face_one_two (p : CechLowDegrees.Pair (K := K)) : face 1 (twoTuple p) = oneTuple p.val.1 := by
  ext i; fin_cases i; rfl
lemma face_zero_three (t : CechLowDegrees.Triple (K := K)) :
    face 0 (threeTuple t) = twoTuple (CechLowDegrees.face12 t) := by
  ext i; fin_cases i <;> rfl
lemma face_one_three (t : CechLowDegrees.Triple (K := K)) :
    face 1 (threeTuple t) = twoTuple (CechLowDegrees.face02 t) := by
  ext i; fin_cases i <;> rfl
lemma face_two_three (t : CechLowDegrees.Triple (K := K)) :
    face 2 (threeTuple t) = twoTuple (CechLowDegrees.face01 t) := by
  ext i; fin_cases i <;> rfl

/-- Identification of the first nonaugmented differential in the two concrete implementations. -/
theorem differential_zero (x : Cochain E S M 1) :
    degreeOne E S M (differential E S M 1 x) = CechLowDegrees.d0 E S M (degreeZero E S M x) := by
  funext p
  change coefficientCongr E S (two_observation M p) (differential E S M 1 x (twoTuple p)) = _
  have hd : differential E S M 1 x (twoTuple p) =
      marginal E S (observation_face M 0 (twoTuple p)) (x (face 0 (twoTuple p))) -
      marginal E S (observation_face M 1 (twoTuple p)) (x (face 1 (twoTuple p))) := by
    simp [differential, coface, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hd, map_sub]
  change _ = marginal E S Finset.inter_subset_right (degreeZero E S M x p.val.2) -
    marginal E S Finset.inter_subset_left (degreeZero E S M x p.val.1)
  congr 1
  · exact component_marginal E S M x (two_observation M p) (face_zero_two p) (one_observation M p.val.2) _ _
  · exact component_marginal E S M x (two_observation M p) (face_one_two p) (one_observation M p.val.1) _ _

/-- Identification of the next differential, including all three alternating faces. -/
theorem differential_one (x : Cochain E S M 2) :
    degreeTwo E S M (differential E S M 2 x) = CechLowDegrees.d1 E S M (degreeOne E S M x) := by
  funext t
  change coefficientCongr E S (three_observation M t) (differential E S M 2 x (threeTuple t)) = _
  have hd : differential E S M 2 x (threeTuple t) =
      marginal E S (observation_face M 0 (threeTuple t)) (x (face 0 (threeTuple t))) -
      marginal E S (observation_face M 1 (threeTuple t)) (x (face 1 (threeTuple t))) +
      marginal E S (observation_face M 2 (threeTuple t)) (x (face 2 (threeTuple t))) := by
    simp [differential, coface, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]
  rw [hd, map_add, map_sub]
  change _ = marginal E S (CechLowDegrees.subset12 M t) (degreeOne E S M x (CechLowDegrees.face12 t)) -
      marginal E S (CechLowDegrees.subset02 M t) (degreeOne E S M x (CechLowDegrees.face02 t)) +
      marginal E S (CechLowDegrees.subset01 M t) (degreeOne E S M x (CechLowDegrees.face01 t))
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· - ·)
    · exact component_marginal E S M x (three_observation M t) (face_zero_three t) (two_observation M _) _ _
    · exact component_marginal E S M x (three_observation M t) (face_one_three t) (two_observation M _) _ _
  · exact component_marginal E S M x (three_observation M t) (face_two_three t) (two_observation M _) _ _

lemma coefficientCongr_global {n : ℕ} (t : Tuple (K := K) n) {A : Finset I}
    (h : observation M t = A) (x : {z // z ∈ S} → ℝ) :
    coefficientCongr E S h (Marginal.push (CechAllDegrees.globalProject E S M t) x) =
      Marginal.push (CechLowDegrees.globalProject E S A) x := by
  subst A
  rfl

lemma augmentation (x : {z // z ∈ S} → ℝ) :
    degreeZero E S M (differential E S M 0 (augmentationEquiv E S M x)) =
      CechLowDegrees.augmentation E S M x := by
  funext i
  change coefficientCongr E S (one_observation M i)
    (differential E S M 0 (augmentationEquiv E S M x) (oneTuple i)) = _
  rw [differential_augmentation]
  exact coefficientCongr_global E S M (oneTuple i) (one_observation M i) x

def kernelEquiv {X Y Z W : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    [Module ℝ X] [Module ℝ Y] [Module ℝ Z] [Module ℝ W]
    (e : X ≃ₗ[ℝ] Y) (f : Z ≃ₗ[ℝ] W) (d : X →ₗ[ℝ] Z) (d' : Y →ₗ[ℝ] W)
    (h : ∀ x, f (d x) = d' (e x)) : LinearMap.ker d ≃ₗ[ℝ] LinearMap.ker d' where
  toFun x := ⟨e x.val, by rw [LinearMap.mem_ker, ← h, x.property, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    apply f.injective
    rw [h, LinearEquiv.apply_symm_apply, y.property, map_zero]⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact map_add e x.val y.val
  map_smul' a x := by apply Subtype.ext; exact map_smul e a x.val

def cyclesZero : LinearMap.ker (differential E S M 1) ≃ₗ[ℝ] LinearMap.ker (CechLowDegrees.d0 E S M) :=
  kernelEquiv (degreeZero E S M) (degreeOne E S M) _ _ (differential_zero E S M)
def cyclesOne : LinearMap.ker (differential E S M 2) ≃ₗ[ℝ] LinearMap.ker (CechLowDegrees.d1 E S M) :=
  kernelEquiv (degreeOne E S M) (degreeTwo E S M) _ _ (differential_one E S M)

lemma boundariesZero : (LinearMap.range (boundaries E S M 0)).map (cyclesZero E S M).toLinearMap =
    LinearMap.range (CechLowDegrees.boundaries0 E S M) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    refine ⟨(augmentationEquiv E S M).symm u, ?_⟩
    apply Subtype.ext
    have h := augmentation E S M ((augmentationEquiv E S M).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · rintro ⟨u, rfl⟩
    refine ⟨boundaries E S M 0 (augmentationEquiv E S M u), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    exact augmentation E S M u

lemma boundariesOne : (LinearMap.range (boundaries E S M 1)).map (cyclesOne E S M).toLinearMap =
    LinearMap.range (CechLowDegrees.boundaries1 E S M) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨degreeZero E S M u, Subtype.ext (differential_zero E S M u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨boundaries E S M 1 ((degreeZero E S M).symm u), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    have h := differential_zero E S M ((degreeZero E S M).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

/-- The old degree-zero presentation is identified with the all-degree cohomology. -/
def cohomologyZero : Cohomology E S M 0 ≃ₗ[ℝ] CechLowDegrees.H0 E S M :=
  Submodule.Quotient.equiv _ _ (cyclesZero E S M) (boundariesZero E S M)

/-- The old degree-one presentation is identified with the all-degree cohomology. -/
def cohomologyOne : Cohomology E S M 1 ≃ₗ[ℝ] CechLowDegrees.H1 E S M :=
  Submodule.Quotient.equiv _ _ (cyclesOne E S M) (boundariesOne E S M)

lemma coefficientCongr_box_iff {A B : Finset I} (h : A = B) (q : State E → ℝ) (C : ℝ)
    (x : SupportState E S A → ℝ) :
    (∀ b, |coefficientCongr E S h x b| ≤ C * weight E q B b.val) ↔
      (∀ a, |x a| ≤ C * weight E q A a.val) := by
  subst B
  rfl

lemma cochain_box_iff (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    {n : ℕ} {J : Type*} (e : J ≃ Tuple (K := K) n) (A : J → Finset I)
    (h : ∀ j, observation M (e j) = A j) (x : Cochain E S M n) {C : ℝ} (hC : 0 ≤ C) :
    cochainNorm E S M q n x ≤ C ↔
      ∀ j b, |cochainEquiv E S M e A h x j b| ≤ C * weight E q (A j) b.val := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  rw [cochainNorm, weightedNorm_le_iff (coordinateWeight_positive E S M hq n) hC]
  constructor
  · intro hx j
    rw [cochainEquiv_apply]
    apply (coefficientCongr_box_iff E S (h j) q C (x (e j))).2
    intro a
    exact hx ⟨e j, a⟩
  · intro hx j
    obtain ⟨k, hk⟩ := e.surjective j.1
    rcases j with ⟨t, a⟩
    dsimp only at hk
    subst t
    exact (coefficientCongr_box_iff E S (h k) q C (x (e k))).1 (hx k) a

end CechLowComparison
end WeightedObstructionNorms
