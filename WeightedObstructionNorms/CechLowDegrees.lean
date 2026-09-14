import WeightedObstructionNorms.FiniteObservations
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The concrete augmented marginal Cech complex through degree two.
Pairs and triples are strictly increasing: no unordered or nonalternating
replacement complex is used here. Higher degrees are not claimed. -/
noncomputable section
namespace WeightedObstructionNorms
namespace CechLowDegrees
open FiniteObservations
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

abbrev Pair := {p : K × K // p.1 < p.2}
abbrev Triple := {t : K × K × K // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
def pairObservation (p : Pair (K := K)) : Finset I := M p.val.1 ∩ M p.val.2
def tripleObservation (t : Triple (K := K)) : Finset I := (M t.val.1 ∩ M t.val.2.1) ∩ M t.val.2.2

def face01 (t : Triple (K := K)) : Pair (K := K) := ⟨(t.val.1, t.val.2.1), t.property.1⟩
def face02 (t : Triple (K := K)) : Pair (K := K) := ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩
def face12 (t : Triple (K := K)) : Pair (K := K) := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩

lemma subset01 (t : Triple (K := K)) : tripleObservation M t ⊆ pairObservation M (face01 t) :=
  Finset.inter_subset_left
lemma subset02 (t : Triple (K := K)) : tripleObservation M t ⊆ pairObservation M (face02 t) := by
  intro i hi
  simp only [tripleObservation, pairObservation, face02, Finset.mem_inter] at hi ⊢
  exact ⟨hi.1.1, hi.2⟩
lemma subset12 (t : Triple (K := K)) : tripleObservation M t ⊆ pairObservation M (face12 t) := by
  intro i hi
  simp only [tripleObservation, pairObservation, face12, Finset.mem_inter] at hi ⊢
  exact ⟨hi.1.2, hi.2⟩

abbrev C0 := ∀ i, SupportState E S (M i) → ℝ
abbrev C1 := ∀ p : Pair (K := K), SupportState E S (pairObservation M p) → ℝ
abbrev C2 := ∀ t : Triple (K := K), SupportState E S (tripleObservation M t) → ℝ

def d0 : C0 E S M →ₗ[ℝ] C1 E S M where
  toFun x p := marginal E S (Finset.inter_subset_right (s₁ := M p.val.1)) (x p.val.2) -
    marginal E S (Finset.inter_subset_left (s₂ := M p.val.2)) (x p.val.1)
  map_add' x y := by funext p; simp only [Pi.add_apply, map_add]; abel
  map_smul' a x := by funext p; simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_sub]

def d1 : C1 E S M →ₗ[ℝ] C2 E S M where
  toFun y t := marginal E S (subset12 M t) (y (face12 t)) -
    marginal E S (subset02 M t) (y (face02 t)) + marginal E S (subset01 M t) (y (face01 t))
  map_add' x y := by funext t; simp only [Pi.add_apply, map_add]; abel
  map_smul' a x := by funext t; simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_sub, smul_add]

/-- Paired-face cancellation for the concrete degree-zero differential. -/
theorem d1_d0 (x : C0 E S M) : d1 E S M (d0 E S M x) = 0 := by
  funext t
  simp only [d1, d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub, face12, face02, face01, Pi.zero_apply]
  simp only [marginal, Marginal.linear, LinearMap.coe_mk, AddHom.coe_mk, Marginal.push_comp, supportRestrict_comp]
  abel

/-- Global support states project to each local support. -/
def globalProject (A : Finset I) (z : {z // z ∈ S}) : SupportState E S A :=
  ⟨project E A z.val, (projected_mem E S A _).2 ⟨z.val, z.property, rfl⟩⟩

def augmentation : ({z // z ∈ S} → ℝ) →ₗ[ℝ] C0 E S M where
  toFun x i := Marginal.push (globalProject E S (M i)) x
  map_add' x y := by funext i; exact Marginal.push_add _ x y
  map_smul' a x := by funext i; exact Marginal.push_smul _ a x

/-- Compatibility of marginals is proved from composition of actual projections. -/
theorem d0_augmentation (x : {z // z ∈ S} → ℝ) : d0 E S M (augmentation E S M x) = 0 := by
  funext p
  change Marginal.push _ (Marginal.push _ x) - Marginal.push _ (Marginal.push _ x) = 0
  rw [Marginal.push_comp, Marginal.push_comp]
  have heq : supportRestrict E S (Finset.inter_subset_right (s₁ := M p.val.1)) ∘
      globalProject E S (M p.val.2) =
      supportRestrict E S (Finset.inter_subset_left (s₂ := M p.val.2)) ∘
      globalProject E S (M p.val.1) := rfl
  rw [heq, sub_self]

/-- Extension by zero in each concrete degree. -/
def extend0 {T : Finset (State E)} (h : S ⊆ T) : C0 E S M →ₗ[ℝ] C0 E T M where
  toFun x i := extend E h (M i) (x i)
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' a x := by funext i; exact map_smul (extend E h (M i)) a (x i)
def extend1 {T : Finset (State E)} (h : S ⊆ T) : C1 E S M →ₗ[ℝ] C1 E T M where
  toFun x p := extend E h (pairObservation M p) (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' a x := by funext p; exact map_smul (extend E h (pairObservation M p)) a (x p)
def extend2 {T : Finset (State E)} (h : S ⊆ T) : C2 E S M →ₗ[ℝ] C2 E T M where
  toFun x t := extend E h (tripleObservation M t) (x t)
  map_add' x y := by funext t; exact map_add _ _ _
  map_smul' a x := by funext t; exact map_smul (extend E h (tripleObservation M t)) a (x t)

lemma extend_d0 {T : Finset (State E)} (h : S ⊆ T) (x : C0 E S M) :
    d0 E T M (extend0 E S M h x) = extend1 E S M h (d0 E S M x) := by
  funext p
  simp only [d0, extend0, extend1, LinearMap.coe_mk, AddHom.coe_mk, map_sub,
    extension_commutes]
  rfl

lemma extend_d1 {T : Finset (State E)} (h : S ⊆ T) (x : C1 E S M) :
    d1 E T M (extend1 E S M h x) = extend2 E S M h (d1 E S M x) := by
  funext t
  simp only [d1, extend1, extend2, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add,
    extension_commutes]

lemma extend0_injective {T : Finset (State E)} (h : S ⊆ T) : Function.Injective (extend0 E S M h) := by
  intro x y hxy
  funext i
  exact extension_injective E h (M i) (congrFun hxy i)
lemma extend1_injective {T : Finset (State E)} (h : S ⊆ T) : Function.Injective (extend1 E S M h) := by
  intro x y hxy
  funext p
  exact extension_injective E h (pairObservation M p) (congrFun hxy p)

/-- Boundaries inside the concrete cocycle spaces. -/
def boundaries0 : ({z // z ∈ S} → ℝ) →ₗ[ℝ] LinearMap.ker (d0 E S M) :=
  (augmentation E S M).codRestrict _ (d0_augmentation E S M)
def boundaries1 : C0 E S M →ₗ[ℝ] LinearMap.ker (d1 E S M) :=
  (d0 E S M).codRestrict _ (d1_d0 E S M)

abbrev H0 := (LinearMap.ker (d0 E S M)) ⧸ LinearMap.range (boundaries0 E S M)
abbrev H1 := (LinearMap.ker (d1 E S M)) ⧸ LinearMap.range (boundaries1 E S M)

def globalInclude {T : Finset (State E)} (h : S ⊆ T) (z : {z // z ∈ S}) : {z // z ∈ T} :=
  ⟨z.val, h z.property⟩
def extendGlobal {T : Finset (State E)} (h : S ⊆ T) :
    ({z // z ∈ S} → ℝ) →ₗ[ℝ] ({z // z ∈ T} → ℝ) := Marginal.linear (globalInclude E S h)

lemma extend_augmentation {T : Finset (State E)} (h : S ⊆ T) (x : {z // z ∈ S} → ℝ) :
    augmentation E T M (extendGlobal E S h x) = extend0 E S M h (augmentation E S M x) := by
  funext i
  change Marginal.push _ (Marginal.push _ x) = Marginal.push _ (Marginal.push _ x)
  rw [Marginal.push_comp, Marginal.push_comp]
  rfl

def cycleExtend0 {T : Finset (State E)} (h : S ⊆ T) :
    LinearMap.ker (d0 E S M) →ₗ[ℝ] LinearMap.ker (d0 E T M) :=
  ((extend0 E S M h).domRestrict _).codRestrict _ (by
    intro c
    change d0 E T M (extend0 E S M h c.val) = 0
    rw [extend_d0, c.property, map_zero])
def cycleExtend1 {T : Finset (State E)} (h : S ⊆ T) :
    LinearMap.ker (d1 E S M) →ₗ[ℝ] LinearMap.ker (d1 E T M) :=
  ((extend1 E S M h).domRestrict _).codRestrict _ (by
    intro c
    change d1 E T M (extend1 E S M h c.val) = 0
    rw [extend_d1, c.property, map_zero])

lemma extend_boundaries0 {T : Finset (State E)} (h : S ⊆ T) :
    LinearMap.range (boundaries0 E S M) ≤ LinearMap.ker
      ((LinearMap.range (boundaries0 E T M)).mkQ.comp (cycleExtend0 E S M h)) := by
  rintro c ⟨x, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨extendGlobal E S h x, Subtype.ext (extend_augmentation E S M h x)⟩
lemma extend_boundaries1 {T : Finset (State E)} (h : S ⊆ T) :
    LinearMap.range (boundaries1 E S M) ≤ LinearMap.ker
      ((LinearMap.range (boundaries1 E T M)).mkQ.comp (cycleExtend1 E S M h)) := by
  rintro c ⟨x, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨extend0 E S M h x, Subtype.ext (extend_d0 E S M h x)⟩

/-- Actual support-enlargement maps on the concrete H^0 and H^1 quotients. -/
def cohomologyExtend0 {T : Finset (State E)} (h : S ⊆ T) : H0 E S M →ₗ[ℝ] H0 E T M :=
  (LinearMap.range (boundaries0 E S M)).liftQ
    ((LinearMap.range (boundaries0 E T M)).mkQ.comp (cycleExtend0 E S M h)) (extend_boundaries0 E S M h)
def cohomologyExtend1 {T : Finset (State E)} (h : S ⊆ T) : H1 E S M →ₗ[ℝ] H1 E T M :=
  (LinearMap.range (boundaries1 E S M)).liftQ
    ((LinearMap.range (boundaries1 E T M)).mkQ.comp (cycleExtend1 E S M h)) (extend_boundaries1 E S M h)

lemma cohomologyExtend0_class {T : Finset (State E)} (h : S ⊆ T) (c : LinearMap.ker (d0 E S M)) :
    cohomologyExtend0 E S M h ((LinearMap.range (boundaries0 E S M)).mkQ c) =
      (LinearMap.range (boundaries0 E T M)).mkQ (cycleExtend0 E S M h c) := rfl
lemma cohomologyExtend1_class {T : Finset (State E)} (h : S ⊆ T) (c : LinearMap.ker (d1 E S M)) :
    cohomologyExtend1 E S M h ((LinearMap.range (boundaries1 E S M)).mkQ c) =
      (LinearMap.range (boundaries1 E T M)).mkQ (cycleExtend1 E S M h c) := rfl

end CechLowDegrees
end WeightedObstructionNorms
