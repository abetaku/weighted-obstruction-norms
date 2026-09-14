import WeightedObstructionNorms.CechWeights
import WeightedObstructionNorms.FullSupportAcyclicity
import WeightedObstructionNorms.RelativeWindow

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace WeightedObstructionNorms
namespace CechSplitting
open FiniteObservations CechAllDegrees
section General
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

abbrev NewCoordinate (n : ℕ) := Σ t : Tuple (K := K) n,
  {z : SupportState E Finset.univ (observation M t) // z.val ∉ projected E S (observation M t)}

instance newCoordinateFintype (n : ℕ) : Fintype (NewCoordinate E S M n) := Fintype.ofFinite _

def pack (n : ℕ) : (Coordinate E S M n → ℝ) ≃ₗ[ℝ] Cochain E S M n where
  toFun x t z := x ⟨t, z⟩
  invFun x j := x j.1 j.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def takeOld (n : ℕ) : Cochain E Finset.univ M n →ₗ[ℝ] Cochain E S M n where
  toFun x t z := x t (supportInclude E (Finset.subset_univ S) _ z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def takeNew (n : ℕ) : Cochain E Finset.univ M n →ₗ[ℝ] (NewCoordinate E S M n → ℝ) where
  toFun x j := x j.1 j.2.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def putNew (n : ℕ) : (NewCoordinate E S M n → ℝ) →ₗ[ℝ] Cochain E Finset.univ M n := by
  classical
  exact {
    toFun := fun x t z => if hz : z.val ∈ projected E S (observation M t) then 0 else x ⟨t, ⟨z, hz⟩⟩
    map_add' := by intro x y; funext t z; split_ifs <;> simp_all
    map_smul' := by intro a x; funext t z; split_ifs <;> simp_all }

lemma takeOld_extension (n : ℕ) (x : Cochain E S M n) :
    takeOld E S M n (extension E S M (Finset.subset_univ S) n x) = x := by
  funext t z
  exact Marginal.push_injective_apply _ (supportInclude_injective E _ _) (x t) z

lemma extension_zero (n : ℕ) (x : Cochain E S M n) (t : Tuple (K := K) n)
    (z : SupportState E Finset.univ (observation M t))
    (hz : z.val ∉ projected E S (observation M t)) :
    extension E S M (Finset.subset_univ S) n x t z = 0 := by
  classical
  simp only [extension, extend, Marginal.linear, LinearMap.coe_mk, AddHom.coe_mk, Marginal.push]
  apply Finset.sum_eq_zero
  intro a _
  rw [if_neg]
  intro h
  apply hz
  have he : a.val = z.val := congrArg Subtype.val h
  exact he ▸ a.property

lemma takeNew_extension (n : ℕ) (x : Cochain E S M n) :
    takeNew E S M n (extension E S M (Finset.subset_univ S) n x) = 0 := by
  funext j
  exact extension_zero E S M n x j.1 j.2.val j.2.property

lemma takeOld_putNew (n : ℕ) (x : NewCoordinate E S M n → ℝ) :
    takeOld E S M n (putNew E S M n x) = 0 := by
  funext t z
  simp [takeOld, putNew, supportInclude, z.property]

lemma takeNew_putNew (n : ℕ) (x : NewCoordinate E S M n → ℝ) :
    takeNew E S M n (putNew E S M n x) = x := by
  funext j
  simp [takeNew, putNew, j.2.property]

lemma split_identity (n : ℕ) (x : Cochain E Finset.univ M n) :
    extension E S M (Finset.subset_univ S) n (takeOld E S M n x) +
      putNew E S M n (takeNew E S M n x) = x := by
  classical
  funext t z
  by_cases hz : z.val ∈ projected E S (observation M t)
  · have he : supportInclude E (Finset.subset_univ S) _ ⟨z.val, hz⟩ = z := Subtype.ext rfl
    have hh := Marginal.push_injective_apply _ (supportInclude_injective E (Finset.subset_univ S) _)
      (takeOld E S M n x t) ⟨z.val, hz⟩
    change extension E S M (Finset.subset_univ S) n (takeOld E S M n x) t
      (supportInclude E (Finset.subset_univ S) _ ⟨z.val, hz⟩) = _ at hh
    rw [he] at hh
    simp only [Pi.add_apply, hh, putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hz, add_zero]
    change x t (supportInclude E (Finset.subset_univ S) _ ⟨z.val, hz⟩) = x t z
    rw [he]
  · simp only [Pi.add_apply, extension_zero E S M n _ t z hz,
      putNew, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hz, zero_add]
    rfl

lemma differential_split (n : ℕ) (x : Cochain E Finset.univ M n) :
    differential E Finset.univ M n x =
      extension E S M (Finset.subset_univ S) (n + 1)
        (differential E S M n (takeOld E S M n x)) +
      differential E Finset.univ M n (putNew E S M n (takeNew E S M n x)) := by
  calc
    _ = differential E Finset.univ M n
        (extension E S M (Finset.subset_univ S) n (takeOld E S M n x) +
        putNew E S M n (takeNew E S M n x)) := congrArg _ (split_identity E S M n x).symm
    _ = _ := by rw [map_add, extension_differential]

lemma differential_takeOld (n : ℕ) (x : Cochain E Finset.univ M n) :
    takeOld E S M (n + 1) (differential E Finset.univ M n x) =
      differential E S M n (takeOld E S M n x) +
      takeOld E S M (n + 1) (differential E Finset.univ M n (putNew E S M n (takeNew E S M n x))) := by
  rw [differential_split, map_add, takeOld_extension]

lemma differential_takeNew (n : ℕ) (x : Cochain E Finset.univ M n) :
    takeNew E S M (n + 1) (differential E Finset.univ M n x) =
      takeNew E S M (n + 1) (differential E Finset.univ M n (putNew E S M n (takeNew E S M n x))) := by
  rw [differential_split, map_add, takeNew_extension, zero_add]

lemma closed_takeOld (n : ℕ) (x : Cochain E Finset.univ M n)
    (hx : differential E Finset.univ M n x = 0) (hn : takeNew E S M n x = 0) :
    differential E S M n (takeOld E S M n x) = 0 := by
  have he : extension E S M (Finset.subset_univ S) n (takeOld E S M n x) = x := by
    have hh := split_identity E S M n x
    rw [hn, map_zero, add_zero] at hh
    exact hh
  apply extension_injective E S M (Finset.subset_univ S) (n + 1)
  rw [← extension_differential, he, hx, map_zero]

lemma parts_injective (n : ℕ) (x y : Cochain E Finset.univ M n)
    (ho : takeOld E S M n x = takeOld E S M n y)
    (hn : takeNew E S M n x = takeNew E S M n y) : x = y := by
  calc
    x = _ := (split_identity E S M n x).symm
    _ = _ := by rw [ho, hn]
    _ = y := split_identity E S M n y

/-- The coordinate window for an inclusion-chain complex with proved full-support exactness. -/
def windowOfExact [∀ i, DecidableEq (E i)] (p : ℕ)
    (hfull : ∀ x : Cochain E Finset.univ M (p + 1),
      differential E Finset.univ M (p + 1) x = 0 → ∃ u, differential E Finset.univ M p u = x) :
    RelativeWindow (Coordinate E S M p) (NewCoordinate E S M p)
      (Coordinate E S M (p + 1)) (NewCoordinate E S M (p + 1))
      (Coordinate E S M (p + 2)) where
  oldD := (pack E S M (p + 1)).symm.toLinearMap ∘ₗ differential E S M p ∘ₗ (pack E S M p).toLinearMap
  liftD := (pack E S M (p + 1)).symm.toLinearMap ∘ₗ takeOld E S M (p + 1) ∘ₗ
    differential E Finset.univ M p ∘ₗ putNew E S M p
  relativeD := takeNew E S M (p + 1) ∘ₗ differential E Finset.univ M p ∘ₗ putNew E S M p
  nextOldD := (pack E S M (p + 2)).symm.toLinearMap ∘ₗ differential E S M (p + 1) ∘ₗ
    (pack E S M (p + 1)).toLinearMap
  old_square_zero := by
    intro u
    change (pack E S M (p + 2)).symm
      (differential E S M (p + 1) (differential E S M p (pack E S M p u))) = 0
    rw [differential_squared, map_zero]
  lift_closed := by
    intro v hv
    change (pack E S M (p + 2)).symm
      (differential E S M (p + 1) (takeOld E S M (p + 1)
        (differential E Finset.univ M p (putNew E S M p v)))) = 0
    rw [closed_takeOld E S M (p + 1) _ (differential_squared E Finset.univ M p _) hv, map_zero]
  full_exact := by
    intro c hc
    have hclosed : differential E S M (p + 1) (pack E S M (p + 1) c) = 0 := by
      exact (pack E S M (p + 2)).symm.injective (by simpa using hc)
    have hfclosed : differential E Finset.univ M (p + 1)
        (extension E S M (Finset.subset_univ S) (p + 1) (pack E S M (p + 1) c)) = 0 := by
      rw [extension_differential, hclosed, map_zero]
    obtain ⟨u, hu⟩ := hfull _ hfclosed
    refine ⟨(pack E S M p).symm (takeOld E S M p u), takeNew E S M p u, ?_, ?_⟩
    · change (pack E S M (p + 1)).symm (differential E S M p (takeOld E S M p u)) +
        (pack E S M (p + 1)).symm (takeOld E S M (p + 1)
          (differential E Finset.univ M p (putNew E S M p (takeNew E S M p u)))) = c
      rw [← map_add, ← differential_takeOld, hu, takeOld_extension, LinearEquiv.symm_apply_apply]
    · change takeNew E S M (p + 1)
        (differential E Finset.univ M p (putNew E S M p (takeNew E S M p u))) = 0
      rw [← differential_takeNew, hu, takeNew_extension]

variable [∀ i, DecidableEq (E i)]
    (p : ℕ) (hfull : ∀ x : Cochain E Finset.univ M (p + 1),
      differential E Finset.univ M (p + 1) x = 0 → ∃ u, differential E Finset.univ M p u = x)

def cycleEquivOfExact : LinearMap.ker (windowOfExact E S M p hfull).nextOldD ≃ₗ[ℝ]
    LinearMap.ker (differential E S M (p + 1)) where
  toFun c := ⟨pack E S M (p + 1) c.val, by
    apply (pack E S M (p + 2)).symm.injective
    exact c.property⟩
  invFun c := ⟨(pack E S M (p + 1)).symm c.val, by
    change (pack E S M (p + 2)).symm (differential E S M (p + 1) c.val) = 0
    rw [c.property, map_zero]⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl
  map_add' c d := by apply Subtype.ext; rfl
  map_smul' a c := by apply Subtype.ext; rfl

lemma cycleEquivOfExact_boundaries :
    (LinearMap.range (windowOfExact E S M p hfull).boundariesToCycles).map
      (cycleEquivOfExact E S M p hfull).toLinearMap = LinearMap.range (boundaries E S M p) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨pack E S M p u, Subtype.ext rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(windowOfExact E S M p hfull).boundariesToCycles ((pack E S M p).symm u),
      ⟨_, rfl⟩, Subtype.ext rfl⟩

/-- The cohomology of the concrete coordinate window is the original Cech
cohomology, with the original boundaries. -/
def cohomologyEquivOfExact : (windowOfExact E S M p hfull).Cohomology ≃ₗ[ℝ] Cohomology E S M p :=
  Submodule.Quotient.equiv _ _ (cycleEquivOfExact E S M p hfull) (cycleEquivOfExact_boundaries E S M p hfull)

end General
section Linear
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

/-- The original Cech window: full-support exactness is supplied by its proved theorem. -/
def window [∀ i, DecidableEq (E i)] (o : State E) (p : ℕ) :=
  windowOfExact E S M p (FullSupportAcyclicity.full_exists_primitive E o M p)

variable [∀ i, DecidableEq (E i)] (o : State E)

def cycleEquiv (p : ℕ) : LinearMap.ker (window E S M o p).nextOldD ≃ₗ[ℝ]
    LinearMap.ker (differential E S M (p + 1)) where
  toFun c := ⟨pack E S M (p + 1) c.val, by
    apply (pack E S M (p + 2)).symm.injective
    exact c.property⟩
  invFun c := ⟨(pack E S M (p + 1)).symm c.val, by
    change (pack E S M (p + 2)).symm (differential E S M (p + 1) c.val) = 0
    rw [c.property, map_zero]⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl
  map_add' c d := by apply Subtype.ext; rfl
  map_smul' a c := by apply Subtype.ext; rfl

lemma cycleEquiv_boundaries (p : ℕ) :
    (LinearMap.range (window E S M o p).boundariesToCycles).map
      (cycleEquiv E S M o p).toLinearMap = LinearMap.range (boundaries E S M p) := by
  ext c
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨pack E S M p u, Subtype.ext rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(window E S M o p).boundariesToCycles ((pack E S M p).symm u),
      ⟨_, rfl⟩, Subtype.ext rfl⟩

/-- The cohomology of the concrete coordinate window is the original Cech
cohomology, with the original boundaries. -/
def cohomologyEquiv (p : ℕ) : (window E S M o p).Cohomology ≃ₗ[ℝ] Cohomology E S M p :=
  Submodule.Quotient.equiv _ _ (cycleEquiv E S M o p) (cycleEquiv_boundaries E S M o p)

end Linear
end CechSplitting
end WeightedObstructionNorms
