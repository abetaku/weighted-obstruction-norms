import WeightedObstructionNorms.Comparison
import WeightedObstructionNorms.Reciprocal
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A split window of a short exact sequence of finite cochain complexes.
All cohomology classes below are actual quotients of cocycles by boundaries.
The remaining Cech-specific task is to instantiate this window and prove
its full-support exactness hypothesis from the concrete Cech differential. -/
noncomputable section
open Set
namespace WeightedObstructionNorms

structure RelativeWindow (U X V Y Z : Type*) [Fintype U] [Fintype X]
    [Fintype V] [Fintype Y] [Fintype Z] where
  oldD : (U → ℝ) →ₗ[ℝ] (V → ℝ)
  liftD : (X → ℝ) →ₗ[ℝ] (V → ℝ)
  relativeD : (X → ℝ) →ₗ[ℝ] (Y → ℝ)
  nextOldD : (V → ℝ) →ₗ[ℝ] (Z → ℝ)
  old_square_zero : ∀ u, nextOldD (oldD u) = 0
  lift_closed : ∀ v, relativeD v = 0 → nextOldD (liftD v) = 0
  full_exact : ∀ c, nextOldD c = 0 →
    ∃ u v, oldD u + liftD v = c ∧ relativeD v = 0

namespace RelativeWindow
variable {U X V Y Z : Type*} [Fintype U] [Fintype X]
    [Fintype V] [Fintype Y] [Fintype Z]
    (W : RelativeWindow U X V Y Z)

def boundariesToCycles : (U → ℝ) →ₗ[ℝ] LinearMap.ker W.nextOldD :=
  W.oldD.codRestrict _ W.old_square_zero

abbrev Cohomology := (LinearMap.ker W.nextOldD) ⧸ LinearMap.range W.boundariesToCycles

def classOf (c : LinearMap.ker W.nextOldD) : W.Cohomology :=
  (LinearMap.range W.boundariesToCycles).mkQ c

def liftToCycles : LinearMap.ker W.relativeD →ₗ[ℝ] LinearMap.ker W.nextOldD where
  toFun v := ⟨W.liftD v, W.lift_closed v v.property⟩
  map_add' v w := by apply Subtype.ext; exact map_add W.liftD (v : X → ℝ) (w : X → ℝ)
  map_smul' a v := by apply Subtype.ext; exact map_smul W.liftD a (v : X → ℝ)

/-- Connecting map on relative cocycles, landing in actual old cohomology. -/
def connecting : LinearMap.ker W.relativeD →ₗ[ℝ] W.Cohomology :=
  (LinearMap.range W.boundariesToCycles).mkQ.comp W.liftToCycles

lemma classOf_eq_iff (c d : LinearMap.ker W.nextOldD) :
    W.classOf c = W.classOf d ↔ ∃ u, W.oldD u = (c : V → ℝ) - d := by
  change Submodule.Quotient.mk c = (Submodule.Quotient.mk d : W.Cohomology) ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, Subtype.ext hu⟩

lemma connecting_eq_iff (v : LinearMap.ker W.relativeD) (c : LinearMap.ker W.nextOldD) :
    W.connecting v = W.classOf c ↔ ∃ u, W.oldD u + W.liftD v = c := by
  change W.classOf (W.liftToCycles v) = W.classOf c ↔ _
  rw [eq_comm, W.classOf_eq_iff]
  change (∃ u, W.oldD u = (c : V → ℝ) - W.liftD v) ↔ _
  simp only [eq_sub_iff_add_eq]

/-- Full-support exactness implies surjectivity of the connecting map. -/
theorem connecting_surjective : Function.Surjective W.connecting := by
  intro α
  obtain ⟨c, hc⟩ := Submodule.mkQ_surjective (LinearMap.range W.boundariesToCycles) α
  obtain ⟨u, v, huv, hv⟩ := W.full_exact c c.property
  refine ⟨⟨v, hv⟩, ?_⟩
  calc
    W.connecting ⟨v, hv⟩ = W.classOf c := (W.connecting_eq_iff _ c).2 ⟨u, huv⟩
    _ = α := hc

/-- The full differential in old/new coordinates has the block form
(u,v) ↦ (oldD u + liftD v, relativeD v). -/
def problem (c : LinearMap.ker W.nextOldD) : LinearProblem U X ((V → ℝ) × (Y → ℝ)) where
  A₀ := W.oldD.prod 0
  A₁ := W.liftD.prod W.relativeD
  b := (c, 0)
  feasible := by
    obtain ⟨u, v, huv, hv⟩ := W.full_exact c c.property
    exact ⟨u, v, Prod.ext huv (by simpa using hv)⟩

/-- The quotient equation of Section 3 is precisely the relative cocycle
and connecting-class condition of Section 4. -/
theorem quotient_condition (c : LinearMap.ker W.nextOldD) (v : X → ℝ) :
    v ∈ (W.problem c).quotientFeasible ↔
      ∃ hv : W.relativeD v = 0, W.connecting ⟨v, hv⟩ = W.classOf c := by
  rw [(W.problem c).quotientFeasible_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hfirst : W.oldD u + W.liftD v = c := congrArg Prod.fst hu
    have hsecond : W.relativeD v = 0 := by simpa [problem] using congrArg Prod.snd hu
    exact ⟨hsecond, (W.connecting_eq_iff _ c).2 ⟨u, hfirst⟩⟩
  · rintro ⟨hv, hc⟩
    obtain ⟨u, hu⟩ := (W.connecting_eq_iff _ c).1 hc
    exact ⟨u, Prod.ext hu (by simpa [problem] using hv)⟩

def relativeFeasible (α : W.Cohomology) : Set (X → ℝ) :=
  {v | ∃ hv : W.relativeD v = 0, W.connecting ⟨v, hv⟩ = α}

def obstructionValue (r : X → ℝ) (α : W.Cohomology) : ℝ := minimum r (W.relativeFeasible α)

lemma feasible_eq (c : LinearMap.ker W.nextOldD) :
    W.relativeFeasible (W.classOf c) = (W.problem c).quotientFeasible := by
  ext v
  exact (W.quotient_condition c v).symm

/-- Equality of the actual optimization problems, not just an inequality. -/
theorem obstruction_eq_coefficient (r : X → ℝ) (c : LinearMap.ker W.nextOldD) :
    W.obstructionValue r (W.classOf c) = (W.problem c).coefficient r := by
  simp only [obstructionValue, LinearProblem.coefficient, W.feasible_eq]

lemma relativeFeasible_nonempty (α : W.Cohomology) : (W.relativeFeasible α).Nonempty := by
  obtain ⟨v, hv⟩ := W.connecting_surjective α
  exact ⟨v, v.property, hv⟩

lemma obstruction_attained {r : X → ℝ} (hr : ∀ j, 0 < r j) (α : W.Cohomology) :
    ∃ v ∈ W.relativeFeasible α, weightedNorm r v = W.obstructionValue r α := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range W.boundariesToCycles) α
  change ∃ v ∈ W.relativeFeasible (W.classOf c), weightedNorm r v = W.obstructionValue r (W.classOf c)
  rw [W.feasible_eq, W.obstruction_eq_coefficient]
  exact (W.problem c).coefficient_attained hr

/-- Relative unit-ball formula, with the cocycle restriction retained. -/
theorem relative_unit_ball {r : X → ℝ} (hr : ∀ j, 0 < r j) (α : W.Cohomology) :
    W.obstructionValue r α ≤ 1 ↔
      ∃ v : LinearMap.ker W.relativeD, W.connecting v = α ∧ ∀ j, |(v : X → ℝ) j| ≤ r j := by
  constructor
  · intro h
    obtain ⟨v, ⟨hv, hc⟩, hmin⟩ := W.obstruction_attained hr α
    refine ⟨⟨v, hv⟩, hc, ?_⟩
    have hb := (weightedNorm_le_iff hr (by norm_num : (0 : ℝ) ≤ 1)).1 (hmin.trans_le h)
    simpa using hb
  · rintro ⟨v, hc, hb⟩
    have hfeas : (v : X → ℝ) ∈ W.relativeFeasible α := ⟨v.property, hc⟩
    exact (minimum_le hfeas).trans ((weightedNorm_le_iff hr (by norm_num)).2 (by simpa using hb))

/-- The connecting kernel is exactly the relative image of closed full
cochains; this kernel need not vanish in augmented degree minus one. -/
theorem connecting_kernel (v : LinearMap.ker W.relativeD) :
    W.connecting v = 0 ↔ ∃ u, W.oldD u + W.liftD v = 0 := by
  have hz : W.classOf 0 = 0 := map_zero (LinearMap.range W.boundariesToCycles).mkQ
  rw [← hz, W.connecting_eq_iff]
  rfl


lemma obstruction_nonneg (r : X → ℝ) (α : W.Cohomology) :
    0 ≤ W.obstructionValue r α := minimum_nonneg (W.relativeFeasible_nonempty α)

lemma obstruction_zero (r : X → ℝ) : W.obstructionValue r 0 = 0 := by
  have hfeas : (0 : X → ℝ) ∈ W.relativeFeasible 0 := ⟨map_zero W.relativeD, map_zero W.connecting⟩
  exact le_antisymm (by simpa [weightedNorm_zero] using (minimum_le (w := r) hfeas))
    (W.obstruction_nonneg r 0)

lemma obstruction_eq_zero_iff {r : X → ℝ} (hr : ∀ j, 0 < r j) (α : W.Cohomology) :
    W.obstructionValue r α = 0 ↔ α = 0 := by
  constructor
  · intro h
    obtain ⟨v, ⟨hv, hc⟩, hmin⟩ := W.obstruction_attained hr α
    have hz := (weightedNorm_eq_zero_iff hr).1 (hmin.trans h)
    subst v
    have hz' : (⟨0, hv⟩ : LinearMap.ker W.relativeD) = 0 := rfl
    simpa [hz'] using hc.symm
  · rintro rfl
    exact W.obstruction_zero r

lemma relativeFeasible_add {α β : W.Cohomology} {x y : X → ℝ}
    (hx : x ∈ W.relativeFeasible α) (hy : y ∈ W.relativeFeasible β) :
    x + y ∈ W.relativeFeasible (α + β) := by
  obtain ⟨hx, hcx⟩ := hx
  obtain ⟨hy, hcy⟩ := hy
  refine ⟨by simp [hx, hy], ?_⟩
  change W.connecting ((⟨x, hx⟩ : LinearMap.ker W.relativeD) + ⟨y, hy⟩) = α + β
  rw [map_add, hcx, hcy]

lemma obstruction_add_le {r : X → ℝ} (hr : ∀ j, 0 < r j) (α β : W.Cohomology) :
    W.obstructionValue r (α + β) ≤ W.obstructionValue r α + W.obstructionValue r β := by
  obtain ⟨x, hx, hxmin⟩ := W.obstruction_attained hr α
  obtain ⟨y, hy, hymin⟩ := W.obstruction_attained hr β
  exact (minimum_le (W.relativeFeasible_add hx hy)).trans
    (by simpa [hxmin, hymin] using (weightedNorm_add_le (w := r) (x := x) (y := y)))

lemma relativeFeasible_smul (a : ℝ) {α : W.Cohomology} {x : X → ℝ}
    (hx : x ∈ W.relativeFeasible α) : a • x ∈ W.relativeFeasible (a • α) := by
  obtain ⟨hx, hcx⟩ := hx
  refine ⟨by simp [hx], ?_⟩
  change W.connecting (a • (⟨x, hx⟩ : LinearMap.ker W.relativeD)) = a • α
  rw [map_smul, hcx]

lemma obstruction_smul_le {r : X → ℝ} (hr : ∀ j, 0 < r j) (a : ℝ) (α : W.Cohomology) :
    W.obstructionValue r (a • α) ≤ |a| * W.obstructionValue r α := by
  obtain ⟨x, hx, hmin⟩ := W.obstruction_attained hr α
  exact (minimum_le (W.relativeFeasible_smul a hx)).trans_eq (by rw [weightedNorm_smul, hmin])

lemma obstruction_smul_eq {r : X → ℝ} (hr : ∀ j, 0 < r j) (a : ℝ) (α : W.Cohomology) :
    W.obstructionValue r (a • α) = |a| * W.obstructionValue r α := by
  by_cases ha : a = 0
  · simp [ha, W.obstruction_zero]
  apply le_antisymm (W.obstruction_smul_le hr a α)
  have h := W.obstruction_smul_le hr a⁻¹ (a • α)
  rw [inv_smul_smul₀ ha, abs_inv] at h
  have h' := mul_le_mul_of_nonneg_left h (abs_nonneg a)
  simpa [mul_assoc, abs_ne_zero.mpr ha] using h'


/-- Exact reciprocal primitive cost for a nonzero class in the actual
cohomology quotient of the split window. -/
theorem primitive_reciprocal {r : X → ℝ} {wbar slope : U → ℝ}
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < wbar j)
    (c : LinearMap.ker W.nextOldD) (hc : W.classOf c ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      (W.problem c).gamma (fun j => wbar j + ε * slope j) (fun j => ε * r j) =
        W.obstructionValue r (W.classOf c) / ε := by
  have hk : 0 < (W.problem c).coefficient r := by
    have hn := W.obstruction_nonneg r (W.classOf c)
    have hne : W.obstructionValue r (W.classOf c) ≠ 0 := by
      intro h
      exact hc ((W.obstruction_eq_zero_iff hr _).1 h)
    rw [← W.obstruction_eq_coefficient]
    exact lt_of_le_of_ne hn (Ne.symm hne)
  obtain ⟨η, hη, hrec⟩ := (W.problem c).affine_reciprocal (r₀ := slope) hw hr hk
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη
  simpa [W.obstruction_eq_coefficient] using (hrec ε hε hεη).2

end RelativeWindow
end WeightedObstructionNorms
