import WeightedObstructionNorms.CechPrimitive
import WeightedObstructionNorms.CommonScale

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators Topology
open Filter
namespace WeightedObstructionNorms
namespace CechReciprocal
open FiniteObservations CechAllDegrees CechSplitting
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)

def mixture (q₀ q₁ : State E → ℝ) (ε : ℝ) : State E → ℝ :=
  fun z => (1 - ε) * q₀ z + ε * q₁ z

lemma mixture_positive {q₀ q₁ : State E → ℝ} (h₀ : ∀ z, 0 ≤ q₀ z) (h₁ : ∀ z, 0 < q₁ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : ∀ z, 0 < mixture E q₀ q₁ ε z := by
  intro z
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hε1) (h₀ z)) (mul_pos hε (h₁ z))

lemma weight_mixture (q₀ q₁ : State E → ℝ) (ε : ℝ) (A : Finset I) (y : LocalState E A) :
    weight E (mixture E q₀ q₁ ε) A y = (1 - ε) * weight E q₀ A y + ε * weight E q₁ A y := by
  classical
  simp only [weight, Marginal.push, mixture, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

lemma weight_outside_support {q₀ : State E → ℝ} (h₀ : ∀ z, z ∉ S → q₀ z = 0)
    (A : Finset I) (y : LocalState E A) (hy : y ∉ projected E S A) : weight E q₀ A y = 0 := by
  classical
  unfold weight Marginal.push
  apply Finset.sum_eq_zero
  intro z _
  split_ifs with hz
  · apply h₀ z
    intro hs
    exact hy ((projected_mem E S A y).2 ⟨z, hs, hz⟩)
  · rfl

lemma weight_on_support {q₀ : State E → ℝ} (h₀ : ∀ z, 0 ≤ q₀ z) (hS : ∀ z ∈ S, 0 < q₀ z)
    (A : Finset I) (y : SupportState E S A) : 0 < weight E q₀ A y.val := by
  classical
  unfold weight Marginal.push
  obtain ⟨z, hz, he⟩ := (projected_mem E S A y.val).1 y.property
  apply Finset.sum_pos'
  · intro a _
    split_ifs <;> simp_all
  · exact ⟨z, Finset.mem_univ z, by simpa [he] using hS z hz⟩

/-- Corollary 3.2 for the manuscript's original primitive cost and an affine
mixture with exact old support S. No product-law assumption is made. -/
theorem primitive_reciprocal {q₀ q₁ : State E → ℝ}
    (h₀ : ∀ z, 0 ≤ q₀ z) (hS : ∀ z ∈ S, 0 < q₀ z)
    (hz : ∀ z, z ∉ S → q₀ z = 0) (h₁ : ∀ z, 0 < q₁ z)
    (p : ℕ) (c : LinearMap.ker (window E S M o p).nextOldD)
    (hc : cohomologyEquiv E S M o p ((window E S M o p).classOf c) ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      CechPrimitive.cost E S M (mixture E q₀ q₁ ε) p (pack E S M (p + 1) c.val) =
        CechObstruction.norm E S M o q₁ p
          (cohomologyEquiv E S M o p ((window E S M o p).classOf c)) / ε := by
  have hw : ∀ j, 0 < coordinateWeight E S M q₀ p j := fun j => weight_on_support E S h₀ hS _ j.2
  have hr := CechObstruction.newWeight_positive E S M o h₁ p
  have hc' : (window E S M o p).classOf c ≠ 0 := by
    intro hh
    apply hc
    rw [hh, map_zero]
  obtain ⟨η, hη, hrec⟩ := (window E S M o p).primitive_reciprocal
    (slope := fun j => coordinateWeight E S M q₁ p j - coordinateWeight E S M q₀ p j) hr hw c hc'
  refine ⟨min η 1, lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη
  have hε1 := (le_min_iff.mp hεη).2
  rw [CechPrimitive.cost_eq_gamma E S M o (mixture_positive E h₀ h₁ hε hε1)]
  have ho : coordinateWeight E S M (mixture E q₀ q₁ ε) p =
      fun j => coordinateWeight E S M q₀ p j + ε * (coordinateWeight E S M q₁ p j - coordinateWeight E S M q₀ p j) := by
    funext j
    unfold coordinateWeight
    rw [weight_mixture]
    ring
  have hn : CechObstruction.newWeight E S M (mixture E q₀ q₁ ε) p =
      fun j => ε * CechObstruction.newWeight E S M q₁ p j := by
    funext j
    unfold CechObstruction.newWeight
    rw [weight_mixture, weight_outside_support E S hz _ _ j.2.property]
    ring
  rw [ho, hn, CechObstruction.norm, LinearEquiv.symm_apply_apply]
  exact hrec ε hε (le_min_iff.mp hεη).1

/-- The rescaled limit includes zero obstruction classes. -/
theorem norm_limit {q₀ q₁ : State E → ℝ}
    (h₀ : ∀ z, 0 ≤ q₀ z) (hS : ∀ z ∈ S, 0 < q₀ z)
    (hz : ∀ z, z ∉ S → q₀ z = 0) (h₁ : ∀ z, 0 < q₁ z)
    (p : ℕ) (c : LinearMap.ker (window E S M o p).nextOldD) :
    Tendsto (fun ε => ε * CechPrimitive.cost E S M (mixture E q₀ q₁ ε) p
      (pack E S M (p + 1) c.val)) (𝓝[>] (0 : ℝ))
      (𝓝 (CechObstruction.norm E S M o q₁ p
        (cohomologyEquiv E S M o p ((window E S M o p).classOf c)))) := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hw : ∀ j, 0 < coordinateWeight E S M q₀ p j := fun j => weight_on_support E S h₀ hS _ j.2
  have hr := CechObstruction.newWeight_positive E S M o h₁ p
  have hwlim (j : Coordinate E S M p) :
      Tendsto (fun ε => coordinateWeight E S M (mixture E q₀ q₁ ε) p j)
        (𝓝[>] (0 : ℝ)) (𝓝 (coordinateWeight E S M q₀ p j)) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub he).mul
      (tendsto_const_nhds (x := weight E q₀ (observation M j.1) j.2.val))).add
      (he.mul (tendsto_const_nhds (x := weight E q₁ (observation M j.1) j.2.val)))
    simpa [coordinateWeight, weight_mixture] using hh
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := Ioc_mem_nhdsGT (by norm_num)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∀ j, 0 < coordinateWeight E S M (mixture E q₀ q₁ ε) p j) ∧
      (∀ j, 0 < CechObstruction.newWeight E S M q₁ p j) ∧ 0 < ε := by
    filter_upwards [hsmall] with ε hε
    exact ⟨coordinateWeight_positive E S M (mixture_positive E h₀ h₁ hε.1 hε.2) p, hr, hε.1⟩
  have hh := ((window E S M o p).problem c).common_scale_limit hw hr hwlim
    (fun _ => tendsto_const_nhds) he hpos
  have hv : ((window E S M o p).problem c).coefficient (CechObstruction.newWeight E S M q₁ p) =
      CechObstruction.norm E S M o q₁ p
        (cohomologyEquiv E S M o p ((window E S M o p).classOf c)) := by
    rw [CechObstruction.norm, LinearEquiv.symm_apply_apply, RelativeWindow.obstruction_eq_coefficient]
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [hsmall] with ε hε
  rw [CechPrimitive.cost_eq_gamma E S M o (mixture_positive E h₀ h₁ hε.1 hε.2)]
  congr 2
  funext j
  unfold CechObstruction.newWeight
  rw [weight_mixture, weight_outside_support E S hz _ _ j.2.property]
  ring

end CechReciprocal
end WeightedObstructionNorms
