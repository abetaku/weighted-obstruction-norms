import WeightedObstructionNorms.OrderComplex
import WeightedObstructionNorms.CechReciprocal

noncomputable section
open Filter Topology
namespace WeightedObstructionNorms
namespace OrderObstruction
open FiniteObservations CechAllDegrees CechSplitting CechReciprocal OrderComplex
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I)) (o : State E)
    (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

def window (p : ℕ) := windowOfExact E S (observations O) p (OrderComplex.full_exists_primitive E O o hO p)
def cohomologyEquiv (p : ℕ) : (window E S O o hO p).Cohomology ≃ₗ[ℝ] OrderComplex.Cohomology E O S p :=
  cohomologyEquivOfExact E S (observations O) p (OrderComplex.full_exists_primitive E O o hO p)

def norm (q : State E → ℝ) (p : ℕ) (α : OrderComplex.Cohomology E O S p) : ℝ :=
  (window E S O o hO p).obstructionValue (CechObstruction.newWeight E S (observations O) q p)
    ((cohomologyEquiv E S O o hO p).symm α)

lemma norm_nonneg (q : State E → ℝ) (p : ℕ) (α : OrderComplex.Cohomology E O S p) :
    0 ≤ norm E S O o hO q p α := (window E S O o hO p).obstruction_nonneg _ _
lemma norm_zero (q : State E → ℝ) (p : ℕ) : norm E S O o hO q p 0 = 0 := by
  simp [norm, RelativeWindow.obstruction_zero]
lemma norm_eq_zero_iff {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α : OrderComplex.Cohomology E O S p) : norm E S O o hO q p α = 0 ↔ α = 0 := by
  rw [norm, (window E S O o hO p).obstruction_eq_zero_iff (CechObstruction.newWeight_positive E S (observations O) o hq p)]
  exact (cohomologyEquiv E S O o hO p).symm.map_eq_zero_iff
lemma norm_add_le {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (α β : OrderComplex.Cohomology E O S p) :
    norm E S O o hO q p (α + β) ≤ norm E S O o hO q p α + norm E S O o hO q p β := by
  unfold norm
  rw [map_add]
  exact (window E S O o hO p).obstruction_add_le (CechObstruction.newWeight_positive E S (observations O) o hq p) _ _
lemma norm_smul {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ) (a : ℝ)
    (α : OrderComplex.Cohomology E O S p) : norm E S O o hO q p (a • α) = |a| * norm E S O o hO q p α := by
  unfold norm
  rw [map_smul]
  exact (window E S O o hO p).obstruction_smul_eq (CechObstruction.newWeight_positive E S (observations O) o hq p) a _

/-- The rescaled limit includes zero obstruction classes. -/
theorem norm_limit {q₀ q₁ : State E → ℝ}
    (h₀ : ∀ z, 0 ≤ q₀ z) (hS : ∀ z ∈ S, 0 < q₀ z)
    (hz : ∀ z, z ∉ S → q₀ z = 0) (h₁ : ∀ z, 0 < q₁ z)
    (p : ℕ) (c : LinearMap.ker (window E S O o hO p).nextOldD) :
    Tendsto (fun ε => ε * CechPrimitive.cost E S (observations O) (mixture E q₀ q₁ ε) p
      (pack E S (observations O) (p + 1) c.val)) (𝓝[>] (0 : ℝ))
      (𝓝 (norm E S O o hO q₁ p
        (cohomologyEquiv E S O o hO p ((window E S O o hO p).classOf c)))) := by
  letI : ∀ i, Nonempty (E i) := fun i => ⟨o i⟩
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hw : ∀ j, 0 < coordinateWeight E S (observations O) q₀ p j := fun j => weight_on_support E S h₀ hS _ j.2
  have hr := CechObstruction.newWeight_positive E S (observations O) o h₁ p
  have hwlim (j : Coordinate E S (observations O) p) :
      Tendsto (fun ε => coordinateWeight E S (observations O) (mixture E q₀ q₁ ε) p j)
        (𝓝[>] (0 : ℝ)) (𝓝 (coordinateWeight E S (observations O) q₀ p j)) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub he).mul
      (tendsto_const_nhds (x := weight E q₀ (observation (observations O) j.1) j.2.val))).add
      (he.mul (tendsto_const_nhds (x := weight E q₁ (observation (observations O) j.1) j.2.val)))
    simpa [coordinateWeight, weight_mixture] using hh
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := Ioc_mem_nhdsGT (by norm_num)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∀ j, 0 < coordinateWeight E S (observations O) (mixture E q₀ q₁ ε) p j) ∧
      (∀ j, 0 < CechObstruction.newWeight E S (observations O) q₁ p j) ∧ 0 < ε := by
    filter_upwards [hsmall] with ε hε
    exact ⟨coordinateWeight_positive E S (observations O) (mixture_positive E h₀ h₁ hε.1 hε.2) p, hr, hε.1⟩
  have hh := ((window E S O o hO p).problem c).common_scale_limit hw hr hwlim
    (fun _ => tendsto_const_nhds) he hpos
  have hv : ((window E S O o hO p).problem c).coefficient (CechObstruction.newWeight E S (observations O) q₁ p) =
      norm E S O o hO q₁ p
        (cohomologyEquiv E S O o hO p ((window E S O o hO p).classOf c)) := by
    rw [norm, LinearEquiv.symm_apply_apply, RelativeWindow.obstruction_eq_coefficient]
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [hsmall] with ε hε
  rw [CechPrimitive.cost_eq_gamma_of_exact E S (observations O) o (mixture_positive E h₀ h₁ hε.1 hε.2) p (OrderComplex.full_exists_primitive E O o hO p)]
  congr 2
  funext j
  unfold CechObstruction.newWeight
  rw [weight_mixture, weight_outside_support E S hz _ _ j.2.property]
  ring


def Normed (_o : State E) (_hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O) (q : State E → ℝ) (_hq : ∀ z, 0 < q z) (p : ℕ) := OrderComplex.Cohomology E O S p

namespace Normed
variable {E S O o hO} {q : State E → ℝ} {hq : ∀ z, 0 < q z} {p : ℕ}
instance : AddCommGroup (Normed E S O o hO q hq p) := inferInstanceAs (AddCommGroup (OrderComplex.Cohomology E O S p))
instance : Module ℝ (Normed E S O o hO q hq p) := inferInstanceAs (Module ℝ (OrderComplex.Cohomology E O S p))
instance : Norm (Normed E S O o hO q hq p) := ⟨OrderObstruction.norm E S O o hO q p⟩
def normCore : NormedSpace.Core ℝ (Normed E S O o hO q hq p) where
  norm_nonneg := norm_nonneg E S O o hO q p
  norm_triangle := norm_add_le E S O o hO hq p
  norm_smul a x := norm_smul E S O o hO hq p a x
  norm_eq_zero_iff := norm_eq_zero_iff E S O o hO hq p
instance : NormedAddCommGroup (Normed E S O o hO q hq p) := NormedAddCommGroup.ofCore normCore
instance : NormedSpace ℝ (Normed E S O o hO q hq p) := NormedSpace.ofCore normCore
instance : FiniteDimensional ℝ (Normed E S O o hO q hq p) :=
  inferInstanceAs (FiniteDimensional ℝ (OrderComplex.Cohomology E O S p))
end Normed

end OrderObstruction
end WeightedObstructionNorms
