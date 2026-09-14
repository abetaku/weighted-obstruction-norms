import WeightedObstructionNorms.OrderComparison

noncomputable section
namespace WeightedObstructionNorms
namespace OrderPrimitiveComparison
open Filter Topology
open FiniteObservations CechAllDegrees OrderComparison
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (O : Finset (Finset I))

lemma restriction_injective (n : ℕ) (h : Function.Surjective (chainTuple O (n := n))) :
    Function.Injective (restriction E S O n) := by
  intro x y hxy
  apply (cochainEquiv E S O n h).injective
  simpa only [cochainEquiv_apply] using hxy

lemma feasible_iff (p : ℕ) (c : LinearMap.ker (differential E S (list O) (p + 1)))
    (hinj : ∀ z : Cochain E Finset.univ (list O) (p + 1),
      differential E Finset.univ (list O) (p + 1) z = 0 → restriction E Finset.univ O (p + 1) z = 0 → z = 0)
    (x : Cochain E Finset.univ (list O) p) :
    OrderComplex.differential E O Finset.univ p (restriction E Finset.univ O p x) =
        extension E S (OrderComplex.observations O) (Finset.subset_univ S) (p + 1) (restriction E S O (p + 1) c.val) ↔
      differential E Finset.univ (list O) p x = extension E S (list O) (Finset.subset_univ S) (p + 1) c.val := by
  simp only [OrderComparison.restriction]
  rw [OrderRestriction.restriction_differential E Finset.univ (list O) O (selection O) (selection_valid O) p x,
    ← OrderRestriction.restriction_extension E S (list O) O (selection O) (selection_valid O) (Finset.subset_univ S) (p + 1) c.val]
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply hinj
    · rw [map_sub, differential_squared, extension_differential, c.property, map_zero, sub_self]
    · rw [map_sub]
      exact sub_eq_zero.mpr h
  · intro h
    rw [h]

lemma cost_eq (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z) (p : ℕ)
    (h : Function.Surjective (chainTuple O (n := p)))
    (hinj : ∀ z : Cochain E Finset.univ (list O) (p + 1),
      differential E Finset.univ (list O) (p + 1) z = 0 → restriction E Finset.univ O (p + 1) z = 0 → z = 0)
    (c : LinearMap.ker (differential E S (list O) (p + 1))) :
    CechPrimitive.cost E S (OrderComplex.observations O) q p (restriction E S O (p + 1) c.val) =
      CechPrimitive.cost E S (list O) q p c.val := by
  unfold CechPrimitive.cost
  congr 1
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := (cochainEquiv E Finset.univ O p h).surjective y
    rw [cochainEquiv_apply] at hx
    subst y
    exact ⟨x, (feasible_iff E S O p c hinj x).1 hy,
      (cochain_norm_eq_of_surjective E Finset.univ O o hq p h x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨restriction E Finset.univ O p x, (feasible_iff E S O p c hinj x).2 hx,
      cochain_norm_eq_of_surjective E Finset.univ O o hq p h x⟩

lemma cost_eq_zero (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)
    (c : LinearMap.ker (differential E S (list O) 1)) :
    CechPrimitive.cost E S (OrderComplex.observations O) q 0 (restriction E S O 1 c.val) =
      CechPrimitive.cost E S (list O) q 0 c.val := by
  apply cost_eq E S O o hq 0 (chainTuple_surjective_zero O) _ c
  intro z _ hz
  apply restriction_injective E Finset.univ O 1 (chainTuple_surjective_one O)
  simpa only [map_zero] using hz

variable (o : State E) (hO : ∀ A ∈ O, ∀ B, B ⊆ A → B ∈ O)

/-- Equality of primitive spaces with their norms passes to obstruction norms. -/
theorem norm_eq (p : ℕ) (h : Function.Surjective (chainTuple O (n := p)))
    (hinj : ∀ z : Cochain E Finset.univ (list O) (p + 1),
      differential E Finset.univ (list O) (p + 1) z = 0 → restriction E Finset.univ O (p + 1) z = 0 → z = 0)
    {q : State E → ℝ} (hq : ∀ z, 0 < q z) (α : Cohomology E S (list O) p) :
    OrderObstruction.norm E S O o hO q p (cohomologyMap E S O p α) = CechObstruction.norm E S (list O) o q p α := by
  classical
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    let q₀ : State E → ℝ := fun z => if z ∈ S then 1 else 0
    have h₀ : ∀ z, 0 ≤ q₀ z := by intro z; simp [q₀]; split_ifs <;> norm_num
    have hS : ∀ z ∈ S, 0 < q₀ z := by intro z hz; simp [q₀, hz]
    have hz : ∀ z, z ∉ S → q₀ z = 0 := by intro z hz; simp [q₀, hz]
    have hr := CechReciprocal.norm_limit E S (list O) o h₀ hS hz hq p
      ((CechSplitting.cycleEquiv E S (list O) o p).symm c)
    have hl := OrderObstruction.norm_limit E S O o hO h₀ hS hz hq p
      ((CechSplitting.cycleEquivOfExact E S (OrderComplex.observations O) p
        (OrderComplex.full_exists_primitive E O o hO p)).symm
          (OrderRestriction.cycleMap E S (list O) O (selection O) (selection_valid O) p c))
    have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := Ioc_mem_nhdsGT (by norm_num)
    have he : (fun ε => ε * CechPrimitive.cost E S (OrderComplex.observations O) (CechReciprocal.mixture E q₀ q ε) p
        (restriction E S O (p + 1) c.val)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ε * CechPrimitive.cost E S (list O) (CechReciprocal.mixture E q₀ q ε) p c.val) := by
      filter_upwards [hs] with ε hε
      rw [cost_eq E S O o (CechReciprocal.mixture_positive E h₀ hq hε.1 hε.2) p h hinj c]
    exact tendsto_nhds_unique (hl.congr' he) hr

/-- Proposition A.1 in degree zero: equality of the actual obstruction norms. -/
theorem norm_eq_zero {q : State E → ℝ} (hq : ∀ z, 0 < q z) (α : Cohomology E S (list O) 0) :
    OrderObstruction.norm E S O o hO q 0 (cohomologyMap E S O 0 α) = CechObstruction.norm E S (list O) o q 0 α := by
  apply norm_eq E S O o hO 0 (chainTuple_surjective_zero O) _ hq α
  intro z _ hz
  apply restriction_injective E Finset.univ O 1 (chainTuple_surjective_one O)
  simpa only [map_zero] using hz

end OrderPrimitiveComparison
end WeightedObstructionNorms
