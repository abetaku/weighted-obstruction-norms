import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Data.Real.Basic

/-! Algebraic lemmas needed by Sections 2, 4, 5 and Appendix A.
These do not claim to construct the paper's Čech contraction or refinement
homotopy. A homotopy is supplied explicitly as an argument. -/
noncomputable section
namespace WeightedObstructionNorms
section Complex
variable {V₀ V₁ V₂ W₀ W₁ W₂ : Type*}
  [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]
  [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
  [AddCommGroup W₂] [Module ℝ W₂]

/-- A cocycle is a boundary if a contracting homotopy has been constructed. -/
theorem exact_of_contraction (d₀ : V₀ →ₗ[ℝ] V₁) (d₁ : V₁ →ₗ[ℝ] V₂)
    (h₁ : V₁ →ₗ[ℝ] V₀) (h₂ : V₂ →ₗ[ℝ] V₁)
    (hcontract : ∀ x, d₀ (h₁ x) + h₂ (d₁ x) = x)
    {c : V₁} (hc : d₁ c = 0) : ∃ x, d₀ x = c := by
  refine ⟨h₁ c, ?_⟩
  simpa [hc] using hcontract c

/-- Explicit equivalence relation before passage to cohomology. -/
def Cohomologous (d₀ : V₀ →ₗ[ℝ] V₁) (c c' : V₁) : Prop :=
  c - c' ∈ LinearMap.range d₀

lemma cohomologous_refl (d₀ : V₀ →ₗ[ℝ] V₁) (c : V₁) : Cohomologous d₀ c c := by
  simp [Cohomologous]

lemma cohomologous_symm (d₀ : V₀ →ₗ[ℝ] V₁) {c c' : V₁}
    (h : Cohomologous d₀ c c') : Cohomologous d₀ c' c := by
  obtain ⟨x, hx⟩ := h
  refine ⟨-x, ?_⟩
  rw [map_neg, hx, neg_sub]

lemma cohomologous_trans (d₀ : V₀ →ₗ[ℝ] V₁) {a b c : V₁}
    (hab : Cohomologous d₀ a b) (hbc : Cohomologous d₀ b c) :
    Cohomologous d₀ a c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  refine ⟨x + y, ?_⟩
  rw [map_add, hx, hy, sub_add_sub_cancel]

/-- Choice independence from an explicitly supplied cochain homotopy. -/
theorem homotopic_cohomologous (d₁ : V₁ →ₗ[ℝ] V₂) (e₀ : W₀ →ₗ[ℝ] W₁)
    (F G : V₁ →ₗ[ℝ] W₁) (h₁ : V₁ →ₗ[ℝ] W₀) (h₂ : V₂ →ₗ[ℝ] W₁)
    (hhom : ∀ x, G x - F x = e₀ (h₁ x) + h₂ (d₁ x))
    {c : V₁} (hc : d₁ c = 0) : Cohomologous e₀ (G c) (F c) := by
  refine ⟨h₁ c, ?_⟩
  simpa [hc] using (hhom c).symm

/-- The connecting representative does not depend on a lift changed by an
old-support cochain. -/
theorem connecting_lift_independence
    (d₀ : V₀ →ₗ[ℝ] V₁) (e₀ : W₀ →ₗ[ℝ] W₁)
    (j₀ : V₀ →ₗ[ℝ] W₀) (j₁ : V₁ →ₗ[ℝ] W₁)
    (hj : Function.Injective j₁) (hchain : ∀ y, e₀ (j₀ y) = j₁ (d₀ y))
    {x x' : W₀} {c c' : V₁} {y : V₀}
    (hx : e₀ x = j₁ c) (hx' : e₀ x' = j₁ c') (hxy : x - x' = j₀ y) :
    Cohomologous d₀ c c' := by
  refine ⟨y, hj ?_⟩
  rw [← hchain, ← hxy, map_sub, hx, hx', map_sub]

/-- The degree-zero kernel issue: zero connecting class is equivalent to
modifying a lift by an old-support cochain to make it closed. -/
theorem connecting_kernel_iff_closed_lift
    (d₀ : V₀ →ₗ[ℝ] V₁) (e₀ : W₀ →ₗ[ℝ] W₁)
    (j₀ : V₀ →ₗ[ℝ] W₀) (j₁ : V₁ →ₗ[ℝ] W₁)
    (hj : Function.Injective j₁) (hchain : ∀ y, e₀ (j₀ y) = j₁ (d₀ y))
    {x : W₀} {c : V₁} (hx : e₀ x = j₁ c) :
    c ∈ LinearMap.range d₀ ↔ ∃ y, e₀ (x - j₀ y) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [map_sub, hx, hchain, sub_self]
  · rintro ⟨y, hy⟩
    refine ⟨y, hj ?_⟩
    rw [map_sub, hx, hchain, sub_eq_zero] at hy
    exact hy.symm

end Complex
end WeightedObstructionNorms
