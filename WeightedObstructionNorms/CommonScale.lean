import WeightedObstructionNorms.Reciprocal

noncomputable section
open Set Filter
open scoped Topology
namespace WeightedObstructionNorms

lemma tendsto_weightedNorm_weights {J T : Type*} [Fintype J] {l : Filter T}
    {w : T → J → ℝ} {wbar : J → ℝ} (hw : ∀ j, Tendsto (fun e => w e j) l (𝓝 (wbar j)))
    (hwbar : ∀ j, 0 < wbar j) (x : J → ℝ) :
    Tendsto (fun e => weightedNorm (w e) x) l (𝓝 (weightedNorm wbar x)) := by
  apply Filter.Tendsto.norm
  exact tendsto_pi_nhds.2 (fun j => tendsto_const_nhds.div (hw j) (hwbar j).ne')

namespace LinearProblem
variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  (P : LinearProblem J₀ J₁ B)

lemma scaled_gamma_upper {w₀ : J₀ → ℝ} {r' : J₁ → ℝ}
    (h₀ : ∀ j, 0 < w₀ j) (hr' : ∀ j, 0 < r' j) {t : ℝ} (ht : 0 < t)
    {u : J₀ → ℝ} {v : J₁ → ℝ} (hfeas : P.A₀ u + P.A₁ v = P.b) :
    t * P.gamma w₀ (fun j => t * r' j) ≤
      max (t * weightedNorm w₀ u) (weightedNorm r' v) := by
  let L := max (t * weightedNorm w₀ u) (weightedNorm r' v)
  have hL : 0 ≤ L := (weightedNorm_nonneg _ _).trans (le_max_right _ _)
  have hupper : P.gamma w₀ (fun j => t * r' j) ≤ L / t := by
    apply (minimum_le (x := Sum.elim u v) hfeas).trans
    apply (weightedNorm_le_iff (Sum.rec h₀ (fun j => mul_pos ht (hr' j)))
      (div_nonneg hL ht.le)).2
    intro j
    cases j with
    | inl j =>
      have hc := coordinate_le_weightedNorm (x := u) h₀ j
      have hm : weightedNorm w₀ u ≤ L / t := (le_div_iff₀ ht).2 (by
        have h := le_max_left (t * weightedNorm w₀ u) (weightedNorm r' v)
        dsimp [L]; nlinarith)
      exact hc.trans (mul_le_mul_of_nonneg_right hm (h₀ j).le)
    | inr j =>
      have hc := coordinate_le_weightedNorm (x := v) hr' j
      have hn : weightedNorm r' v ≤ L := le_max_right _ _
      dsimp
      rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']
      exact hc.trans (mul_le_mul_of_nonneg_right hn (hr' j).le)
  have h := (le_div_iff₀ ht).1 hupper
  nlinarith

lemma scaled_gamma_lower {r r' : J₁ → ℝ} {w₀ : J₀ → ℝ}
    (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j) (h₀ : ∀ j, 0 < w₀ j)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hrr' : ∀ j, r' j ≤ (1 + δ) * r j) :
    P.coefficient r / (1 + δ) ≤ t * P.gamma w₀ (fun j => t * r' j) := by
  obtain ⟨x, hx, hmin⟩ := P.gamma_attained h₀ (fun j => mul_pos ht (hr' j))
  let L := weightedNorm (Sum.elim w₀ (fun j => t * r' j)) x
  have hL : 0 ≤ L := weightedNorm_nonneg _ _
  have hv : (fun j => x (.inr j)) ∈ P.quotientFeasible :=
    (P.quotientFeasible_iff _).2 ⟨fun j => x (.inl j), hx⟩
  have hb : weightedNorm r (fun j => x (.inr j)) ≤ (1 + δ) * (t * L) := by
    apply (weightedNorm_le_iff hr (by positivity)).2
    intro j
    have hc := coordinate_le_weightedNorm (x := x)
      (w := Sum.elim w₀ (fun j => t * r' j)) (Sum.rec h₀ (fun j => mul_pos ht (hr' j))) (.inr j)
    have hm := mul_le_mul_of_nonneg_left (hrr' j) (mul_nonneg hL ht.le)
    dsimp at hc
    dsimp [L] at hm ⊢
    nlinarith
  have hk : P.coefficient r ≤ weightedNorm r (fun j => x (.inr j)) := minimum_le hv
  apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
  change L = P.gamma w₀ (fun j => t * r' j) at hmin
  rw [← hmin]
  nlinarith

/-- Common-scale rescaled limit from Proposition 3.4. Indexing by any filter
allows ε ↓ 0 by taking the right-neighborhood filter, or positive ε as a subtype.
New weights are t(e) r'(e), where r'(e) tends coordinatewise to r. -/
theorem common_scale_limit {T : Type*} {l : Filter T}
    {w : T → J₀ → ℝ} {wbar : J₀ → ℝ} {r' : T → J₁ → ℝ} {r : J₁ → ℝ}
    {t : T → ℝ}
    (hwbar : ∀ j, 0 < wbar j) (hr : ∀ j, 0 < r j)
    (hw : ∀ j, Tendsto (fun e => w e j) l (𝓝 (wbar j)))
    (hrlim : ∀ j, Tendsto (fun e => r' e j) l (𝓝 (r j)))
    (htlim : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ e in l, (∀ j, 0 < w e j) ∧ (∀ j, 0 < r' e j) ∧ 0 < t e) :
    Tendsto (fun e => t e * P.gamma (w e) (fun j => t e * r' e j)) l
      (𝓝 (P.coefficient r)) := by
  obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr
  obtain ⟨u, hu⟩ := (P.quotientFeasible_iff v).1 hv
  let δ : T → ℝ := fun e => weightedNorm r (r' e - r)
  have hδ : ∀ e, 0 ≤ δ e := fun e => weightedNorm_nonneg _ _
  have hrpi : Tendsto r' l (𝓝 r) := tendsto_pi_nhds.2 hrlim
  have hδlim : Tendsto δ l (𝓝 0) := by
    have h := (continuous_weightedNorm r).tendsto (0 : J₁ → ℝ)
    have hsub : Tendsto (fun e => r' e - r) l (𝓝 0) := by simpa using hrpi.sub (show Tendsto (fun _ : T => r) l (𝓝 r) from tendsto_const_nhds)
    simpa [δ, weightedNorm_zero] using h.comp hsub
  have hlower : Tendsto (fun e => P.coefficient r / (1 + δ e)) l (𝓝 (P.coefficient r)) := by
    have hc : Tendsto (fun _ : T => P.coefficient r) l (𝓝 (P.coefficient r)) := tendsto_const_nhds
    have h := hc.div (tendsto_const_nhds.add hδlim) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa using h
  have hM := tendsto_weightedNorm_weights hw hwbar u
  have hN := tendsto_weightedNorm_weights hrlim hr v
  have hupper : Tendsto (fun e => max (t e * weightedNorm (w e) u) (weightedNorm (r' e) v)) l
      (𝓝 (P.coefficient r)) := by
    have h := (htlim.mul hM).max hN
    simpa [hmin, max_eq_right (P.coefficient_nonneg r)] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hpos] with e he
    apply P.scaled_gamma_lower hr he.2.1 he.1 he.2.2 (hδ e)
    intro j
    have hc := coordinate_le_weightedNorm (x := r' e - r) hr j
    have ha := le_abs_self (r' e j - r j)
    change |r' e j - r j| ≤ δ e * r j at hc
    nlinarith
  · filter_upwards [hpos] with e he
    exact P.scaled_gamma_upper he.1 he.2.1 he.2.2 hu

/-- Eventual equality when the new coordinates have an exact common scale.
The old coordinates need only converge to positive weights. -/
theorem common_scale_exact {T : Type*} {l : Filter T}
    {w : T → J₀ → ℝ} {wbar : J₀ → ℝ} {r : J₁ → ℝ} {t : T → ℝ}
    (hwbar : ∀ j, 0 < wbar j) (hr : ∀ j, 0 < r j)
    (hw : ∀ j, Tendsto (fun e => w e j) l (𝓝 (wbar j)))
    (htlim : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ e in l, (∀ j, 0 < w e j) ∧ 0 < t e)
    (hk : 0 < P.coefficient r) :
    ∀ᶠ e in l, P.gamma (w e) (fun j => t e * r j) = P.coefficient r / t e := by
  obtain ⟨v, hv, hmin⟩ := P.coefficient_attained hr
  obtain ⟨u, hu⟩ := (P.quotientFeasible_iff v).1 hv
  have hsmall : ∀ᶠ e in l, t e * weightedNorm (w e) u < P.coefficient r := by
    have hlim := htlim.mul (tendsto_weightedNorm_weights hw hwbar u)
    apply Filter.Tendsto.eventually_lt_const hk
    simpa using hlim
  filter_upwards [hpos, hsmall] with e he hs
  apply P.reciprocal_eq_of_lift hr he.1 he.2 hu hmin
  intro j
  have hm : weightedNorm (w e) u ≤ P.coefficient r / t e :=
    (le_div_iff₀ he.2).2 (by nlinarith)
  exact (coordinate_le_weightedNorm (x := u) he.1 j).trans
    (mul_le_mul_of_nonneg_right hm (he.1 j).le)

end LinearProblem
end WeightedObstructionNorms
