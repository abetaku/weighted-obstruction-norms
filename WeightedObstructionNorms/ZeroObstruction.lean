import WeightedObstructionNorms.CommonScale
import Mathlib.Tactic.Abel

noncomputable section
open Set Filter
open scoped Topology
namespace WeightedObstructionNorms

/-- Coordinate normalization as a linear map; division by weights is total,
while norm interpretations are used only for strictly positive weights. -/
def normalizeLinear {J : Type*} (w : J → ℝ) : (J → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun x j := x j / w j
  map_add' x y := by funext j; exact add_div _ _ _
  map_smul' a x := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

namespace LinearProblem
variable {J₀ J₁ B : Type*} [Fintype J₀] [Fintype J₁]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  (P : LinearProblem J₀ J₁ B)

def oldValue (w : J₀ → ℝ) : ℝ := minimum w {u | P.A₀ u = P.b}

lemma oldValue_nonneg (w : J₀ → ℝ) (hb : P.b ∈ LinearMap.range P.A₀) :
    0 ≤ P.oldValue w := minimum_nonneg hb

lemma oldValue_attained {w : J₀ → ℝ} (hw : ∀ j, 0 < w j)
    (hb : P.b ∈ LinearMap.range P.A₀) :
    ∃ u, P.A₀ u = P.b ∧ weightedNorm w u = P.oldValue w :=
  minimum_attained hw (isClosed_eq P.A₀.continuous_of_finiteDimensional continuous_const) hb

/-- Construct a linear correction of newly available coordinates whenever
their image is already in the old-coordinate image. No inverse is assumed. -/
lemma exists_old_correction : ∃ T : (J₁ → ℝ) →ₗ[ℝ] (J₀ → ℝ),
    ∀ v, P.A₁ v ∈ LinearMap.range P.A₀ → P.A₀ (T v) = P.A₁ v := by
  obtain ⟨g, hg⟩ := P.A₀.rangeRestrict.exists_rightInverse_of_surjective P.A₀.range_rangeRestrict
  obtain ⟨p, hp⟩ := (LinearMap.range P.A₀).subtype.exists_leftInverse_of_injective
    (LinearMap.range P.A₀).ker_subtype
  refine ⟨g.comp (p.comp P.A₁), ?_⟩
  intro v hv
  let z : LinearMap.range P.A₀ := ⟨P.A₁ v, hv⟩
  have hpz := LinearMap.congr_fun hp z
  have hgz := LinearMap.congr_fun hg z
  change p (P.A₁ v) = z at hpz
  change P.A₀.rangeRestrict (g z) = z at hgz
  change P.A₀ (g (p (P.A₁ v))) = P.A₁ v
  rw [hpz]
  exact congrArg Subtype.val hgz

lemma gamma_le_old_witness {w₀ : J₀ → ℝ} {w₁ : J₁ → ℝ}
    (h₀ : ∀ j, 0 < w₀ j) (h₁ : ∀ j, 0 < w₁ j)
    {u : J₀ → ℝ} (hu : P.A₀ u = P.b) : P.gamma w₀ w₁ ≤ weightedNorm w₀ u := by
  have hfeas : Sum.elim u 0 ∈ P.fullFeasible := by
    change P.A₀ u + P.A₁ 0 = P.b
    simpa using hu
  apply (minimum_le hfeas).trans
  apply (weightedNorm_le_iff (Sum.rec h₀ h₁) (weightedNorm_nonneg _ _)).2
  intro j
  cases j with
  | inl j => exact coordinate_le_weightedNorm h₀ j
  | inr j => simpa using mul_nonneg (weightedNorm_nonneg w₀ u) (h₁ j).le

/-- A quantitative lower bound uniform over the entire feasible affine space. -/
lemma oldValue_lower_bound {wbar w₀ : J₀ → ℝ} {w₁ : J₁ → ℝ}
    (hbar : ∀ j, 0 < wbar j) (h₀ : ∀ j, 0 < w₀ j) (h₁ : ∀ j, 0 < w₁ j)
    (hb : P.b ∈ LinearMap.range P.A₀)
    (T : (J₁ → ℝ) →ₗ[ℝ] (J₀ → ℝ))
    (hT : ∀ v, P.A₁ v ∈ LinearMap.range P.A₀ → P.A₀ (T v) = P.A₁ v)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hbound : ∀ v, weightedNorm wbar (T v) ≤ C * ‖v‖)
    (hweights : ∀ j, w₀ j ≤ (1 + δ) * wbar j) :
    P.oldValue wbar / (1 + δ + C * ‖w₁‖) ≤ P.gamma w₀ w₁ := by
  obtain ⟨x, hx, hmin⟩ := P.gamma_attained h₀ h₁
  let u : J₀ → ℝ := fun j => x (.inl j)
  let v : J₁ → ℝ := fun j => x (.inr j)
  let L := weightedNorm (Sum.elim w₀ w₁) x
  have hL : 0 ≤ L := weightedNorm_nonneg _ _
  have hfeas : P.A₀ u + P.A₁ v = P.b := hx
  have hv : P.A₁ v ∈ LinearMap.range P.A₀ := by
    have h := (LinearMap.range P.A₀).sub_mem hb (LinearMap.mem_range_self P.A₀ u)
    have heq : P.b - P.A₀ u = P.A₁ v := by rw [← hfeas]; abel
    rwa [heq] at h
  have hcorrect : u + T v ∈ {y | P.A₀ y = P.b} := by
    change P.A₀ (u + T v) = P.b
    rw [map_add, hT v hv, hfeas]
  have hu : weightedNorm wbar u ≤ L * (1 + δ) := by
    apply (weightedNorm_le_iff hbar (by positivity)).2
    intro j
    have hc := coordinate_le_weightedNorm (x := x) (w := Sum.elim w₀ w₁) (Sum.rec h₀ h₁) (.inl j)
    have hm := mul_le_mul_of_nonneg_left (hweights j) hL
    dsimp [u, L] at *
    nlinarith
  have hvnorm : ‖v‖ ≤ L * ‖w₁‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg _))).2
    intro j
    have hc := coordinate_le_weightedNorm (x := x) (w := Sum.elim w₀ w₁) (Sum.rec h₀ h₁) (.inr j)
    have hwj : w₁ j ≤ ‖w₁‖ := by
      have h := norm_le_pi_norm w₁ j
      simpa [Real.norm_eq_abs, abs_of_pos (h₁ j)] using h
    have hm := mul_le_mul_of_nonneg_left hwj hL
    change |v j| ≤ L * ‖w₁‖
    dsimp [v, L] at *
    exact hc.trans hm
  have hold : P.oldValue wbar ≤ weightedNorm wbar (u + T v) := minimum_le hcorrect
  have hadd := weightedNorm_add_le (w := wbar) (x := u) (y := T v)
  have hcorr := (hbound v).trans (mul_le_mul_of_nonneg_left hvnorm hC)
  have hden : 0 < 1 + δ + C * ‖w₁‖ := by positivity
  apply (div_le_iff₀ hden).2
  change L = P.gamma w₀ w₁ at hmin
  rw [← hmin]
  nlinarith

/-- Zero-obstruction unscaled limit. New weights may vanish at unrelated
rates: only coordinatewise convergence to zero is needed. This covers the
zero branches of Theorem 3.1 and Proposition 3.4. -/
theorem zero_obstruction_limit {S : Type*} {l : Filter S}
    {w₀ : S → J₀ → ℝ} {w₁ : S → J₁ → ℝ} {wbar : J₀ → ℝ}
    (hbar : ∀ j, 0 < wbar j) (hb : P.b ∈ LinearMap.range P.A₀)
    (hlim₀ : ∀ j, Tendsto (fun e => w₀ e j) l (𝓝 (wbar j)))
    (hlim₁ : ∀ j, Tendsto (fun e => w₁ e j) l (𝓝 0))
    (hpos : ∀ᶠ e in l, (∀ j, 0 < w₀ e j) ∧ (∀ j, 0 < w₁ e j)) :
    Tendsto (fun e => P.gamma (w₀ e) (w₁ e)) l (𝓝 (P.oldValue wbar)) := by
  obtain ⟨u, hu, humin⟩ := P.oldValue_attained hbar hb
  obtain ⟨T, hT⟩ := P.exists_old_correction
  let A := LinearMap.toContinuousLinearMap ((normalizeLinear wbar).comp T)
  let C : ℝ := ‖A‖
  have hC : 0 ≤ C := norm_nonneg _
  have hbound : ∀ v, weightedNorm wbar (T v) ≤ C * ‖v‖ := fun v => A.le_opNorm v
  let δ : S → ℝ := fun e => weightedNorm wbar (w₀ e - wbar)
  have hδ : ∀ e, 0 ≤ δ e := fun e => weightedNorm_nonneg _ _
  have hpi₀ : Tendsto w₀ l (𝓝 wbar) := tendsto_pi_nhds.2 hlim₀
  have hpi₁ : Tendsto w₁ l (𝓝 0) := tendsto_pi_nhds.2 hlim₁
  have hδlim : Tendsto δ l (𝓝 0) := by
    have hs : Tendsto (fun e => w₀ e - wbar) l (𝓝 0) := by
      simpa using hpi₀.sub (show Tendsto (fun _ : S => wbar) l (𝓝 wbar) from tendsto_const_nhds)
    simpa [δ, weightedNorm_zero] using ((continuous_weightedNorm wbar).tendsto 0).comp hs
  have hden : Tendsto (fun e => 1 + δ e + C * ‖w₁ e‖) l (𝓝 1) := by
    have hn : Tendsto (fun e => ‖w₁ e‖) l (𝓝 (0 : ℝ)) := by simpa using hpi₁.norm
    have hc : Tendsto (fun _ : S => C) l (𝓝 C) := tendsto_const_nhds
    have hone : Tendsto (fun _ : S => (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
    simpa using (hone.add hδlim).add (hc.mul hn)
  have hlow : Tendsto (fun e => P.oldValue wbar / (1 + δ e + C * ‖w₁ e‖)) l
      (𝓝 (P.oldValue wbar)) := by
    have hc : Tendsto (fun _ : S => P.oldValue wbar) l (𝓝 (P.oldValue wbar)) := tendsto_const_nhds
    simpa using hc.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hupper : Tendsto (fun e => weightedNorm (w₀ e) u) l (𝓝 (P.oldValue wbar)) := by
    simpa [humin] using tendsto_weightedNorm_weights hlim₀ hbar u
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupper
  · filter_upwards [hpos] with e he
    apply P.oldValue_lower_bound hbar he.1 he.2 hb T hT hC (hδ e) hbound
    intro j
    have hc := coordinate_le_weightedNorm (x := w₀ e - wbar) hbar j
    have ha := le_abs_self (w₀ e j - wbar j)
    change |w₀ e j - wbar j| ≤ δ e * wbar j at hc
    nlinarith
  · filter_upwards [hpos] with e he
    exact P.gamma_le_old_witness he.1 he.2 hu


/-- The zero-coefficient branch of the common-scale proposition, with
exactly the normalized weight hypotheses of `common_scale_limit`. -/
theorem common_scale_zero_limit {S : Type*} {l : Filter S}
    {w : S → J₀ → ℝ} {wbar : J₀ → ℝ} {r' : S → J₁ → ℝ} {r : J₁ → ℝ}
    {t : S → ℝ}
    (hwbar : ∀ j, 0 < wbar j) (hr : ∀ j, 0 < r j)
    (hw : ∀ j, Tendsto (fun e => w e j) l (𝓝 (wbar j)))
    (hrlim : ∀ j, Tendsto (fun e => r' e j) l (𝓝 (r j)))
    (htlim : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ e in l, (∀ j, 0 < w e j) ∧ (∀ j, 0 < r' e j) ∧ 0 < t e)
    (hzero : P.coefficient r = 0) :
    Tendsto (fun e => P.gamma (w e) (fun j => t e * r' e j)) l (𝓝 (P.oldValue wbar)) := by
  apply P.zero_obstruction_limit hwbar ((P.coefficient_eq_zero_iff hr).1 hzero) hw
  · intro j
    simpa using htlim.mul (hrlim j)
  · filter_upwards [hpos] with e he
    exact ⟨he.1, fun j => mul_pos he.2.2 (he.2.1 j)⟩

/-- Exact proportionality need hold only eventually, as in the manuscript. -/
theorem common_scale_exact_eventual {S : Type*} {l : Filter S}
    {w : S → J₀ → ℝ} {wbar : J₀ → ℝ} {r : J₁ → ℝ}
    {wnew : S → J₁ → ℝ} {t : S → ℝ}
    (hwbar : ∀ j, 0 < wbar j) (hr : ∀ j, 0 < r j)
    (hw : ∀ j, Tendsto (fun e => w e j) l (𝓝 (wbar j)))
    (htlim : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ e in l, (∀ j, 0 < w e j) ∧ 0 < t e)
    (hexact : ∀ᶠ e in l, ∀ j, wnew e j = t e * r j)
    (hk : 0 < P.coefficient r) :
    ∀ᶠ e in l, P.gamma (w e) (wnew e) = P.coefficient r / t e := by
  filter_upwards [P.common_scale_exact hwbar hr hw htlim hpos hk, hexact] with e he heq
  simpa only [show wnew e = (fun j => t e * r j) from funext heq] using he

end LinearProblem
end WeightedObstructionNorms
