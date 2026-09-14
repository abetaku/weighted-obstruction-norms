import WeightedObstructionNorms.RelativeCohomology
import WeightedObstructionNorms.NormedCohomology
import WeightedObstructionNorms.Marginal
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! The actual degree-zero marginal equations for the diagonal support.
Local entries are (first -, first +, second -, second +), old entries are
(--,++), and new entries are (+-,-+). No exactness or dimension is assumed. -/
noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalCohomology

def oldD : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun u := ![u 0, u 1, u 0, u 1]
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a u := by ext i; fin_cases i <;> rfl

def liftD : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![v 1, v 0, v 0, v 1]
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a u := by ext i; fin_cases i <;> rfl

def nextD : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) where
  toFun c := fun _ => c 0 + c 1 - c 2 - c 3
  map_add' u v := by ext i; simp only [Pi.add_apply]; ring
  map_smul' a u := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- A fully instantiated split marginal window, including proved solvability. -/
def window : RelativeWindow (Fin 2) (Fin 2) (Fin 4) (Fin 0) (Fin 1) where
  oldD := oldD
  liftD := liftD
  relativeD := 0
  nextOldD := nextD
  old_square_zero u := by ext i; simp [oldD, nextD]
  lift_closed v _ := by ext i; simp [liftD, nextD]
  full_exact c hc := by
    have h : c 0 + c 1 - c 2 - c 3 = 0 := congrFun hc 0
    refine ⟨![c 0, c 3], ![c 1 - c 3, 0], ?_, rfl⟩
    ext i
    fin_cases i <;> simp [oldD, liftD] <;> linarith

/-- Encodings of diagonal and off-diagonal support in the binary product. -/
def diagonalEmbedding (i : Fin 2) : Fin 2 × Fin 2 := (i, i)
def offDiagonalEmbedding : Fin 2 → Fin 2 × Fin 2 := ![(1, 0), (0, 1)]

/-- The concrete matrices are pushforwards of signed measures, rather than
uninterpreted matrices with merely analogous dimensions. -/
theorem old_marginals (u : Fin 2 → ℝ) :
    Marginal.push Prod.fst (Marginal.push diagonalEmbedding u) = ![oldD u 0, oldD u 1] ∧
    Marginal.push Prod.snd (Marginal.push diagonalEmbedding u) = ![oldD u 2, oldD u 3] := by
  constructor <;> rw [Marginal.push_comp] <;> ext i <;> fin_cases i <;>
    simp [Marginal.push, Fin.sum_univ_two, diagonalEmbedding, oldD]

theorem new_marginals (v : Fin 2 → ℝ) :
    Marginal.push Prod.fst (Marginal.push offDiagonalEmbedding v) = ![liftD v 0, liftD v 1] ∧
    Marginal.push Prod.snd (Marginal.push offDiagonalEmbedding v) = ![liftD v 2, liftD v 3] := by
  constructor <;> rw [Marginal.push_comp] <;> ext i <;> fin_cases i <;>
    simp [Marginal.push, Fin.sum_univ_two, offDiagonalEmbedding, liftD]

/-- Difference of the positive-state marginals. -/
def classCoordinateOnCycles : LinearMap.ker window.nextOldD →ₗ[ℝ] ℝ where
  toFun c := c.val 1 - c.val 3
  map_add' u v := by
    change (u.val 1 + v.val 1) - (u.val 3 + v.val 3) = (u.val 1 - u.val 3) + (v.val 1 - v.val 3)
    ring
  map_smul' a u := by change a * u.val 1 - a * u.val 3 = a * (u.val 1 - u.val 3); ring

lemma boundary_coordinate_zero : LinearMap.range window.boundariesToCycles ≤
    LinearMap.ker classCoordinateOnCycles := by
  rintro c ⟨u, rfl⟩
  change u 1 - u 1 = 0
  ring

def classCoordinate : window.Cohomology →ₗ[ℝ] ℝ :=
  (LinearMap.range window.boundariesToCycles).liftQ classCoordinateOnCycles boundary_coordinate_zero

lemma classCoordinate_class (c : LinearMap.ker window.nextOldD) :
    classCoordinate (window.classOf c) = c.val 1 - c.val 3 := rfl

lemma coordinate_injective : Function.Injective classCoordinate := by
  apply (LinearMap.ker_eq_bot).1
  apply le_antisymm _ bot_le
  intro α hα
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range window.boundariesToCycles) α
  have hzero : c.val 1 - c.val 3 = 0 := hα
  have hmass : c.val 0 + c.val 1 - c.val 2 - c.val 3 = 0 := congrFun c.property 0
  change (LinearMap.range window.boundariesToCycles).mkQ c = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨![c.val 0, c.val 1], ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [RelativeWindow.boundariesToCycles, window, oldD] <;> linarith

/-- The manuscript's cocycle (h,0). -/
def generator : LinearMap.ker window.nextOldD := ⟨![-1, 1, 0, 0], by
  ext i; change (-1 : ℝ) + 1 - 0 - 0 = 0; norm_num⟩

lemma generator_coordinate : classCoordinate (window.classOf generator) = 1 := by
  change (1 : ℝ) - 0 = 1
  norm_num

lemma generator_nonzero : window.classOf generator ≠ 0 := by
  intro h
  have h' := congrArg classCoordinate h
  rw [map_zero, generator_coordinate] at h'
  norm_num at h'

lemma coordinate_surjective : Function.Surjective classCoordinate := by
  intro a
  refine ⟨a • window.classOf generator, ?_⟩
  rw [map_smul, generator_coordinate]
  simp

def coordinateEquiv : window.Cohomology ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective classCoordinate ⟨coordinate_injective, coordinate_surjective⟩

/-- The obstruction group is one-dimensional. -/
theorem cohomology_dimension : Module.finrank ℝ window.Cohomology = 1 := by
  rw [coordinateEquiv.finrank_eq]
  exact Module.finrank_self ℝ

lemma connecting_coordinate (v : LinearMap.ker window.relativeD) :
    classCoordinate (window.connecting v) = v.val 0 - v.val 1 := rfl

lemma relative_constraint (v : Fin 2 → ℝ) (α : window.Cohomology) :
    v ∈ window.relativeFeasible α ↔ v 0 - v 1 = classCoordinate α := by
  constructor
  · rintro ⟨hv, h⟩
    exact congrArg classCoordinate h
  · intro h
    exact ⟨rfl, coordinate_injective h⟩

/-- The nontrivial connecting kernel in degree zero is the diagonal line. -/
theorem connecting_kernel (v : LinearMap.ker window.relativeD) :
    window.connecting v = 0 ↔ v.val 0 = v.val 1 := by
  constructor
  · intro h
    have h' := congrArg classCoordinate h
    rw [connecting_coordinate, map_zero] at h'
    exact sub_eq_zero.mp h'
  · intro h
    apply coordinate_injective
    rw [connecting_coordinate, map_zero]
    exact sub_eq_zero.mpr h

def referenceWeight : Fin 2 → ℝ := fun _ => 1 / 4
lemma referenceWeight_pos : ∀ j, 0 < referenceWeight j := by intro j; norm_num [referenceWeight]

/-- Proposition 6.1 on the actual cohomology quotient, for every class. -/
theorem obstruction_value (α : window.Cohomology) :
    window.obstructionValue referenceWeight α = 2 * |classCoordinate α| := by
  apply le_antisymm
  · let a := classCoordinate α
    let v : Fin 2 → ℝ := ![a / 2, -a / 2]
    have hv : v ∈ window.relativeFeasible α := by
      apply (relative_constraint v α).2
      dsimp [v, a]
      ring
    apply (minimum_le hv).trans
    apply (weightedNorm_le_iff referenceWeight_pos (by positivity)).2
    intro j
    fin_cases j <;> simp [v, referenceWeight, abs_div, abs_neg] <;> ring_nf <;> rfl
  · apply le_minimum (window.relativeFeasible_nonempty α)
    intro v hv
    have h := (relative_constraint v α).1 hv
    have h₀ := coordinate_le_weightedNorm (x := v) referenceWeight_pos 0
    have h₁ := coordinate_le_weightedNorm (x := v) referenceWeight_pos 1
    have habs := abs_sub (v 0) (v 1)
    rw [h] at habs
    dsimp [referenceWeight] at h₀ h₁
    linarith

theorem obstruction_generator (a : ℝ) :
    window.obstructionValue referenceWeight (a • window.classOf generator) = 2 * |a| := by
  rw [obstruction_value, map_smul, generator_coordinate]
  simp

/-- The unit ball in the class coordinate is exactly the interval [-1/2,1/2]. -/
theorem unit_ball (α : window.Cohomology) :
    window.obstructionValue referenceWeight α ≤ 1 ↔ |classCoordinate α| ≤ 1 / 2 := by
  rw [obstruction_value]
  constructor <;> intro h <;> linarith

/-- The exact primitive value for the affine mixture in the manuscript's
paragraph following Proposition 6.1, throughout 0 < ε ≤ 1. -/
theorem affine_primitive_value {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (window.problem generator).gamma (fun _ => (2 - ε) / 4)
      (fun j => ε * referenceWeight j) = 2 / ε := by
  let P := window.problem generator
  have hk : P.coefficient referenceWeight = 2 := by
    rw [← window.obstruction_eq_coefficient, obstruction_value, generator_coordinate]
    norm_num
  let u : Fin 2 → ℝ := ![-1 / 2, 1 / 2]
  let v : Fin 2 → ℝ := ![1 / 2, -1 / 2]
  have hf : P.A₀ u + P.A₁ v = P.b := by
    apply Prod.ext
    · ext i
      fin_cases i <;> norm_num [P, RelativeWindow.problem, window, oldD, liftD, u, v, generator]
    · ext i; exact Fin.elim0 i
  have hv : weightedNorm referenceWeight v = P.coefficient referenceWeight := by
    apply le_antisymm
    · rw [hk]
      apply (weightedNorm_le_iff referenceWeight_pos (by norm_num)).2
      intro j
      fin_cases j <;> norm_num [referenceWeight, v, abs_div]
    · exact minimum_le ((P.quotientFeasible_iff v).2 ⟨u, hf⟩)
  have hw : ∀ _ : Fin 2, 0 < (2 - ε) / 4 := by intro j; linarith
  have hu : ∀ j, |u j| ≤ (P.coefficient referenceWeight / ε) * ((2 - ε) / 4) := by
    rw [hk]
    have hcancel : (2 / ε) * ε = 2 := div_mul_cancel₀ _ hε.ne'
    have hnonneg : 0 ≤ 2 / ε := by positivity
    have hbound : (1 : ℝ) / 2 ≤ (2 / ε) * ((2 - ε) / 4) := by
      have hmult := mul_le_mul_of_nonneg_left hε₁ hnonneg
      nlinarith
    intro j
    fin_cases j <;> simpa [u, abs_div, abs_inv] using hbound
  simpa [hk] using P.reciprocal_eq_of_lift referenceWeight_pos hw hε hf hv hu

end DiagonalCohomology
end WeightedObstructionNorms
