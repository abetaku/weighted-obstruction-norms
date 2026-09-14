import WeightedObstructionNorms.NormedCohomology
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Projection

noncomputable section
open Set Filter
open scoped Topology
namespace WeightedObstructionNorms
namespace SlicePolytope
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A finite coordinate box intersected with a linear subspace. -/
def slice (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) : Set (J → ℝ) :=
  {x | x ∈ V ∧ ∀ j, |x j| ≤ r j}

def active (r x : J → ℝ) : J → Bool × Bool :=
  fun j => (decide (x j = -r j), decide (x j = r j))

lemma extreme_same_active (V : Submodule ℝ (J → ℝ)) (r : J → ℝ)
    {x y : J → ℝ} (hx : x ∈ (slice V r).extremePoints ℝ)
    (hy : y ∈ slice V r) (ha : active r x = active r y) : x = y := by
  have hx0 := (mem_extremePoints_iff_left.mp hx).1
  have hj (j : J) : ∀ᶠ t : ℝ in 𝓝 0, |x j + t * (x j - y j)| ≤ r j := by
    have he := congrFun ha j
    have helo : (x j = -r j) ↔ (y j = -r j) := by
      have := congrArg Prod.fst he
      simpa only [active, decide_eq_decide] using this
    have hehi : (x j = r j) ↔ (y j = r j) := by
      have := congrArg Prod.snd he
      simpa only [active, decide_eq_decide] using this
    by_cases hlo : x j = -r j
    · have hxy : x j = y j := hlo.trans (helo.mp hlo).symm
      apply Filter.Eventually.of_forall
      intro t
      simpa [hxy] using hx0.2 j
    by_cases hhi : x j = r j
    · have hxy : x j = y j := hhi.trans (hehi.mp hhi).symm
      apply Filter.Eventually.of_forall
      intro t
      simpa [hxy] using hx0.2 j
    have hb := abs_le.mp (hx0.2 j)
    have hl : -r j < x j := lt_of_le_of_ne hb.1 (Ne.symm hlo)
    have hh : x j < r j := lt_of_le_of_ne hb.2 hhi
    have hc : Tendsto (fun t : ℝ => x j + t * (x j - y j)) (𝓝 0) (𝓝 (x j)) := by
      simpa using (tendsto_const_nhds (x := x j)).add
        ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mul_const (x j - y j))
    filter_upwards [hc (Ioo_mem_nhds hl hh)] with t ht
    exact abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have hall : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j, |x j + t * (x j - y j)| ≤ r j :=
    (Filter.eventually_all.mpr hj).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, hpos⟩ := (hall.and (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0)).exists
  let z : J → ℝ := x + t • (x - y)
  have hz : z ∈ slice V r := ⟨V.add_mem hx0.1 (V.smul_mem t (V.sub_mem hx0.1 hy.1)), ht⟩
  have hd : 0 < 1 + t := by linarith
  have hsegment : x ∈ openSegment ℝ y z := by
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos hpos hd, div_pos one_pos hd, ?_, ?_⟩
    · field_simp
      ring
    · funext j
      change t / (1 + t) * y j + 1 / (1 + t) * (x j + t * (x j - y j)) = x j
      field_simp
      ring
  exact ((mem_extremePoints_iff_left.mp hx).2 y hy z hz hsegment).symm

theorem finite_extremePoints (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) :
    ((slice V r).extremePoints ℝ).Finite := by
  apply Set.Finite.of_finite_image (f := active r) (Set.toFinite _)
  intro x hx y hy ha
  exact extreme_same_active V r hx (extremePoints_subset hy) ha

lemma slice_eq_inter (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) :
    slice V r = (V : Set (J → ℝ)) ∩ Icc (-r) r := by
  ext x
  simp only [slice, mem_setOf_eq, mem_inter_iff, mem_Icc, Pi.le_def, Pi.neg_apply, abs_le, forall_and, SetLike.mem_coe]

lemma compact_slice (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) : IsCompact (slice V r) := by
  rw [slice_eq_inter]
  exact isCompact_Icc.inter_left V.closed_of_finiteDimensional

lemma convex_slice (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) : Convex ℝ (slice V r) := by
  rw [slice_eq_inter]
  exact V.convex.inter (convex_Icc _ _)

/-- A box section is the convex hull of finitely many points. -/
theorem exists_finite_convexHull (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) :
    ∃ F : Set (J → ℝ), F.Finite ∧ convexHull ℝ F = slice V r := by
  refine ⟨(slice V r).extremePoints ℝ, finite_extremePoints V r, ?_⟩
  have h := closure_convexHull_extremePoints (compact_slice V r) (convex_slice V r)
  rwa [(finite_extremePoints V r).isClosed_convexHull.closure_eq] at h

/-- A linear image of a box section is also a finite convex hull. The map
is defined only on the subspace; an auxiliary extension is eliminated. -/
theorem image_exists_finite_convexHull {H : Type*} [AddCommGroup H] [Module ℝ H]
    (V : Submodule ℝ (J → ℝ)) (r : J → ℝ) (f : V →ₗ[ℝ] H) :
    ∃ F : Set H, F.Finite ∧ convexHull ℝ F =
      {α | ∃ v : V, f v = α ∧ ∀ j, |v.val j| ≤ r j} := by
  obtain ⟨Q, hQ⟩ := V.exists_isCompl
  let g : (J → ℝ) →ₗ[ℝ] H := f.comp (V.linearProjOfIsCompl Q hQ)
  obtain ⟨F, hF, hHull⟩ := exists_finite_convexHull V r
  refine ⟨g '' F, hF.image g, ?_⟩
  rw [← g.image_convexHull, hHull]
  ext α
  constructor
  · rintro ⟨v, ⟨hv, hb⟩, rfl⟩
    refine ⟨⟨v, hv⟩, ?_, hb⟩
    dsimp [g]
    rw [V.linearProjOfIsCompl_apply_left hQ ⟨v, hv⟩]
  · rintro ⟨v, rfl, hb⟩
    refine ⟨v.val, ⟨v.property, hb⟩, ?_⟩
    dsimp [g]
    rw [V.linearProjOfIsCompl_apply_left hQ v]

end SlicePolytope
end WeightedObstructionNorms
