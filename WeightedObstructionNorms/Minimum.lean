import WeightedObstructionNorms.WeightedNorm

noncomputable section
open Set
namespace WeightedObstructionNorms
variable {J : Type*} [Fintype J]

/-- Only used with a proved nonempty feasible set. -/
def minimum (w : J → ℝ) (s : Set (J → ℝ)) : ℝ := sInf (weightedNorm w '' s)

lemma minimum_le {w : J → ℝ} {s : Set (J → ℝ)} {x : J → ℝ} (hx : x ∈ s) :
    minimum w s ≤ weightedNorm w x := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact weightedNorm_nonneg w y
  · exact ⟨x, hx, rfl⟩

lemma le_minimum {w : J → ℝ} {s : Set (J → ℝ)} (hs : s.Nonempty) {a : ℝ}
    (ha : ∀ x ∈ s, a ≤ weightedNorm w x) : a ≤ minimum w s := by
  apply le_csInf (hs.image (weightedNorm w))
  rintro z ⟨x, hx, rfl⟩
  exact ha x hx

lemma minimum_nonneg {w : J → ℝ} {s : Set (J → ℝ)} (hs : s.Nonempty) :
    0 ≤ minimum w s := le_minimum hs (fun x _ => weightedNorm_nonneg w x)

lemma minimum_attained {w : J → ℝ} (hw : ∀ j, 0 < w j)
    {s : Set (J → ℝ)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ x ∈ s, weightedNorm w x = minimum w s := by
  obtain ⟨x, hx, hmin⟩ := exists_weightedNorm_minimum hw hs hne
  exact ⟨x, hx, le_antisymm (le_minimum hne hmin) (minimum_le hx)⟩

lemma minimum_antitone {w : J → ℝ} {s t : Set (J → ℝ)}
    (hs : s.Nonempty) (hst : s ⊆ t) : minimum w t ≤ minimum w s := by
  apply le_minimum hs
  intro x hx
  exact minimum_le (hst hx)

lemma minimum_mono_weights {w w' : J → ℝ} (hw : ∀ j, 0 < w j)
    (hww' : ∀ j, w j ≤ w' j) {s : Set (J → ℝ)} (hs : s.Nonempty) :
    minimum w' s ≤ minimum w s := by
  apply le_minimum hs
  intro x hx
  exact (minimum_le hx).trans (weightedNorm_mono_weights hw hww')

end WeightedObstructionNorms
