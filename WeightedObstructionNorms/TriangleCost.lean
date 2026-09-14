import WeightedObstructionNorms.TriangleCocycle

noncomputable section
namespace WeightedObstructionNorms
namespace TriangleCost
open FiniteObservations BinaryMarginals TriangleSetup CechAllDegrees CechLowComparison
open TriangleCoordinates TriangleCocycle

lemma norm_box_iff {ε L : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hL : 0 ≤ L)
    (x : Cochain E Finset.univ M 1) :
    cochainNorm E Finset.univ M (q ε) 1 x ≤ L ↔
      BinaryExamples.TriangleBox ε L (encode (degreeZero E Finset.univ M x)) := by
  exact (cochain_box_iff E Finset.univ M (diagonal 0) (q_positive hε hε₁)
    oneEquiv M (one_observation M) x hL).trans (box_iff ε L _)

lemma feasible_threshold {ε L : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hL : 0 ≤ L) :
    (∃ x : Cochain E Finset.univ M 1,
      differential E Finset.univ M 1 x = extension E S M (Finset.subset_univ S) 2 c ∧
      cochainNorm E Finset.univ M (q ε) 1 x ≤ L) ↔ max 1 (2 / (3*ε)) ≤ L := by
  rw [← BinaryExamples.triangle_full_threshold hε hε₁]
  constructor
  · rintro ⟨x,hx,hb⟩
    exact ⟨encode (degreeZero E Finset.univ M x), (feasible_iff x).1 hx,
      (norm_box_iff hε hε₁ hL x).1 hb⟩
  · rintro ⟨y,hy,hb⟩
    let x := (degreeZero E Finset.univ M).symm (decode y)
    have he : encode (degreeZero E Finset.univ M x) = y := by
      simp only [x, LinearEquiv.apply_symm_apply, encode_decode]
    refine ⟨x,(feasible_iff x).2 ?_,(norm_box_iff hε hε₁ hL x).2 ?_⟩
    · rwa [he]
    · rwa [he]

/-- Proposition 6.2 for the actual all-degree marginal Cech differential and norm. -/
theorem cost_eq {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    CechPrimitive.cost E S M (q ε) 1 c = max 1 (2 / (3*ε)) := by
  let L := max 1 (2 / (3*ε))
  have hL : 0 ≤ L := le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨x,hx,hxn⟩ := (feasible_threshold hε hε₁ hL).2 le_rfl
  unfold CechPrimitive.cost
  apply le_antisymm
  · exact le_trans (csInf_le ⟨0, by rintro r ⟨y,hy,rfl⟩; exact cochainNorm_nonneg E Finset.univ M (q ε) 1 y⟩
      ⟨x,hx,rfl⟩) hxn
  · refine le_csInf ?_ ?_
    · exact ⟨_,⟨x,hx,rfl⟩⟩
    rintro r ⟨y,hy,rfl⟩
    exact (feasible_threshold hε hε₁ (cochainNorm_nonneg E Finset.univ M (q ε) 1 y)).1 ⟨y,hy,le_rfl⟩

end TriangleCost
end WeightedObstructionNorms
