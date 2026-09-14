import WeightedObstructionNorms.DiagonalCocycle

noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalCost
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees DiagonalCoordinates DiagonalCocycle

lemma pair_lower {ε L : ℝ} (hε : 0 < ε) (y : BinaryExamples.PairMeasure)
    (hy : Feasible y) (hb : BinaryExamples.PairBox ε L y) : 2/ε ≤ L := by
  have hpm := le_trans (le_abs_self y.pm) hb.2.1
  have hmp := le_trans (neg_le_abs y.mp) hb.2.2.1
  rw [div_le_iff₀ hε]
  rcases hy with ⟨h1,h2,h3,h4⟩
  nlinarith

lemma primitive_feasible : Feasible primitiveMeasure := by norm_num [Feasible, primitiveMeasure]
lemma primitive_box {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    BinaryExamples.PairBox ε (2/ε) primitiveMeasure := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have ho : (2/ε)*ε/4 = (1/2 : ℝ) := by field_simp; ring
  have hd : (1/2 : ℝ) ≤ (2/ε)*(2-ε)/4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have he : 2/ε*(2-ε) = 2*(2-ε)/ε := by ring
    rw [he, le_div_iff₀ hε]
    nlinarith
  change |(1/2 : ℝ)| ≤ _ ∧ |(1/2 : ℝ)| ≤ _ ∧ |(-1/2 : ℝ)| ≤ _ ∧ |(-1/2 : ℝ)| ≤ _
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1/2), abs_div, abs_neg, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact ⟨hd,le_of_eq ho.symm,le_of_eq ho.symm,hd⟩

lemma norm_box_iff {ε L : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hL : 0 ≤ L) (u : Global) :
    cochainNorm E Finset.univ M (q ε) 0 (augmentationEquiv E Finset.univ M u) ≤ L ↔
      BinaryExamples.PairBox ε L (encode u) :=
  (CechAugmentationNorm.norm_box_iff E M (diagonal 0) (q_positive hε hε₁) u hL).trans (box_iff ε L u)

lemma witness_bound {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    cochainNorm E Finset.univ M (q ε) 0 witness ≤ 2/ε := by
  apply (norm_box_iff hε hε₁ (by positivity) (decode primitiveMeasure)).2
  rw [encode_decode]
  exact primitive_box hε hε₁

lemma feasible_lower {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (x : Cochain E Finset.univ M 0)
    (hx : differential E Finset.univ M 0 x = extension E S M (Finset.subset_univ S) 1 c) :
    2/ε ≤ cochainNorm E Finset.univ M (q ε) 0 x := by
  obtain ⟨u,rfl⟩ := (augmentationEquiv E Finset.univ M).surjective x
  exact pair_lower hε (encode u) ((feasible_iff u).1 hx)
    ((norm_box_iff hε hε₁ (cochainNorm_nonneg E Finset.univ M (q ε) 0 _) u).1 le_rfl)

/-- The primitive cost in the actual degree-zero Cech example. -/
theorem cost_eq {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) : CechPrimitive.cost E S M (q ε) 0 c = 2/ε := by
  have hx : differential E Finset.univ M 0 witness = extension E S M (Finset.subset_univ S) 1 c := extension_c.symm
  unfold CechPrimitive.cost
  apply le_antisymm
  · exact le_trans (csInf_le ⟨0, by rintro r ⟨y,hy,rfl⟩; exact cochainNorm_nonneg E Finset.univ M (q ε) 0 y⟩
      ⟨witness,hx,rfl⟩) (witness_bound hε hε₁)
  · refine le_csInf ?_ ?_
    · exact ⟨_,⟨witness,hx,rfl⟩⟩
    rintro r ⟨y,hy,rfl⟩
    exact feasible_lower hε hε₁ y hy

end DiagonalCost
end WeightedObstructionNorms
