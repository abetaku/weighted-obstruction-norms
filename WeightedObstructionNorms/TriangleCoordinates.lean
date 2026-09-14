import WeightedObstructionNorms.TriangleSetup

noncomputable section
set_option maxHeartbeats 2000000
namespace WeightedObstructionNorms
namespace TriangleCoordinates
open FiniteObservations BinaryMarginals TriangleSetup CechLowDegrees CechLowComparison

def encode (x : C0 E Finset.univ M) : BinaryExamples.TriangleMeasure :=
  ⟨BinaryPairCoordinates.encode 0 1 (by decide) (x 0),
   BinaryPairCoordinates.encode 1 2 (by decide) (x 1),
   BinaryPairCoordinates.encode 0 2 (by decide) (x 2)⟩

def decode (x : BinaryExamples.TriangleMeasure) : C0 E Finset.univ M :=
  fun i => Fin.cases (BinaryPairCoordinates.decode (0 : Fin 3) 1 (by decide) x.x12)
    (Fin.cases (BinaryPairCoordinates.decode (1 : Fin 3) 2 (by decide) x.x23)
      (Fin.cases (BinaryPairCoordinates.decode (0 : Fin 3) 2 (by decide) x.x13)
        (fun k => Fin.elim0 k))) i

lemma encode_decode (x : BinaryExamples.TriangleMeasure) : encode (decode x) = x := by
  cases x with
  | mk x12 x23 x13 =>
    exact congrArg₂ (fun a bc => BinaryExamples.TriangleMeasure.mk a bc.1 bc.2)
      (BinaryPairCoordinates.encode_decode (0 : Fin 3) 1 (by decide) x12)
      (congrArg₂ Prod.mk (BinaryPairCoordinates.encode_decode (1 : Fin 3) 2 (by decide) x23)
      (BinaryPairCoordinates.encode_decode (0 : Fin 3) 2 (by decide) x13))
lemma decode_encode (x : C0 E Finset.univ M) : decode (encode x) = x := by
  funext i
  fin_cases i
  · exact BinaryPairCoordinates.decode_encode (0 : Fin 3) 1 (by decide) (x 0)
  · exact BinaryPairCoordinates.decode_encode (1 : Fin 3) 2 (by decide) (x 1)
  · exact BinaryPairCoordinates.decode_encode (0 : Fin 3) 2 (by decide) (x 2)

@[simp] lemma decode_zero (x : BinaryExamples.TriangleMeasure) :
    decode x 0 = BinaryPairCoordinates.decode (0 : Fin 3) 1 (by decide) x.x12 := rfl
@[simp] lemma decode_one (x : BinaryExamples.TriangleMeasure) :
    decode x 1 = BinaryPairCoordinates.decode (1 : Fin 3) 2 (by decide) x.x23 := rfl
@[simp] lemma decode_two (x : BinaryExamples.TriangleMeasure) :
    decode x 2 = BinaryPairCoordinates.decode (0 : Fin 3) 2 (by decide) x.x13 := rfl

def edge : Fin 3 → Pair (K := Fin 3) :=
  ![⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(1,2), by decide⟩]
def vertex : Fin 3 → Fin 3 := ![1,0,2]
lemma edge_surjective : Function.Surjective edge := by
  rintro ⟨⟨i,j⟩,h⟩
  fin_cases i <;> fin_cases j <;> try (exfalso; exact (by decide : ¬ _) h)
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
lemma edge_observation (k : Fin 3) : pairObservation M (edge k) = {vertex k} := by
  fin_cases k <;> decide

def eval (x : C1 E Finset.univ M) (k : Fin 3) (a : Bit) : ℝ :=
  coefficientCongr E Finset.univ (edge_observation k) (x (edge k))
    ((fullSingletonEquiv (vertex k)).symm a)

lemma eval_injective : Function.Injective eval := by
  intro x y h
  funext p
  obtain ⟨k,rfl⟩ := edge_surjective p
  apply (coefficientCongr E Finset.univ (edge_observation k)).injective
  funext z
  obtain ⟨a,rfl⟩ := (fullSingletonEquiv (vertex k)).symm.surjective z
  exact congrFun (congrFun h k) a


lemma eval_d0_zero (x : C0 E Finset.univ M) (a : Bit) :
    eval (d0 E Finset.univ M x) 0 a =
      x 1 ((fullPairEquiv 1 2 (by decide)).symm (a,0)) +
      x 1 ((fullPairEquiv 1 2 (by decide)).symm (a,1)) -
      (x 0 ((fullPairEquiv 0 1 (by decide)).symm (0,a)) +
      x 0 ((fullPairEquiv 0 1 (by decide)).symm (1,a))) := by
  have hl := BinaryMarginals.cast_marginal (edge_observation 0)
    (Finset.inter_subset_right (s₁ := M 0)) (show {1} ⊆ {1,2} by decide) (x 1)
  have hr := BinaryMarginals.cast_marginal (edge_observation 0)
    (Finset.inter_subset_left (s₂ := M 1)) (show {1} ⊆ {0,1} by decide) (x 0)
  have hle := (congrFun hl ((fullSingletonEquiv 1).symm a)).trans (full_pair_first 1 2 (by decide) (x 1) a)
  have hre := (congrFun hr ((fullSingletonEquiv 1).symm a)).trans (full_pair_second 0 1 (by decide) (x 0) a)
  unfold eval
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub, Pi.sub_apply]
  exact congrArg₂ (fun a b : ℝ => a - b) hle hre

lemma eval_d0_one (x : C0 E Finset.univ M) (a : Bit) :
    eval (d0 E Finset.univ M x) 1 a =
      x 2 ((fullPairEquiv 0 2 (by decide)).symm (a,0)) +
      x 2 ((fullPairEquiv 0 2 (by decide)).symm (a,1)) -
      (x 0 ((fullPairEquiv 0 1 (by decide)).symm (a,0)) +
      x 0 ((fullPairEquiv 0 1 (by decide)).symm (a,1))) := by
  have hl := BinaryMarginals.cast_marginal (edge_observation 1)
    (Finset.inter_subset_right (s₁ := M 0)) (show {0} ⊆ {0,2} by decide) (x 2)
  have hr := BinaryMarginals.cast_marginal (edge_observation 1)
    (Finset.inter_subset_left (s₂ := M 2)) (show {0} ⊆ {0,1} by decide) (x 0)
  have hle := (congrFun hl ((fullSingletonEquiv 0).symm a)).trans (full_pair_first 0 2 (by decide) (x 2) a)
  have hre := (congrFun hr ((fullSingletonEquiv 0).symm a)).trans (full_pair_first 0 1 (by decide) (x 0) a)
  unfold eval
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub, Pi.sub_apply]
  exact congrArg₂ (fun a b : ℝ => a - b) hle hre

lemma eval_d0_two (x : C0 E Finset.univ M) (a : Bit) :
    eval (d0 E Finset.univ M x) 2 a =
      x 2 ((fullPairEquiv 0 2 (by decide)).symm (0,a)) +
      x 2 ((fullPairEquiv 0 2 (by decide)).symm (1,a)) -
      (x 1 ((fullPairEquiv 1 2 (by decide)).symm (0,a)) +
      x 1 ((fullPairEquiv 1 2 (by decide)).symm (1,a))) := by
  have hl := BinaryMarginals.cast_marginal (edge_observation 2)
    (Finset.inter_subset_right (s₁ := M 1)) (show {2} ⊆ {0,2} by decide) (x 2)
  have hr := BinaryMarginals.cast_marginal (edge_observation 2)
    (Finset.inter_subset_left (s₂ := M 2)) (show {2} ⊆ {1,2} by decide) (x 1)
  have hle := (congrFun hl ((fullSingletonEquiv 2).symm a)).trans (full_pair_second 0 2 (by decide) (x 2) a)
  have hre := (congrFun hr ((fullSingletonEquiv 2).symm a)).trans (full_pair_second 1 2 (by decide) (x 1) a)
  unfold eval
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub, Pi.sub_apply]
  exact congrArg₂ (fun a b : ℝ => a - b) hle hre

lemma box_iff (ε L : ℝ) (x : C0 E Finset.univ M) :
    (∀ i z, |x i z| ≤ L * weight E (q ε) (M i) z.val) ↔
      BinaryExamples.TriangleBox ε L (encode x) := by
  change _ ↔ BinaryExamples.PairBox ε L (BinaryPairCoordinates.encode 0 1 (by decide) (x 0)) ∧
    BinaryExamples.PairBox ε L (BinaryPairCoordinates.encode 1 2 (by decide) (x 1)) ∧
    BinaryExamples.PairBox ε L (BinaryPairCoordinates.encode 0 2 (by decide) (x 2))
  simp only [← BinaryPairCoordinates.box_iff, ← pair_weight_apply]
  constructor
  · intro h; exact ⟨h 0,h 1,h 2⟩
  · rintro ⟨h0,h1,h2⟩ i; fin_cases i
    · exact h0
    · exact h1
    · exact h2

end TriangleCoordinates
end WeightedObstructionNorms
