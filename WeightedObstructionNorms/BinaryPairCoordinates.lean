import WeightedObstructionNorms.BinaryMarginals

noncomputable section
namespace WeightedObstructionNorms
namespace BinaryPairCoordinates
open FiniteObservations BinaryMarginals BinaryExamples
variable {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j)

def encode (x : SupportState (Outcomes I) Finset.univ {i, j} → ℝ) : PairMeasure :=
  ⟨x ((fullPairEquiv i j hij).symm (1, 1)), x ((fullPairEquiv i j hij).symm (1, 0)),
    x ((fullPairEquiv i j hij).symm (0, 1)), x ((fullPairEquiv i j hij).symm (0, 0))⟩

def decode (x : PairMeasure) (z : SupportState (Outcomes I) Finset.univ {i, j}) : ℝ :=
  if (fullPairEquiv i j hij z).1 = 1 then
    if (fullPairEquiv i j hij z).2 = 1 then x.pp else x.pm
  else if (fullPairEquiv i j hij z).2 = 1 then x.mp else x.mm

@[simp] lemma decode_apply (x : PairMeasure) (b : Bit × Bit) :
    decode i j hij x ((fullPairEquiv i j hij).symm b) =
      if b.1 = 1 then if b.2 = 1 then x.pp else x.pm else if b.2 = 1 then x.mp else x.mm := by
  simp only [decode, Equiv.apply_symm_apply]

lemma encode_decode (x : PairMeasure) : encode i j hij (decode i j hij x) = x := by
  cases x
  simp [encode, decode]

lemma decode_encode (x : SupportState (Outcomes I) Finset.univ {i, j} → ℝ) :
    decode i j hij (encode i j hij x) = x := by
  funext z
  obtain ⟨⟨a, b⟩, rfl⟩ := (fullPairEquiv i j hij).symm.surjective z
  fin_cases a <;> fin_cases b <;> simp [encode, decode]

lemma box_iff (ε L : ℝ) (x : SupportState (Outcomes I) Finset.univ {i, j} → ℝ) :
    (∀ z, |x z| ≤ L * (if (fullPairEquiv i j hij z).1 = (fullPairEquiv i j hij z).2 then (2 - ε) / 4 else ε / 4)) ↔
      PairBox ε L (encode i j hij x) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [encode, mul_div_assoc] using h ((fullPairEquiv i j hij).symm (1, 1))
    · simpa [encode, mul_div_assoc] using h ((fullPairEquiv i j hij).symm (1, 0))
    · simpa [encode, mul_div_assoc] using h ((fullPairEquiv i j hij).symm (0, 1))
    · simpa [encode, mul_div_assoc] using h ((fullPairEquiv i j hij).symm (0, 0))
  · intro h z
    obtain ⟨⟨a, b⟩, rfl⟩ := (fullPairEquiv i j hij).symm.surjective z
    rcases h with ⟨hpp, hpm, hmp, hmm⟩
    fin_cases a <;> fin_cases b <;> simp only [Equiv.apply_symm_apply]
    · simpa [encode, mul_div_assoc] using hmm
    · simpa [encode, mul_div_assoc] using hmp
    · simpa [encode, mul_div_assoc] using hpm
    · simpa [encode, mul_div_assoc] using hpp

end BinaryPairCoordinates
end WeightedObstructionNorms
