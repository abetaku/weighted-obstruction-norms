import WeightedObstructionNorms.BinaryPairCoordinates
import WeightedObstructionNorms.CechReciprocal

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace WeightedObstructionNorms
namespace TriangleSetup
open FiniteObservations BinaryMarginals
abbrev E := Outcomes (Fin 3)
def M : Fin 3 → Finset (Fin 3) := ![{0, 1}, {1, 2}, {0, 2}]
abbrev S : Finset (State E) := support

def stateEquiv : State E ≃ Bit × Bit × Bit where
  toFun z := (z 0, z 1, z 2)
  invFun b := ![b.1, b.2.1, b.2.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv b := rfl

lemma sum_states (f : State E → ℝ) :
    ∑ z, f z = ∑ a : Bit, ∑ b : Bit, ∑ c : Bit, f ![a,b,c] := by
  simpa only [Fintype.sum_prod_type] using
    Fintype.sum_equiv stateEquiv f (fun b => f (stateEquiv.symm b)) (fun z => by simp)

def q₀ (z : State E) : ℝ := if z 0 = z 1 ∧ z 1 = z 2 then 1 / 2 else 0
def q₁ (_ : State E) : ℝ := 1 / 8
def q (ε : ℝ) : State E → ℝ := CechReciprocal.mixture E q₀ q₁ ε

lemma mem_support (z : State E) : z ∈ S ↔ z 0 = z 1 ∧ z 1 = z 2 := by
  constructor
  · intro hz
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨rfl, rfl⟩
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z 0, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact hz.1
    · exact hz.1.trans hz.2

lemma q₀_nonneg (z : State E) : 0 ≤ q₀ z := by unfold q₀; split <;> norm_num
lemma q₀_positive (z : State E) : 0 < q₀ z ↔ z ∈ S := by
  rw [mem_support]; unfold q₀; split <;> simp_all
lemma q₀_zero (z : State E) (hz : z ∉ S) : q₀ z = 0 := by
  simp [q₀, (mem_support z).not.mp hz]
lemma q₁_positive (z : State E) : 0 < q₁ z := by norm_num [q₁]
lemma q_positive {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (z : State E) : 0 < q ε z :=
  CechReciprocal.mixture_positive E q₀_nonneg q₁_positive hε hε₁ z

lemma pair_weight (ε : ℝ) (i j : Fin 3) (hij : i ≠ j) (b : Bit × Bit) :
    weight E (q ε) {i,j} ((fullPairEquiv i j hij).symm b).val =
      if b.1 = b.2 then (2 - ε) / 4 else ε / 4 := by
  classical
  have hv : ((fullPairEquiv i j hij).symm b).val = (pairLocalEquiv i j hij).symm b := rfl
  rw [hv]
  simp only [weight, Marginal.push]
  simp only [project_pair_eq, sum_states, Fin.sum_univ_two]
  rcases b with ⟨a,b⟩
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases a <;> fin_cases b <;> norm_num [q, CechReciprocal.mixture, q₀, q₁, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Prod.ext_iff] <;> ring

lemma pair_weight_apply (ε : ℝ) (i j : Fin 3) (hij : i ≠ j)
    (z : SupportState E Finset.univ {i,j}) :
    weight E (q ε) {i,j} z.val =
      if (fullPairEquiv i j hij z).1 = (fullPairEquiv i j hij z).2 then (2-ε)/4 else ε/4 := by
  simpa using pair_weight ε i j hij (fullPairEquiv i j hij z)

end TriangleSetup
end WeightedObstructionNorms
