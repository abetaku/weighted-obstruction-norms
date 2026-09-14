import WeightedObstructionNorms.BinaryPairCoordinates
import WeightedObstructionNorms.CechReciprocal
import WeightedObstructionNorms.CechAugmentationNorm
import WeightedObstructionNorms.DiagonalCohomology

noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalSetup
open FiniteObservations BinaryMarginals
abbrev E := Outcomes (Fin 2)
def M (i : Fin 2) : Finset (Fin 2) := {i}
abbrev S : Finset (State E) := support

def stateEquiv : State E ≃ Bit × Bit where
  toFun z := (z 0,z 1)
  invFun b := ![b.1,b.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def q₀ (z : State E) : ℝ := if z 0 = z 1 then 1/2 else 0
def q₁ (_ : State E) : ℝ := 1/4
def q (ε : ℝ) : State E → ℝ := CechReciprocal.mixture E q₀ q₁ ε
lemma mem_support (z : State E) : z ∈ S ↔ z 0 = z 1 := by
  constructor
  · intro hz
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hz
    rfl
  · intro hz
    refine Finset.mem_image.mpr ⟨z 0, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact hz
lemma q₀_nonneg (z : State E) : 0 ≤ q₀ z := by unfold q₀; split <;> norm_num
lemma q₀_positive (z : State E) : 0 < q₀ z ↔ z ∈ S := by
  rw [mem_support]; unfold q₀; split <;> simp_all
lemma q₀_zero (z : State E) (hz : z ∉ S) : q₀ z = 0 := by
  simp [q₀, (mem_support z).not.mp hz]
lemma q₁_positive (z : State E) : 0 < q₁ z := by norm_num [q₁]
lemma q_positive {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (z : State E) : 0 < q ε z :=
  CechReciprocal.mixture_positive E q₀_nonneg q₁_positive hε hε₁ z
lemma q_value (ε : ℝ) (z : State E) : q ε z =
    if z 0 = z 1 then (2-ε)/4 else ε/4 := by
  unfold q CechReciprocal.mixture q₀ q₁
  split <;> ring

def globalEquiv : {z : State E // z ∈ (Finset.univ : Finset (State E))} ≃ Bit × Bit :=
  (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)).trans stateEquiv

def supportedGlobalEquiv : {z : State E // z ∈ S} ≃ Bit where
  toFun z := z.val 0
  invFun b := ⟨diagonal b,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact (mem_support z.val).1 z.property
  right_inv _ := rfl

lemma singleton_support (i : Fin 2) : projected E S {i} = projected E Finset.univ {i} := by
  ext x
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := (projected_mem E S {i} x).1 hx
    exact (projected_mem E Finset.univ {i} _).2 ⟨z, Finset.mem_univ _, rfl⟩
  · intro _
    apply (projected_mem E S {i} x).2
    refine ⟨diagonal (x ⟨i, by simp⟩), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    funext a
    have ha : a = ⟨i, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
    subst a
    rfl

end DiagonalSetup
end WeightedObstructionNorms
