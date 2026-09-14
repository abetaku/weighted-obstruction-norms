import WeightedObstructionNorms.NormedCohomology

noncomputable section
namespace WeightedObstructionNorms

/-- A map between split windows. The correction term permits a new source
coordinate to become an old target coordinate under support enlargement.
No induced map on cohomology or norm inequality is assumed. -/
structure WindowMap
    {U X V Y Z U' X' V' Y' Z' : Type*}
    [Fintype U] [Fintype X] [Fintype V] [Fintype Y] [Fintype Z]
    [Fintype U'] [Fintype X'] [Fintype V'] [Fintype Y'] [Fintype Z']
    (W : RelativeWindow U X V Y Z) (W' : RelativeWindow U' X' V' Y' Z') where
  oldMap : (U → ℝ) →ₗ[ℝ] (U' → ℝ)
  newMap : (X → ℝ) →ₗ[ℝ] (X' → ℝ)
  cochainMap : (V → ℝ) →ₗ[ℝ] (V' → ℝ)
  correction : (X → ℝ) →ₗ[ℝ] (U' → ℝ)
  old_comm : ∀ u, cochainMap (W.oldD u) = W'.oldD (oldMap u)
  closed : ∀ c, W.nextOldD c = 0 → W'.nextOldD (cochainMap c) = 0
  new_closed : ∀ v, W.relativeD v = 0 → W'.relativeD (newMap v) = 0
  lift_comm : ∀ v, W.relativeD v = 0 →
    cochainMap (W.liftD v) = W'.oldD (correction v) + W'.liftD (newMap v)

namespace WindowMap
variable {U X V Y Z U' X' V' Y' Z' U'' X'' V'' Y'' Z'' : Type*}
    [Fintype U] [Fintype X] [Fintype V] [Fintype Y] [Fintype Z]
    [Fintype U'] [Fintype X'] [Fintype V'] [Fintype Y'] [Fintype Z']
    [Fintype U''] [Fintype X''] [Fintype V''] [Fintype Y''] [Fintype Z'']
    {W : RelativeWindow U X V Y Z} {W' : RelativeWindow U' X' V' Y' Z'}
    {W'' : RelativeWindow U'' X'' V'' Y'' Z''}

def cycleMap (F : WindowMap W W') : LinearMap.ker W.nextOldD →ₗ[ℝ] LinearMap.ker W'.nextOldD :=
  (F.cochainMap.domRestrict _).codRestrict _ (fun c => F.closed c c.property)

lemma boundaries_map (F : WindowMap W W') : LinearMap.range W.boundariesToCycles ≤
    LinearMap.ker ((LinearMap.range W'.boundariesToCycles).mkQ.comp F.cycleMap) := by
  rintro c ⟨u, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨F.oldMap u, Subtype.ext (F.old_comm u).symm⟩

/-- The actual map induced on the quotient of old cocycles by boundaries. -/
def cohomologyMap (F : WindowMap W W') : W.Cohomology →ₗ[ℝ] W'.Cohomology :=
  (LinearMap.range W.boundariesToCycles).liftQ
    ((LinearMap.range W'.boundariesToCycles).mkQ.comp F.cycleMap) F.boundaries_map

lemma cohomologyMap_class (F : WindowMap W W') (c : LinearMap.ker W.nextOldD) :
    F.cohomologyMap (W.classOf c) = W'.classOf (F.cycleMap c) := rfl

def relativeCycleMap (F : WindowMap W W') :
    LinearMap.ker W.relativeD →ₗ[ℝ] LinearMap.ker W'.relativeD :=
  (F.newMap.domRestrict _).codRestrict _ (fun v => F.new_closed v v.property)

/-- Naturality of the connecting map, including the old-coordinate correction. -/
theorem connecting_naturality (F : WindowMap W W') (v : LinearMap.ker W.relativeD) :
    F.cohomologyMap (W.connecting v) = W'.connecting (F.relativeCycleMap v) := by
  change W'.classOf (F.cycleMap (W.liftToCycles v)) =
    W'.classOf (W'.liftToCycles (F.relativeCycleMap v))
  apply (W'.classOf_eq_iff _ _).2
  refine ⟨F.correction v, ?_⟩
  change W'.oldD (F.correction v) = F.cochainMap (W.liftD v) - W'.liftD (F.newMap v)
  rw [F.lift_comm v v.property]
  abel

lemma maps_feasible (F : WindowMap W W') {α : W.Cohomology} {v : X → ℝ}
    (hv : v ∈ W.relativeFeasible α) : F.newMap v ∈ W'.relativeFeasible (F.cohomologyMap α) := by
  obtain ⟨hv, hα⟩ := hv
  refine ⟨F.new_closed v hv, ?_⟩
  exact (F.connecting_naturality ⟨v, hv⟩).symm.trans (congrArg F.cohomologyMap hα)

/-- Nonexpansion is deduced from the coordinate estimate, not assumed on classes. -/
theorem obstruction_nonexpansive (F : WindowMap W W') {r : X → ℝ} {r' : X' → ℝ}
    (hr : ∀ j, 0 < r j)
    (hbound : ∀ v, weightedNorm r' (F.newMap v) ≤ weightedNorm r v) (α : W.Cohomology) :
    W'.obstructionValue r' (F.cohomologyMap α) ≤ W.obstructionValue r α := by
  obtain ⟨v, hv, hmin⟩ := W.obstruction_attained hr α
  exact (minimum_le (F.maps_feasible hv)).trans ((hbound v).trans_eq hmin)

/-- Bundling the resulting map as an actual continuous linear contraction. -/
def normedMap (F : WindowMap W W') {r : X → ℝ} {r' : X' → ℝ}
    (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j)
    (hbound : ∀ v, weightedNorm r' (F.newMap v) ≤ weightedNorm r v) :
    W.NormedCohomology r hr →L[ℝ] W'.NormedCohomology r' hr' :=
  (show W.NormedCohomology r hr →ₗ[ℝ] W'.NormedCohomology r' hr' from F.cohomologyMap).mkContinuous 1
    (by intro α; simpa using F.obstruction_nonexpansive hr hbound α)

lemma normedMap_norm_le_one (F : WindowMap W W') {r : X → ℝ} {r' : X' → ℝ}
    (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j)
    (hbound : ∀ v, weightedNorm r' (F.newMap v) ≤ weightedNorm r v) :
    ‖F.normedMap hr hr' hbound‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro α
  simpa using F.obstruction_nonexpansive hr hbound α

def identity (W : RelativeWindow U X V Y Z) : WindowMap W W where
  oldMap := LinearMap.id
  newMap := LinearMap.id
  cochainMap := LinearMap.id
  correction := 0
  old_comm _ := rfl
  closed _ h := h
  new_closed _ h := h
  lift_comm v _ := by simp

/-- Composition includes both ways that new mass becomes old mass. -/
def comp (G : WindowMap W' W'') (F : WindowMap W W') : WindowMap W W'' where
  oldMap := G.oldMap.comp F.oldMap
  newMap := G.newMap.comp F.newMap
  cochainMap := G.cochainMap.comp F.cochainMap
  correction := G.oldMap.comp F.correction + G.correction.comp F.newMap
  old_comm u := by simp only [LinearMap.comp_apply, F.old_comm, G.old_comm]
  closed c hc := G.closed _ (F.closed c hc)
  new_closed v hv := G.new_closed _ (F.new_closed v hv)
  lift_comm v hv := by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, F.lift_comm v hv, map_add,
      G.old_comm, G.lift_comm _ (F.new_closed v hv)]
    abel

lemma cohomologyMap_identity (α : W.Cohomology) : (identity W).cohomologyMap α = α := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range W.boundariesToCycles) α
  rfl

lemma cohomologyMap_comp (G : WindowMap W' W'') (F : WindowMap W W') (α : W.Cohomology) :
    (G.comp F).cohomologyMap α = G.cohomologyMap (F.cohomologyMap α) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range W.boundariesToCycles) α
  rfl

/-- The degree-p part of a cochain homotopy on old cocycles. -/
theorem cohomologyMap_eq_of_homotopy (F G : WindowMap W W')
    (H : (V → ℝ) →ₗ[ℝ] (U' → ℝ))
    (hH : ∀ c, W.nextOldD c = 0 → G.cochainMap c - F.cochainMap c = W'.oldD (H c)) :
    F.cohomologyMap = G.cohomologyMap := by
  apply LinearMap.ext
  intro α
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range W.boundariesToCycles) α
  change W'.classOf (F.cycleMap c) = W'.classOf (G.cycleMap c)
  symm
  exact (W'.classOf_eq_iff _ _).2 ⟨H c, (hH c c.property).symm⟩

/-- Inverse maps on cohomology are isometric when both coordinate maps contract. -/
theorem obstruction_eq_of_inverse (F : WindowMap W W') (G : WindowMap W' W)
    {r : X → ℝ} {r' : X' → ℝ} (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j)
    (hF : ∀ v, weightedNorm r' (F.newMap v) ≤ weightedNorm r v)
    (hG : ∀ v, weightedNorm r (G.newMap v) ≤ weightedNorm r' v)
    (hGF : ∀ α, G.cohomologyMap (F.cohomologyMap α) = α) (α : W.Cohomology) :
    W'.obstructionValue r' (F.cohomologyMap α) = W.obstructionValue r α := by
  apply le_antisymm (F.obstruction_nonexpansive hr hF α)
  simpa [hGF] using G.obstruction_nonexpansive hr' hG (F.cohomologyMap α)

/-- A bundled linear isometric equivalence, once the two homotopy inverse
identities have been established by the concrete observation construction. -/
def isometryOfInverse (F : WindowMap W W') (G : WindowMap W' W)
    {r : X → ℝ} {r' : X' → ℝ} (hr : ∀ j, 0 < r j) (hr' : ∀ j, 0 < r' j)
    (hF : ∀ v, weightedNorm r' (F.newMap v) ≤ weightedNorm r v)
    (hG : ∀ v, weightedNorm r (G.newMap v) ≤ weightedNorm r' v)
    (hGF : ∀ α, G.cohomologyMap (F.cohomologyMap α) = α)
    (hFG : ∀ β, F.cohomologyMap (G.cohomologyMap β) = β) :
    W.NormedCohomology r hr ≃ₗᵢ[ℝ] W'.NormedCohomology r' hr' where
  toLinearEquiv :=
    { F.cohomologyMap with
      invFun := G.cohomologyMap
      left_inv := hGF
      right_inv := hFG }
  norm_map' := F.obstruction_eq_of_inverse G hr hr' hF hG hGF

end WindowMap
end WeightedObstructionNorms
