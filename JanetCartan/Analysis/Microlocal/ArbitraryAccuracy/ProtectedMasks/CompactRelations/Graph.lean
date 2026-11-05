module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations.Carrier

/-!
# Compact graphs of the actual masked relations

The original zero-energy source is reconstructed from its root state. Both
orientations are continuous images of the same closed accepted carrier. A finite
union in the actual chart family then gives the physical direct relation required
by the nesting construction in `app:ch_regular:lem:finite-chain`.

The hypotheses concern the same roots and flows supplied by
`UniformGeometry/Construction` and `UniformGeometry/RootFlow`. Root continuity is
restricted to the original domain containing the selected compact buffers; no
global extension or compact coefficient class is assumed. The parent must select
these buffers and the common elapsed bound for its actual finite family.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic EvolutionIntegratedLocalization
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}

/-- The original source and target are precisely the two zero-energy lifts
of an accepted initial-state/time pair, in either orientation
(`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_iff_accepted
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ) (backward : Bool)
    (a b : Euclidean (d + 1) × Euclidean (d + 1)) :
    maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward a b ↔
      ∃ vr ∈ acceptedRootTimeCarrier e Φ U K W χsource χout Δ,
        originalSource backward a b = rootSuspensionState h 0 vr.1 ∧
        originalTarget backward a b = rootSuspensionState h 0 (Φ vr) := by
  have hrel (r : ℝ) : zeroEnergyFlowRelation backward h Φ r a b ↔
      rootSuspension h (originalSource backward a b) = 0 ∧
      originalTarget backward a b =
        rootSuspensionState h 0 (Φ (spacetimeRootState (originalSource backward a b), r)) := by
    cases backward <;> rfl
  constructor
  · rintro ⟨r, hr, hc, hs, ht, hf⟩
    obtain ⟨he, hf⟩ := (hrel r).1 hf
    have ha := rootSuspensionState_eq_of_zero_energy h _ he
    refine ⟨(spacetimeRootState (originalSource backward a b), r), ?_, ha.symm, hf⟩
    rw [mem_acceptedRootTimeCarrier_iff e h]
    exact ⟨hr, by simpa only [ha] using hc, by simpa only [ha] using hs,
      by simpa only [hf] using ht⟩
  · rintro ⟨vr, hv, ha, hb⟩
    obtain ⟨hr, hc, hs, ht⟩ := (mem_acceptedRootTimeCarrier_iff e h Φ U K W
      χsource χout Δ vr).1 hv
    refine ⟨vr.2, hr, ?_, ?_, ?_, (hrel vr.2).2 ?_⟩
    · simpa only [ha] using hc
    · simpa only [ha] using hs
    · simpa only [hb] using ht
    · rw [ha, spacetimeRootState_rootSuspensionState, rootSuspension_rootSuspensionState]
      exact ⟨rfl, hb⟩

/-- The endpoint map swaps the same forward endpoints for the literal adjoint.
Consumer: the compact continuous image of the accepted carrier
(`app:ch_regular:lem:finite-chain`). -/
def orientedRootEndpoints
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (backward : Bool) (vr : RootState (Euclidean d) × ℝ) :=
  if backward then (rootSuspensionState h 0 (Φ vr), rootSuspensionState h 0 vr.1)
  else (rootSuspensionState h 0 vr.1, rootSuspensionState h 0 (Φ vr))

/-- Exact image description of the graph, retaining both mask supports and
the original elapsed bound (`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_graph_eq_image
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ) (backward : Bool) :
    {ab : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) | maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward ab.1 ab.2} =
      orientedRootEndpoints h Φ backward '' acceptedRootTimeCarrier e Φ U K W χsource χout Δ := by
  ext ab
  rw [mem_ofPred_eq, maskedZeroEnergyRelation_iff_accepted]
  cases backward <;>
    simp only [originalSource, originalTarget, orientedRootEndpoints, Bool.false_eq_true,
      ↓reduceIte, mem_image, Prod.exists] <;>
    aesop

/-- Suspension is continuous on the original root domain; it needs no
extension outside that domain (`app:ch_regular:lem:finite-chain`). -/
theorem continuousOn_zeroRootSuspensionState
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hh : ContinuousOn h D) : ContinuousOn (rootSuspensionState h 0) D := by
  unfold rootSuspensionState
  simpa only [zero_add, Function.comp_apply, timeSpacePointCLM_apply] using
    (timeSpacePointCLM.continuous.comp_continuousOn
      (continuous_fst.continuousOn.prodMk continuous_snd.fst.continuousOn)).prodMk
    (timeSpacePointCLM.continuous.comp_continuousOn
      (hh.prodMk continuous_snd.snd.continuousOn))

/-- Each oriented graph is compact, as the continuous image of its closed
accepted carrier. Compact buffers must be selected inside the same root domain
used by the actual flow (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_maskedZeroEnergyRelation
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K D : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    (χsource χout : Euclidean (d + 1) → ℂ) (Δ : ℝ) (backward : Bool)
    (hU : IsCompact U) (hK : IsCompact K) (hW : IsClosed W)
    (hUD : U ⊆ D) (hKD : K ⊆ D) (hh : ContinuousOn h D)
    (hΦ : ContinuousOn Φ (U ×ˢ Icc 0 Δ)) :
    IsCompact {ab : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) | maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward ab.1 ab.2} := by
  rw [maskedZeroEnergyRelation_graph_eq_image]
  apply (isCompact_acceptedRootTimeCarrier e χsource χout Δ hU hK hW hΦ).image_of_continuousOn
  have hsub : acceptedRootTimeCarrier e Φ U K W χsource χout Δ ⊆ U ×ˢ Icc 0 Δ :=
    fun _ hv ↦ hv.1
  have hc := continuousOn_zeroRootSuspensionState hh
  have hsource : ContinuousOn (fun vr : RootState (Euclidean d) × ℝ ↦
      rootSuspensionState h 0 vr.1) (acceptedRootTimeCarrier e Φ U K W χsource χout Δ) :=
    hc.comp continuous_fst.continuousOn (fun _ hv ↦ hUD hv.1.1)
  have hout : ContinuousOn (fun vr ↦ rootSuspensionState h 0 (Φ vr))
      (acceptedRootTimeCarrier e Φ U K W χsource χout Δ) :=
    hc.comp (hΦ.mono hsub) (fun vr hv ↦ hKD (by
      simpa only [one_mul] using (hv.2.1 1 (by simp)).1))
  cases backward
  · exact hsource.prodMk hout
  · exact hout.prodMk hsource

/-- The literal physical coordinate conversion is continuous on all phase
space (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_adaptedPhysicalPhaseState
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)) :
    Continuous (adaptedPhysicalPhaseState e) := by
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous
  exact (e.symm.continuous.comp
    ((ht.comp continuous_fst).prodMk (spatialPartCLM.continuous.comp continuous_fst))).prodMk
    (e.symm.continuous.comp
      ((ht.comp continuous_snd).prodMk (spatialPartCLM.continuous.comp continuous_snd)))

/-- A finite family of actual charts gives a compact physical direct relation.
This is the precise compact-graph input of the nested proof-mask construction;
it includes both orientations and excludes the full diagonal
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_physicalDirectRelation {J : Type*} [Finite J]
    (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hU : ∀ j, IsCompact (U j)) (hK : ∀ j, IsCompact (K j)) (hW : IsClosed W)
    (hUD : ∀ j, U j ⊆ D j) (hKD : ∀ j, K j ⊆ D j)
    (hh : ∀ j, ContinuousOn (h j) (D j))
    (hΦ : ∀ j, ContinuousOn (Φ j) (U j ×ˢ Icc 0 Δ)) :
    IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) | physicalDirectRelation i h Φ U K W χsource χout Δ pq.1 pq.2} := by
  let G := fun j backward ↦
    (fun ab : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) ↦ (adaptedPhysicalPhaseState (coordinateSplit (i j)) ab.1,
      adaptedPhysicalPhaseState (coordinateSplit (i j)) ab.2)) ''
    {ab : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) | maskedZeroEnergyRelation (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W
      (χsource j) (χout j) Δ backward ab.1 ab.2}
  have heq : {pq : (Euclidean (d + 1) × Euclidean (d + 1)) × (Euclidean (d + 1) × Euclidean (d + 1)) | physicalDirectRelation i h Φ U K W χsource χout Δ pq.1 pq.2} =
      ⋃ j, ⋃ backward, G j backward := by
    ext pq
    simp only [physicalDirectRelation, mem_ofPred_eq, mem_iUnion, G, mem_image]
    constructor
    · rintro ⟨j, backward, a, b, hab, hp, hq⟩
      exact ⟨j, backward, (a, b), hab, Prod.ext hp.symm hq.symm⟩
    · rintro ⟨j, backward, ⟨a, b⟩, hab, he⟩
      exact ⟨j, backward, a, b, hab, (congrArg Prod.fst he).symm,
        (congrArg Prod.snd he).symm⟩
  rw [heq]
  apply isCompact_iUnion
  intro j
  apply isCompact_iUnion
  intro backward
  apply (isCompact_maskedZeroEnergyRelation (coordinateSplit (i j))
    (χsource j) (χout j) Δ backward (hU j) (hK j) hW (hUD j) (hKD j) (hh j) (hΦ j)).image
  exact ((continuous_adaptedPhysicalPhaseState _).comp continuous_fst).prodMk
    ((continuous_adaptedPhysicalPhaseState _).comp continuous_snd)

/-- The full diagonal is closed without any characteristic-energy restriction
(`app:ch_regular:lem:finite-chain`). -/
theorem isClosed_fullPhaseDiagonal :
    IsClosed {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | pq.1 = pq.2} :=
  isClosed_eq continuous_fst continuous_snd

/-- Properness over compact inputs of the full diagonal. No global compactness
or annular restriction on the diagonal is asserted
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_fullPhaseDiagonal_over_compact
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S) :
    IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | pq.1 ∈ S ∧ pq.1 = pq.2} := by
  convert hS.image (continuous_id.prodMk continuous_id) using 1
  ext pq
  simp only [mem_ofPred_eq, mem_image]
  aesop

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
