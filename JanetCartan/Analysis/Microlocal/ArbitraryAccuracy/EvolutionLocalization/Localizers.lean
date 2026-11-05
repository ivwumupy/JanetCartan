module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CanonicalMap
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# Common buffers for the actual elapsed canonical maps

The root and flow are only used on their original open domains. Their
smoothness gives continuity of the lifted canonical map, hence one compact
image carrier and one pair of buffered symbols for the whole elapsed interval.
The entire closed input support, including the shoulders, is protected from
the closed support of `1 - mo`. No kernel estimate is assumed here.

Consumer: the compact carriers and localizers in
`exists_graph_factor_sobolev_bound_of_primitive_grades`, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph

variable {d : ℕ}

/-- The full source-base-aware image of an elapsed family. This is the
output plateau carrier in `app:ch_regular:lem:finite-chain`. -/
def elapsedCanonicalImage (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (T : Set ℝ) (K : Set (Euclidean (d + 1) × Euclidean (d + 1))) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  (fun z : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
    elapsedCanonicalMap h Φ z.1 z.2) '' (T ×ˢ K)

/-- Continuity of the actual canonical map on a common elapsed/input
domain follows from the original smooth root and flow. The domain and range
inclusions are the geometric outputs of the local two-time construction,
to be checked on the chosen common buffers (`app:ch_regular:lem:finite-chain`). -/
theorem continuousOn_elapsedCanonicalMap
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {D : Set (RootState (Euclidean d))} {W : Set (RootState (Euclidean d) × ℝ)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W)
    {T : Set ℝ} {I : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hi : ∀ p ∈ I, spacetimeRootState p ∈ D)
    (hw : ∀ r ∈ T, ∀ p ∈ I, (spacetimeRootState p, r) ∈ W)
    (ho : ∀ r ∈ T, ∀ p ∈ I, Φ (spacetimeRootState p, r) ∈ D) :
    ContinuousOn (fun z : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
      elapsedCanonicalMap h Φ z.1 z.2) (T ×ˢ I) := by
  intro z hz
  exact (contDiffAt_elapsedCanonicalMap
    (hh.contDiffAt (hD.mem_nhds (hi z.2 hz.2)))
    (hh.contDiffAt (hD.mem_nhds (ho z.1 hz.1 z.2 hz.2)))
    (hΦ.contDiffAt (hW.mem_nhds (hw z.1 hz.1 z.2 hz.2)))).continuousAt.continuousWithinAt

/-- Construct common compact proof localizers from the primitive root/flow
regularity and their actual buffered domains. The same symbols and positive
geometric gap work for all `r ∈ [0, Δ]`, before any scale or accuracy is
chosen. The compact image is explicitly retained for the primitive graph
theorem, and `1 - mo` retains the identity contribution
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsed_bufferedLocalizers
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {D : Set (RootState (Euclidean d))} {W : Set (RootState (Euclidean d) × ℝ)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (Δ : ℝ) {K I O : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hK : IsCompact K) (hI : IsOpen I) (hO : IsOpen O) (hKI : K ⊆ I)
    (hi : ∀ p ∈ I, spacetimeRootState p ∈ D)
    (hw : ∀ r ∈ Icc 0 Δ, ∀ p ∈ I, (spacetimeRootState p, r) ∈ W)
    (ho : ∀ r ∈ Icc 0 Δ, ∀ p ∈ I, Φ (spacetimeRootState p, r) ∈ D)
    (himage : ∀ r ∈ Icc 0 Δ, ∀ p ∈ I, elapsedCanonicalMap h Φ r p ∈ O) :
    ∃ (mi mo : LocalizerSymbol (d + 1)) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧
      IsCompact (elapsedCanonicalImage h Φ (Icc 0 Δ) (tsupport mi)) ∧
      IsBufferedLocalizer mo (elapsedCanonicalImage h Φ (Icc 0 Δ) (tsupport mi)) O ∧
      (∀ r ∈ Icc 0 Δ, ∀ p ∈ tsupport mi,
        elapsedCanonicalMap h Φ r p ∈ interior {q | mo q = 1}) ∧
      ∀ r ∈ Icc 0 Δ, ∀ p ∈ tsupport mi, ∀ q ∈ tsupport (fun q => 1 - mo q),
        δ < dist (elapsedCanonicalMap h Φ r p) q := by
  have hc := continuousOn_elapsedCanonicalMap hD hh hW hΦ hi hw ho
  obtain ⟨mi, mo, δ, hδ, hmi, hmo, hbuffer, hgap⟩ :=
    exists_bufferedLocalizers_with_gap isCompact_Icc hK hI hO hKI
      (elapsedCanonicalMap h Φ) hc himage
  exact ⟨mi, mo, δ, hδ, hmi,
    (isCompact_Icc.prod hmi.compactSupport).image_of_continuousOn
      (hc.mono (prod_mono Subset.rfl hmi.support_subset)), hmo, hbuffer, hgap⟩

/-- A constructed compact localizer inside the nonzero-covector region
has a positive normalized annulus and a compact physical carrier. Consumer:
`hiSupport` (or the output physical carrier) in the primitive graph theorem.
This includes the entire closed support, not just the plateau
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_elapsed_localizer_annular_carrier
    {m : LocalizerSymbol (d + 1)} {K O : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hm : IsBufferedLocalizer m K O) (hO : ∀ p ∈ O, p.2 ≠ 0) :
    ∃ (Ki : Set (Euclidean (d + 1))) (a b : ℝ),
      IsCompact Ki ∧ 0 < a ∧ a < b ∧
      tsupport m ⊆ Ki ×ˢ PhysicalShells.frequencyAnnulus a b := by
  obtain ⟨a, ha, hlow⟩ := CompatibleResponse.exists_uniform_positive_bound hm.compactSupport
    (continuous_snd.norm.continuousOn)
    (fun p hp => norm_pos_iff.mpr (hO p (hm.support_subset hp)))
  obtain ⟨b, hb⟩ := hm.compactSupport.exists_bound_of_continuousOn
    continuous_snd.continuousOn
  refine ⟨Prod.fst '' tsupport m, a, max a b + 1,
    hm.compactSupport.image continuous_fst, ha, ?_, ?_⟩
  · linarith [le_max_left a b]
  · intro p hp
    exact ⟨⟨p, hp, rfl⟩, hlow p hp,
      (hb p hp).trans ((le_max_right a b).trans (le_add_of_nonneg_right zero_le_one))⟩

/-- The source-base-aware flow identity excludes the full actual forward
canonical relation on the complementary support of a buffered output. The
phase is used only on its original two-time chart; no extension at spatial
frequency zero enters (`app:ch_regular:eq:joint-stationary`). -/
theorem not_forwardRelation_of_elapsed_buffer
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    {mo : LocalizerSymbol (d + 1)}
    (hbuffer : elapsedCanonicalMap h Φ r p ∈ interior {z | mo z = 1})
    (hq : q ∈ tsupport (fun z => 1 - mo z))
    (hchart : elapsedChartPoint r q.1 p.2 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r q.1 p.2))).1 = q.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r q.1 p.2))
      (elapsedChartPoint r q.1 p.2)) :
    ¬ ForwardRelation (elapsedPhase (chartPhase C) r) p.1 p.2 q.1 q.2 := by
  intro hrel
  rw [elapsedCanonicalMap_eq_of_forwardRelation hC hchart hclock hphase hrel] at hbuffer
  exact notMem_complement_tsupport_of_mem_plateau hbuffer hq

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
