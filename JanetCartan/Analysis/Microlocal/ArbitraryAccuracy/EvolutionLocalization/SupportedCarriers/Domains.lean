module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.Carriers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Locality

/-!
# Common elapsed chart domains and mixed-point carriers

The open two-time domain and its buffered inclusions are inputs from the
original two-time chart construction. Compactness of the elapsed interval
makes its simultaneous pullback open. The chart carrier also contains all
mixed points required by both orientations of the primitive graph theorem;
agreement merely on the amplitude support would not suffice there.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph

variable {d : ℕ}

/-- The actual two-time point, in the joint phase coordinates of
`SymbolBudgets`, for `app:ch_regular_base:eq:fixed-time-representation`. -/
def elapsedPhasePoint (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    SymbolBudgets.TwoTimePoint d :=
  ((p.1 0, p.1 0 - r, spatialPart p.1), spatialPart p.2)

/-- The pullback uses the original spatial covector, including its chart
restriction (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem contDiff_elapsedPhasePoint :
    ContDiff ℝ ∞ (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × ℝ =>
      elapsedPhasePoint p.2 p.1) := by
  have ht : ContDiff ℝ ∞ (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × ℝ =>
      p.1.1 0) := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp
        (contDiff_fst.comp contDiff_fst)
  exact (ht.prodMk ((ht.sub contDiff_snd).prodMk
    (spatialPartCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)))).prodMk
      (spatialPartCLM.contDiff.comp (contDiff_snd.comp contDiff_fst))

/-- One domain works throughout the bounded elapsed interval. It is defined
by the actual two-time chart, not by nonvanishing of the spacetime covector
(`app:ch_regular:lem:finite-chain`). -/
def elapsedCommonPhaseDomain (Δ : ℝ)
    (W : Set (SymbolBudgets.TwoTimePoint d)) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  {p | ∀ r ∈ Icc 0 Δ, elapsedPhasePoint r p ∈ W}

/-- Compactness of the elapsed interval proves openness of the simultaneous
chart domain (`app:ch_regular:lem:finite-chain`). -/
theorem isOpen_elapsedCommonPhaseDomain (Δ : ℝ)
    {W : Set (SymbolBudgets.TwoTimePoint d)} (hW : IsOpen W) :
    IsOpen (elapsedCommonPhaseDomain Δ W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro r hr
  exact contDiff_elapsedPhasePoint.continuous.continuousAt.preimage_mem_nhds
    (hW.mem_nhds (hp r hr))

/-- The original joint two-time regularity supplies the phase regularity
on the common domain, uniformly in elapsed time. This is the `hφ`/`hSV`
input of the primitive graph theorem (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiffOn_elapsedPhase_commonDomain
    (Ψ : TwoTimePhase d) (Δ : ℝ)
    {W : Set (SymbolBudgets.TwoTimePoint d)} (hW : IsOpen W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    {r : ℝ} (hr : r ∈ Icc 0 Δ) :
    ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r))
      (elapsedCommonPhaseDomain Δ W) := by
  have hc : ContDiff ℝ ∞ (elapsedPhasePoint (d := d) r) :=
    contDiff_elapsedPhasePoint.comp (contDiff_id.prodMk contDiff_const)
  have hs : ContDiffOn ℝ ∞ (fun p => SymbolBudgets.jointPhase Ψ (elapsedPhasePoint r p))
      (elapsedCommonPhaseDomain Δ W) := by
    intro p hp
    exact ((hΨ.contDiffAt (hW.mem_nhds (hp r hr))).comp p hc.contDiffAt).contDiffWithinAt
  have ht : ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × Euclidean (d + 1) =>
      (p.1 0 - r) * p.2 0) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp contDiff_fst).sub
      contDiff_const).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp contDiff_snd)
  exact ht.contDiffOn.add hs

/-- The actual two-time chart target, expressed in the symbol budget's
joint coordinates. This supplies `W` to the supported extension constructor
(`app:ch_regular_base:eq:fixed-time-representation`). -/
def elapsedJointChartDomain
    (C : OpenPartialHomeomorph
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))) :
    Set (SymbolBudgets.TwoTimePoint d) :=
  (fun p : SymbolBudgets.TwoTimePoint d => (p.1.1, p.1.2.1, p.1.2.2, p.2)) ⁻¹' C.target

/-- Openness is inherited from the original chart, without enlarging its
spatial frequency domain (`app:ch_regular:lem:finite-chain`). -/
theorem isOpen_elapsedJointChartDomain
    (C : OpenPartialHomeomorph
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))) :
    IsOpen (elapsedJointChartDomain C) :=
  C.open_target.preimage (by fun_prop)

/-- The inverse-chart smoothness conclusion of
`RegularSector.Characteristic.exists_localTwoTimeHamiltonPhase` supplies
the exact joint phase regularity used here, via `contDiffOn_twoTimePhase`.
This adapter requires no regularity outside the actual chart target
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem contDiffOn_jointPhase_chartPhase
    (C : OpenPartialHomeomorph
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d)))
    (hC : ContDiffOn ℝ ∞ C.symm C.target) :
    ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (chartPhase C)) (elapsedJointChartDomain C) := by
  have hc : ContDiff ℝ ∞ (fun p : SymbolBudgets.TwoTimePoint d =>
      (p.1.1, p.1.2.1, p.1.2.2, p.2)) := by fun_prop
  exact (RegularSector.Characteristic.contDiffOn_twoTimePhase hC).comp hc.contDiffOn
    (fun _ hp => hp)

/-- The buffer conditions for this construction are exactly inclusions in
the original target, at all elapsed times. The relation-point inclusion for
the forward map is supplied by `elapsedChartPoint_elapsedCanonicalMap` and
`C.map_source`; mixed-point and angular buffers remain explicit geometric
inputs of the original chart refinement (`app:ch_regular:lem:finite-chain`). -/
theorem mem_elapsedCommonPhaseDomain_chart_iff
    (C : OpenPartialHomeomorph
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d))
      (RegularSector.Characteristic.TwoTimePoint (Euclidean d)))
    (Δ : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    p ∈ elapsedCommonPhaseDomain Δ (elapsedJointChartDomain C) ↔
      ∀ r ∈ Icc 0 Δ, elapsedChartPoint r p.1 p.2 ∈ C.target := Iff.rfl

/-- The symbol/multiplier support and the physical chart buffer put every
graph shell in the same open domain. `hbuffer` is precisely the original
two-time chart inclusion on the fixed physical mask and frequency support;
it contains no graph estimate (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedPhysicalPhaseCarrier_subset_commonDomain
    (χout β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d)) (Δ : ℝ)
    (W : Set (SymbolBudgets.TwoTimePoint d))
    (hbuffer : ∀ r ∈ Icc 0 Δ, ∀ u ∈ tsupport χout,
      ∀ ξ ∈ elapsedFrequencyCarrier β F, elapsedPhasePoint r (u, ξ) ∈ W)
    (low : Bool) (j : ℕ) :
    elapsedPhysicalPhaseCarrier χout β F low j ⊆ elapsedCommonPhaseDomain Δ W := by
  intro p hp r hr
  exact hbuffer r hr p.1 hp.1 p.2 hp.2.2

/-- A fixed base/spatial-frequency buffer in the original two-time domain
gives the normalized comparable inclusion. `hfrequency` is the spatial
support inclusion of the multiplier and original symbol after normalization;
the preceding cone bound proves its positive inner radius. Angular inclusion
and `hbuffer` belong to the original conic two-time chart construction
(`app:ch_regular:lem:finite-chain`). -/
theorem elapsedComparableCarrier_subset_commonDomain
    (χout β : Euclidean (d + 1) → ℂ) (F : Set (Euclidean d)) (c C a b Δ : ℝ)
    {X : Set (Euclidean (d + 1))} {D : Set (Euclidean d)}
    {W : Set (SymbolBudgets.TwoTimePoint d)}
    (hbase : tsupport χout ⊆ X)
    (hfrequency : ∀ ξ ∈
      PhysicalShells.frequencyAnnulus (a / (16 * KernelEstimates.NoncomparableGeometry.annulusFactor c C))
        (4 * max 1 (4 * KernelEstimates.NoncomparableGeometry.annulusFactor c C * b)) ∩
          elapsedNormalizedFrequencyCarrier β F, spatialPart ξ ∈ D)
    (hbuffer : ∀ r ∈ Icc 0 Δ, ∀ u ∈ X, ∀ η ∈ D,
      ((u 0, u 0 - r, spatialPart u), η) ∈ W) :
    elapsedComparableCarrier χout β F c C a b ⊆ elapsedCommonPhaseDomain Δ W := by
  intro p hp r hr
  exact hbuffer r hr p.1 (hbase hp.1) (spatialPart p.2) (hfrequency p.2 hp.2)

/-- Compact mixed-point carrier for a whole elapsed family. The relation
points and the off-diagonal mixed points are retained separately; this
avoids asking for regularity on unused rectangular phase domains
(`app:ch_regular:eq:joint-stationary`). -/
def elapsedMixedPhaseCarrier (backward : Bool) (Δ : ℝ)
    (κ : ℝ → (Euclidean (d + 1) × Euclidean (d + 1)) →
      Euclidean (d + 1) × Euclidean (d + 1))
    (I Z : Set (Euclidean (d + 1) × Euclidean (d + 1))) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  Z ∪ (fun rp : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
      if backward then (rp.2.1, (κ rp.1 rp.2).2) else ((κ rp.1 rp.2).1, rp.2.2)) ''
        (Icc 0 Δ ×ˢ I) ∪
    (if backward then (Prod.fst '' I) ×ˢ (Prod.snd '' Z)
      else (Prod.fst '' Z) ×ˢ (Prod.snd '' I))

/-- The actual canonical map's continuity, supplied for the forward map by
`continuousOn_elapsedCanonicalMap`, gives a compact common chart carrier.
The literal inverse map uses its own inverse-chart continuity
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_elapsedMixedPhaseCarrier (backward : Bool) (Δ : ℝ)
    {κ : ℝ → (Euclidean (d + 1) × Euclidean (d + 1)) →
      Euclidean (d + 1) × Euclidean (d + 1)}
    {I Z : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hI : IsCompact I) (hZ : IsCompact Z)
    (hκ : ContinuousOn (fun rp : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
      κ rp.1 rp.2) (Icc 0 Δ ×ˢ I)) :
    IsCompact (elapsedMixedPhaseCarrier backward Δ κ I Z) := by
  cases backward
  · exact (hZ.union ((isCompact_Icc.prod hI).image_of_continuousOn
      (hκ.fst.prodMk continuous_snd.snd.continuousOn))).union
        ((hZ.image continuous_fst).prod (hI.image continuous_snd))
  · exact (hZ.union ((isCompact_Icc.prod hI).image_of_continuousOn
      (continuous_snd.fst.continuousOn.prodMk hκ.snd))).union
        ((hI.image continuous_fst).prod (hZ.image continuous_snd))

/-- The carrier supplies exactly `hZT` and `hpoints` of the primitive graph
theorem, simultaneously for every elapsed time and either orientation
(`app:ch_regular:eq:joint-stationary`). -/
theorem elapsedMixedPhaseCarrier_contains (backward : Bool) (Δ : ℝ)
    (κ : ℝ → (Euclidean (d + 1) × Euclidean (d + 1)) →
      Euclidean (d + 1) × Euclidean (d + 1))
    (I Z : Set (Euclidean (d + 1) × Euclidean (d + 1))) :
    let T := elapsedMixedPhaseCarrier backward Δ κ I Z
    Z ⊆ T ∧ ∀ r ∈ Icc 0 Δ,
      if backward then
        (∀ p ∈ I, (p.1, (κ r p).2) ∈ T) ∧
          (∀ p ∈ I, ∀ z ∈ Z, (p.1, z.2) ∈ T)
      else
        (∀ p ∈ I, ((κ r p).1, p.2) ∈ T) ∧
          (∀ p ∈ I, ∀ z ∈ Z, (z.1, p.2) ∈ T) := by
  refine ⟨fun _ h => Or.inl (Or.inl h), ?_⟩
  intro r hr
  cases backward <;> refine ⟨?_, ?_⟩
  · intro p hp
    exact Or.inl (Or.inr ⟨(r, p), ⟨hr, hp⟩, rfl⟩)
  · intro p hp z hz
    exact Or.inr ⟨⟨z, hz, rfl⟩, ⟨p, hp, rfl⟩⟩
  · intro p hp
    exact Or.inl (Or.inr ⟨(r, p), ⟨hr, hp⟩, rfl⟩)
  · intro p hp z hz
    exact Or.inr ⟨⟨p, hp, rfl⟩, ⟨z, hz, rfl⟩⟩

/-- The original buffered chart inclusions suffice for the entire mixed
carrier. These geometric inclusions must be instantiated by the original
two-time chart and its forward/inverse image buffers; no phase estimate or
successful localization is a premise (`app:ch_regular:lem:finite-chain`). -/
theorem elapsedMixedPhaseCarrier_subset (backward : Bool) (Δ : ℝ)
    (κ : ℝ → (Euclidean (d + 1) × Euclidean (d + 1)) →
      Euclidean (d + 1) × Euclidean (d + 1))
    {I Z U : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hZ : Z ⊆ U)
    (hpoints : ∀ r ∈ Icc 0 Δ, ∀ p ∈ I,
      (if backward then (p.1, (κ r p).2) else ((κ r p).1, p.2)) ∈ U)
    (hmixed : ∀ p ∈ I, ∀ z ∈ Z,
      (if backward then (p.1, z.2) else (z.1, p.2)) ∈ U) :
    elapsedMixedPhaseCarrier backward Δ κ I Z ⊆ U := by
  rintro p ((hp | ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩) | hp)
  · exact hZ hp
  · exact hpoints r hr y hy
  · cases backward
    · obtain ⟨⟨z, hz, hez⟩, ⟨y, hy, hey⟩⟩ := hp
      simpa only [Bool.false_eq_true, ite_false, hez, hey, Prod.eta] using hmixed y hy z hz
    · obtain ⟨⟨y, hy, hey⟩, ⟨z, hz, hez⟩⟩ := hp
      simpa only [ite_true, hez, hey, Prod.eta] using hmixed y hy z hz

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
