module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Support

/-!
# Compact finite-band buffers for the frozen kernel

The compact sets are the original carrier-parameter and frequency supports.
Their actual frozen forward images supply the two slice-buffer fields of
`frozenRefinedKernelSymbolInputs`; no transformed support is assumed.
Sources: `new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' R : ℝ}

/-- The smaller original finite band lies in the retained outer frozen cone
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenRefined_bandInputSupport_subset
    (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') :
    bandInputSupport z₀ ηb r' a' R ⊆ frozenInputDomain z₀ ηb r (6 * a) := by
  intro p hp
  have hi := refined_bandInputSupport_subset hηb hr' ha' hrr haa har' hp
  have hz : (0 : Euclidean n) ∈ ball 0 (6 * a) := by
    simp only [mem_ball, dist_self]
    linarith
  exact ⟨⟨hi.1.1, hz, hz⟩, hi.2⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C) (hηb : ηb ≠ 0) (hr : 0 < r)
    (hr' : 0 < r') (ha' : 0 < a') (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))

include hP hηb hr hr' ha' hrr haa har' har hcarrier hf in
/-- Compactness of the smaller band's actual frozen forward image follows
from the outer chart's smoothness (`bg-full-complex-amplitude`). -/
theorem frozenRefined_bandImage_compact :
    IsCompact (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      bandInputSupport z₀ ηb r' a' R) := by
  apply (bandInputSupport_compact z₀ ηb r' a' R).image_of_continuousOn
  have hh := (frozenKernelGradient_smooth T Q hP hηb hr har hcarrier hf).continuousOn
  exact ((continuousOn_fst.fst.prodMk (continuousOn_fst.snd.prodMk hh)).prodMk
    continuousOn_snd.fst.snd).mono
      (frozenRefined_bandInputSupport_subset hηb hr' ha' hrr haa har')

include hP hηb hr hr' ha' hrr haa har' har hcarrier hf in
/-- Closed spectator slices of the actual frozen finite-band image, with
both physical positions retained (`bg-full-complex-amplitude`). -/
theorem frozenRefined_bandImage_slice_closed (p : Variables n) :
    IsClosed {v : Euclidean 2 | (p, v) ∈
      augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        bandInputSupport z₀ ηb r' a' R} :=
  (frozenRefined_bandImage_compact T Q hP hηb hr hr' ha' hrr haa har' har hcarrier hf).isClosed.preimage
    (continuous_const.prodMk continuous_id)

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hP hηb hr hr' ha' hrr haa har' har hcarrier hInv htrans in
/-- The smaller finite-band image has its buffer in the same outer frozen
symbol domain used by the literal inverse (`bg-full-complex-amplitude`). -/
theorem frozenRefined_bandImage_subset_symbolDomain :
    augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      bandInputSupport z₀ ηb r' a' R ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) := by
  rw [frozenSymbolDomain_eq_image T Q hP hηb hr har hcarrier hInv htrans]
  exact image_mono (frozenRefined_bandInputSupport_subset hηb hr' ha' hrr haa har')

end JanetCartan.ContinuumNormal.FrozenModel
