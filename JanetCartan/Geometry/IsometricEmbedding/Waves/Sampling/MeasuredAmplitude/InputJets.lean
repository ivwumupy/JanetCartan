module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.NormalizedBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ParameterJets

/-!
# Full normal input jets of the measured amplitude

The finite output-coordinate map and freezing of the spectator preserve the
joint bounds. The epsilon derivative costs one further joint order, including
at zero. This supplies the two amplitude terms of `UniformNormalData.input_jets`
for `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open FullNormalGeometry FullNormalGeometry.PhaseJets RawPrimary.SliceBounds
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

/-- The actual finite output coordinates used by `UniformNormalData`. This
only exposes the components of the SAME complex vector; both quadratures
remain present (`app:ch_waves:eq:sampling-prefix-normal`). -/
def measuredOutputCoordinates (n : ℕ) : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℂ)).toContinuousLinearMap

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Freezing the spectator contracts the original joint jets; the only
output cost is the fixed finite coordinate map, independent of every band,
field and frequency (`app:ch_waves:setup:oscillatory`). -/
theorem measured_spectator_jet_le {M : ℝ}
    {f : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) →
      EuclideanSpace ℂ (Fin (m + 1))}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M))
    (ε : ℝ) {v : Euclidean 2} {w : Euclidean (m + 1) × Euclidean (m + 1)}
    (hw : w ∈ fullPhaseExtensionDomain T v M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        (f (q.1, v, q.2)).ofLp) (ε, w)‖ ≤
      ‖measuredOutputCoordinates (m + 1)‖ * ‖iteratedFDeriv ℝ k f (ε, v, w)‖ := by
  let L : (ℝ × (Euclidean (m + 1) × Euclidean (m + 1))) →L[ℝ]
      (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((0 : (ℝ × (Euclidean (m + 1) × Euclidean (m + 1))) →L[ℝ] Euclidean 2).prod
        (ContinuousLinearMap.snd ℝ _ _))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro q
    simp [L, Prod.norm_def]
  have hh := norm_iteratedFDeriv_preAffine_le L (0, v, 0)
    (isOpen_univ.prod (isOpen_tripleDomain T M)) hf
    (x := (ε, w)) (by simpa [L, tripleDomain] using And.intro (mem_univ ε) hw) k
  have hrestr : ‖iteratedFDeriv ℝ k
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦ f (q.1, v, q.2)) (ε, w)‖ ≤
      ‖iteratedFDeriv ℝ k f (ε, v, w)‖ := by
    simpa [L] using hh.trans (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hL))
  have hi : ContDiff ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦ (q.1, v, q.2)) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hf₀ : ContDiffAt ℝ ∞ f (ε, v, w) :=
    hf.contDiffAt ((isOpen_univ.prod (isOpen_tripleDomain T M)).mem_nhds
      ⟨mem_univ _, hw⟩)
  have hs := hf₀.comp (ε, w) hi.contDiffAt
  exact ((measuredOutputCoordinates (m + 1)).norm_iteratedFDeriv_comp_left hs
    (by simp : (k : ℕ∞ω) ≤ ∞)).trans
      (mul_le_mul_of_nonneg_left hrestr (norm_nonneg _))

/-- Exact amplitude input-jet estimate, including the ordinary epsilon
derivative at both closed endpoints, from orders `k` and `k+1` of the proved
joint polynomial. The common geometry is unchanged
(`app:ch_waves:setup:oscillatory`). -/
theorem measured_inputJets_le_joint {M : ℝ}
    {f : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) →
      EuclideanSpace ℂ (Fin (m + 1))}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M))
    (ε : ℝ) {v : Euclidean 2} {w : Euclidean (m + 1) × Euclidean (m + 1)}
    (hw : w ∈ fullPhaseExtensionDomain T v M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ (f (ε, v, y)).ofLp) w‖ +
      ‖deriv (fun t ↦ iteratedFDeriv ℝ k (fun y ↦ (f (t, v, y)).ofLp) w) ε‖ ≤
      ‖measuredOutputCoordinates (m + 1)‖ *
        (‖iteratedFDeriv ℝ k f (ε, v, w)‖ + ‖iteratedFDeriv ℝ (k + 1) f (ε, v, w)‖) := by
  have hs : ContDiffOn ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦ (f (q.1, v, q.2)).ofLp)
      (univ ×ˢ fullPhaseExtensionDomain T v M) :=
    PiLp.contDiff_ofLp.comp_contDiffOn
      (hf.comp (by fun_prop) (fun q hq ↦ hq))
  rw [mul_add]
  exact add_le_add
    ((norm_iteratedFDeriv_slice_le_joint isOpen_univ
      (isOpen_fullPhaseExtensionDomain T v M) hs (mem_univ ε) hw k).trans
        (measured_spectator_jet_le T hf ε hw k))
    ((norm_deriv_sliceJet_le_joint isOpen_univ
      (isOpen_fullPhaseExtensionDomain T v M) hs (mem_univ ε) hw k).trans
        (measured_spectator_jet_le T hf ε hw (k + 1)))

end JanetCartan.Sampling.MeasuredAmplitude
