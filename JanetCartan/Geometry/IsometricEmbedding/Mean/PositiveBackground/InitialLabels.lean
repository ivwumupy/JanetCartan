module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Transport
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot

/-!
# The synthesized density in the original transport labels

The raw density uses `((s,v),y)` whereas the retained null flow takes `(y,z)`
with `z ∈ ℝ³`. This fixed relabeling preserves the actual scalar after applying
`Canonical.initialScalar`. It introduces neither a new footpoint nor an
initial-position cutoff. Its finite-jet bound supplies the original density
class in `WideDensity.exists_source_densityPair_comparison` from the bounds of
`SourceInverse.exists_small_uncorrectedDensity_of_normal_estimates`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PositiveBackground
open ContinuumRow FullPhaseCharts.ActualComparison

variable {n : ℕ}

/-- The literal uncut density in the retained ODE's initial labels
(`app:ch_background:eq:bg-density-four`, `app:ch_background:prop:bg-frame`). -/
def densityOnInitialLabels (v : CarrierVariable n → ℝ)
    (q : Euclidean (n - 1) × Euclidean 3) : ℝ :=
  v ((q.2 0, spectatorCenter q.2), q.1)

private theorem contDiff_initialLabelMap :
    ContDiff ℝ ∞ (fun q : Euclidean (n - 1) × Euclidean 3 ↦
      ((q.2 0, spectatorCenter q.2), q.1)) := by
  have hs : ContDiff ℝ ∞ (fun q : Euclidean (n - 1) × Euclidean 3 ↦
      spectatorCenter q.2) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i <;> dsimp [spectatorCenter] <;> fun_prop
  exact ((by fun_prop : ContDiff ℝ ∞
    (fun q : Euclidean (n - 1) × Euclidean 3 ↦ q.2 0)).prodMk hs).prodMk contDiff_fst

/-- Relabeling the output back into the raw coordinates recovers the SAME
density at every carrier and initial point (`app:ch_background:eq:bg-density-four`). -/
theorem initialScalar_densityOnInitialLabels (v : CarrierVariable n → ℝ) :
    ContinuumAdjoint.Canonical.initialScalar (densityOnInitialLabels v) = v := by
  funext p
  change v (((CanonicalCarrier.parameter p.1) 0,
    spectatorCenter (CanonicalCarrier.parameter p.1)), p.2) = v p
  congr 1
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  · rfl

/-- Global smoothness is preserved by the original fixed coordinate change,
with no initial-position restriction (`app:ch_background:prop:bg-positive`). -/
theorem contDiff_densityOnInitialLabels {v : CarrierVariable n → ℝ}
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (densityOnInitialLabels v) :=
  hv.comp contDiff_initialLabelMap

/-- The corrected scalar supplied to the retained flow has exactly the
factor-four synthesized density in the raw variables; the fixed relabeling
does not change its scale (`app:ch_background:prop:bg-positive`). -/
theorem initialScalar_positiveDensityAmplitude_labels (σ : ℝ) (v : CarrierVariable n → ℝ) :
    ContinuumAdjoint.Canonical.initialScalar
      (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q)) =
        fun p ↦ positiveDensityAmplitude σ (v p) := by
  funext p
  change positiveDensityAmplitude σ
    (ContinuumAdjoint.Canonical.initialScalar (densityOnInitialLabels v) p) = _
  rw [initialScalar_densityOnInitialLabels]

/-- Global raw jet bounds control the density on the actual compact ODE-label
domain without losing derivatives. The constant precedes the density and its
size (`app:ch_background:prop:bg-frame`, `bg-positive-profile`). -/
theorem exists_cNorm_densityOnInitialLabels_le
    {K : Set (Euclidean (n - 1) × Euclidean 3)} (hK : IsCompact K) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (v : CarrierVariable n → ℝ) (A : ℝ), 0 ≤ A →
      ContDiff ℝ ∞ v →
      (∀ j ≤ k, ∀ p, ‖iteratedFDeriv ℝ j v p‖ ≤ A) →
      cNorm K k (densityOnInitialLabels v) ≤ C * A := by
  obtain ⟨C, hC, hb⟩ := ActualCarriers.ConstructedCarrierJets.exists_cNorm_fixed_pullback_le_jet_bound
    (G := ℝ) hK (fun p _ ↦ contDiff_initialLabelMap.contDiffAt (x := p)) k
  exact ⟨C, hC, fun v A hA hv hj ↦
    hb v A hA (fun _ _ ↦ hv.contDiffAt.of_le (by simp)) (fun j h _ _ ↦ hj j h _)⟩

end JanetCartan.PositiveBackground
