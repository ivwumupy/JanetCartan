module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Integral
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationPeriodization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SmoothRealization

/-!
# The concrete smooth canonical derivative map

The input remains `RawInputPartition.WideInput`. The SAME supplied slice
cutoff extends the physical derivative proved in `Integral`, and the existing
periodization realizes its exact values on the centered chart. This constructs
the `G` consumed by `CanonicalChange.smoothCanonicalDerivative`; it does not
choose a new smooth representative. The cutoff is only an extension and is
removed on its original measurement plateau.

Sources: `app:ch_mean_pairs:defn:mean-canonical`,
`app:ch_mean_pairs:eq:mean-current-canonical`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalAtomRealization

open RawPrimary RawInputPartition CorrectedAtoms CurrentMean AmplitudeBound
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1))
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ O ×ˢ V, (p.1, (z, ζ + τ • p.2)) ∈ Ω)
    (hτ : τ ≠ 0) (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ O)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

include hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
  hd hM hb hψ hs hcell hbox

/-- Finite-band smoothness on the actual torus is derived using the supplied
slice cutoff and the existing physical periodization
(`app:ch_mean_pairs:eq:mean-current-raw`). -/
theorem isSmoothPeriodic_cutCorrectedWideDerivative (v : WideInput n J) :
    IsSmoothPeriodic (fun x ↦ ψ (centeredTorusRepresentative x) •
      correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v (centeredTorusRepresentative x)) := by
  have hD := contDiffOn_correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v
  have hh := preparationMatrixExtension_regular ψ hψ hO hs hcell hbox
    (fun p ↦ correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v p.1)
    (hD.comp contDiffOn_fst (fun _ hp ↦ hp.1))
  exact ⟨hh.1.comp (continuous_id.prodMk (continuous_const (y := 0))),
    hh.2.comp (contDiff_id.prodMk (contDiff_const (c := 0)))⟩

/-- The constructed real-linear raw-to-smooth derivative map `G`. No inverse
sample weight, new raw space, or choice of smooth field is introduced. The
fixed upper cutoff is instantiated by `J = cutoffCount K`
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
def smoothCorrectedWideDerivative :
    WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) where
  toFun v := ⟨fun x _ ↦ ψ (centeredTorusRepresentative x) •
    correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v (centeredTorusRepresentative x),
    fun _ ↦ isSmoothPeriodic_cutCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox v⟩
  map_add' v w := by
    apply Subtype.ext
    funext x a
    change ψ _ • correctedWideDerivative _ _ _ _ _ _ _ _ _ _ _ _ _ _ (v + w) _ = _
    by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
    · rw [correctedWideDerivative_add T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
        hd hM hb v w (hs hx), smul_add]
      rfl
    · simp [image_eq_zero_of_notMem_tsupport hx]
  map_smul' a v := by
    apply Subtype.ext
    funext x u
    change ψ _ • correctedWideDerivative _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a • v) _ = _
    by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
    · rw [correctedWideDerivative_real_smul T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
        hd hM hb a v (hs hx)]
      exact smul_comm _ _ _
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Evaluation of `G` is the SAME physical derivative, with precisely the
given extension cutoff (`app:ch_mean_pairs:defn:mean-canonical`). -/
@[simp] theorem smoothCorrectedWideDerivative_apply (v : WideInput n J) (x : Torus n) :
    (smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox v).val x () =
      ψ (centeredTorusRepresentative x) •
        correctedWideDerivative T Q F row col Φ Y χ B τ r z ζ d v (centeredTorusRepresentative x) := rfl

/-- The constructed periodic map has its literal integral representation
at EVERY torus point. Outside the original chart the supplied slice cutoff
vanishes; no unproved regularity there is used
(`app:ch_waves:eq:individual-representation`). -/
theorem smoothCorrectedWideDerivative_eq_cutIntegral (v : WideInput n J) (x : Torus n) :
    (smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox v).val x () =
      ψ (centeredTorusRepresentative x) •
        rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
          (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
          ζ τ volume (weightedWideDensity d v) (centeredTorusRepresentative x) := by
  rw [smoothCorrectedWideDerivative_apply]
  by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
  · rw [correctedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v (hs hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- On the original measurement plateau, the smooth map is literally the
uncut corrected derivative integral. The same masks, half weights, Fourier
measure, and upper cutoff occur on both sides
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem smoothCorrectedWideDerivative_eq_integral (v : WideInput n J) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox v).val x () =
      rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
        (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
        ζ τ volume (weightedWideDensity d v) (centeredTorusRepresentative x) := by
  rw [smoothCorrectedWideDerivative_apply, hx, one_smul]
  apply correctedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v
  exact hs (subset_tsupport ψ (by rw [Function.mem_support, hx]; exact one_ne_zero))

/-- Applying the ORIGINAL raw adjoint and `Q₀` before this constructed `G`
gives exactly the canonical integral of
`app:ch_mean_pairs:eq:mean-current-canonical`. This component identity is
used for each member of the finite row; it changes neither the Hilbert
product nor the original inverse. -/
theorem smoothCanonicalDerivative_corrected_eq_integral
    (A : WideInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) (x : Torus n)
    (hx : ψ (centeredTorusRepresentative x) = 1) :
    (CanonicalChange.smoothCanonicalDerivative (fun _ : Unit ↦ A)
      (fun _ ↦ smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
        hd hM hb ψ hψ hs hcell hbox) Q₀ e).val x () =
      rawPrimaryDemodulatedIntegral (fun y η ↦ phase T Q y η)
        (fun y η ↦ fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (y, (z, η)))
        ζ τ volume (weightedWideDensity d (A.adjoint (Q₀ e))) (centeredTorusRepresentative x) :=
  smoothCorrectedWideDerivative_eq_integral T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
    hd hM hb ψ hψ hs hcell hbox (A.adjoint (Q₀ e)) x hx

end JanetCartan.CanonicalAtomRealization
