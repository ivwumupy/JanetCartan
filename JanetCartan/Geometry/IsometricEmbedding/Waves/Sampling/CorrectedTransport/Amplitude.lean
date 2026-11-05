module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedProfileBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.JointPolynomial

/-!
# A transport homotopy at one fixed response frequency

The response is always evaluated at its original positive inverse frequency.
Only the algebraic interpolation parameter varies. Its zero endpoint is the
same leading derivative, independent of that frequency; at the original
inverse frequency it is exactly the cut corrected derivative. The previously
proved inverse-frequency error cancels the normalization in every spatial jet.
This is the amplitude path for the corrected colored-to-transport comparison,
without differentiating the solver with respect to frequency.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

variable {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : Euclidean (d + 1) → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) →
      Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))
    (χ : Euclidean (d + 1) → ℝ)
    (B : MetricField (d + 1) →ₗ[ℝ] (Euclidean (d + 1) → Euclidean N))
    (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ)

/-- Normalize the SAME corrected-minus-leading error by its fixed positive
inverse frequency. The response is not evaluated at a varying homotopy
parameter (`app:ch_waves:eq:colored-normal-comparison`). -/
def correctedTransportScaledError (τ : ℝ)
    (w : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) :
    Matrix (Fin N) (Fin (d + 1)) ℂ :=
  τ⁻¹ • (κ w • (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w -
    fullLeadingPrincipalMatrix T Q F row col Φ Y r w))

/-- The literal amplitude interpolation for the original corrected sample.
Its parameter is later `ε / 2^j`; its fixed frequency remains `τ`
(`app:ch_waves:eq:phase-quotient`, `app:ch_waves:eq:colored-normal-comparison`). -/
def correctedTransportDerivativeHomotopy (τ : ℝ)
    (q : ℝ × (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))) :
    Matrix (Fin N) (Fin (d + 1)) ℂ :=
  κ q.2 • fullLeadingPrincipalMatrix T Q F row col Φ Y r q.2 +
    q.1 • correctedTransportScaledError T Q F row col Φ Y χ B r κ τ q.2

/-- All colors have the identical leading endpoint on the SAME cutoff
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportDerivativeHomotopy_zero (τ : ℝ) (w) :
    correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ (0, w) =
      κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w := by
  simp only [correctedTransportDerivativeHomotopy, zero_smul, add_zero]

/-- The other endpoint is exactly the original corrected derivative,
with no alteration of either amplitude slot (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedTransportDerivativeHomotopy_self {τ : ℝ} (hτ : τ ≠ 0) (w) :
    correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ (τ, w) =
      κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w := by
  rw [correctedTransportDerivativeHomotopy, correctedTransportScaledError,
    smul_smul, mul_inv_cancel₀ hτ, one_smul, smul_sub]
  abel

/-- Every homotopy slice retains the supplied cutoff support, including
points outside the retained physical/carrier chart
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem correctedTransportDerivativeHomotopy_eventually_zero
    (τ t : ℝ) (w) (hw : w ∉ tsupport κ) :
    correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ =ᶠ[𝓝 (t, w)] 0 := by
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
    (continuous_snd.tendsto (t, w))
  filter_upwards [hz] with q hq
  change κ q.2 = 0 at hq
  simp only [correctedTransportDerivativeHomotopy, correctedTransportScaledError,
    hq, zero_smul, smul_zero, add_zero, Pi.zero_apply]

variable {Kjoint Ω : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))}
    (hΩ : IsOpen Ω) (hκ : ContDiff ℝ ∞ κ) (hκsupport : tsupport κ ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)

include hΩ hκ hκsupport hphase hν₀ in
/-- Smoothness of the cut leading field follows on its original phase domain
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
private theorem smooth_cut_leading :
    ContDiff ℝ ∞ (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w) := by
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hl : ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r) Ω := by
    apply (contDiffOn_normalTensor hξ hν₀).neg.congr
    intro x _
    exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r x
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ tsupport κ
  · exact hκ.contDiffAt.smul (hl.contDiffAt (hΩ.mem_nhds (hκsupport hw)))
  · have hz : κ =ᶠ[𝓝 w] 0 := notMem_tsupport_iff_eventuallyEq.mp hw
    apply (contDiffAt_const (c := (0 : Matrix (Fin N) (Fin (d + 1)) ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul]

include hΩ hκ hκsupport hphase hν₀ hν₁ hV₀ hV₁ hτ hresponse

/-- The normalized error is globally smooth using only the SAME fixed
response's spatial smoothness and the original cutoff support
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem contDiff_correctedTransportScaledError :
    ContDiff ℝ ∞ (correctedTransportScaledError T Q F row col Φ Y χ B r κ τ) := by
  have ha := contDiff_cutCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r κ
    hΩ hκ hκsupport hphase hν₀ hν₁ hV₀ hV₁ hτ hresponse
  have hl := smooth_cut_leading T Q F row col Φ Y r κ hΩ hκ hκsupport hphase hν₀
  change ContDiff ℝ ∞ (fun w ↦ τ⁻¹ • (κ w •
    (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r w)))
  simpa only [smul_sub] using (ha.sub hl).const_smul τ⁻¹

/-- Joint smoothness through parameter zero does not assume frequency
regularity of the response. It is the explicit affine interpolation of the
SAME fixed response (`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_correctedTransportDerivativeHomotopy :
    ContDiff ℝ ∞ (correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ) := by
  have hl := smooth_cut_leading T Q F row col Φ Y r κ hΩ hκ hκsupport hphase hν₀
  have he := contDiff_correctedTransportScaledError T Q F row col Φ Y χ B r κ
    hΩ hκ hκsupport hphase hν₀ hν₁ hV₀ hV₁ hτ hresponse
  exact (hl.comp contDiff_snd).add (contDiff_fst.smul (he.comp contDiff_snd))

end JanetCartan.Sampling.CorrectedTransport
