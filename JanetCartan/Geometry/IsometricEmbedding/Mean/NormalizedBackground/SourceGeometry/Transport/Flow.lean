module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Geometry

/-!
# Physical characteristic dilation with fixed labels

Direct conjugation of the supplied seed flow in `app:ch_background:eq:bg-Nsigma`.
Only physical time and initial position scale. The carrier and canonical labels
are unchanged. The exponential formula proves the scalar identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Scale initial position, retaining all carrier/canonical labels
(`app:ch_background:eq:bg-Nsigma`). -/
def transportLabelDilation (ρ : ℝ) (p : X × Z) : X × Z := (ρ • p.1, p.2)

/-- Scale physical time and position, retaining all carrier/canonical labels
(`app:ch_background:eq:bg-Nsigma`). -/
def transportCoordinateDilation (ρ : ℝ) (q : ℝ × (X × Z)) : ℝ × (X × Z) :=
  (ρ * q.1, transportLabelDilation ρ q.2)

/-- The same explicit conjugation rescales the seed characteristic flow and
its inverse footpoint map (`app:ch_background:eq:bg-Nsigma`). -/
def sourceTransportFlow (Φ : ℝ × (X × Z) → X × Z) (ρ : ℝ)
    (q : ℝ × (X × Z)) : X × Z :=
  transportLabelDilation ρ⁻¹ (Φ (transportCoordinateDilation ρ q))

/-- Inverse position scaling does not affect labels
(`app:ch_background:eq:bg-Nsigma`). -/
@[simp] theorem transportLabelDilation_inv {ρ : ℝ} (hρ : ρ ≠ 0) (p : X × Z) :
    transportLabelDilation ρ (transportLabelDilation ρ⁻¹ p) = p := by
  simp [transportLabelDilation, smul_smul, hρ]

/-- The transformed physical Cauchy flow is still the identity on `t = 0`
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceTransportFlow_initial {Φ : ℝ × (X × Z) → X × Z}
    {ρ : ℝ} (hρ : ρ ≠ 0) {p : X × Z}
    (hΦ : Φ (0, transportLabelDilation ρ p) = transportLabelDilation ρ p) :
    sourceTransportFlow Φ ρ (0, p) = p := by
  simp only [sourceTransportFlow, transportCoordinateDilation, mul_zero, hΦ]
  simp [transportLabelDilation, smul_smul, hρ]

/-- The conjugated inverse chart is a left inverse wherever the seed is
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceTransportFlow_left_inverse
    {Φ Y : ℝ × (X × Z) → X × Z} {ρ : ℝ} (hρ : ρ ≠ 0)
    {t : ℝ} {p : X × Z}
    (hY : Y (ρ * t, Φ (ρ * t, transportLabelDilation ρ p)) =
      transportLabelDilation ρ p) :
    sourceTransportFlow Y ρ (t, sourceTransportFlow Φ ρ (t, p)) = p := by
  simp only [sourceTransportFlow, transportCoordinateDilation,
    transportLabelDilation_inv hρ, hY]
  simp [transportLabelDilation, smul_smul, hρ]

/-- The conjugated inverse chart is a right inverse wherever the seed is
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceTransportFlow_right_inverse
    {Φ Y : ℝ × (X × Z) → X × Z} {ρ : ℝ} (hρ : ρ ≠ 0)
    {q : ℝ × (X × Z)}
    (hY : Φ ((transportCoordinateDilation ρ q).1, Y (transportCoordinateDilation ρ q)) =
      (transportCoordinateDilation ρ q).2) :
    sourceTransportFlow Φ ρ (q.1, sourceTransportFlow Y ρ q) = q.2 := by
  change transportLabelDilation ρ⁻¹ (Φ (ρ * q.1,
    transportLabelDilation ρ (transportLabelDilation ρ⁻¹
      (Y (transportCoordinateDilation ρ q))))) = q.2
  rw [transportLabelDilation_inv hρ]
  change transportLabelDilation ρ⁻¹
    (Φ ((transportCoordinateDilation ρ q).1, Y (transportCoordinateDilation ρ q))) = _
  rw [hY]
  simp [transportCoordinateDilation, transportLabelDilation, smul_smul, hρ]

/-- The physical coefficient pulled along the conjugated flow is exactly the
scaled seed characteristic coefficient (`app:ch_background:eq:bg-Nsigma`). -/
theorem flowTransportCoefficient_sourceTransportFlow
    (c : ℝ × (X × Z) → ℝ) (Φ : ℝ × (X × Z) → X × Z)
    {ρ : ℝ} (hρ : ρ ≠ 0) (q : ℝ × (X × Z)) :
    flowTransportCoefficient (fun w ↦ ρ * c (transportCoordinateDilation ρ w))
      (sourceTransportFlow Φ ρ) q =
      ρ * flowTransportCoefficient c Φ (transportCoordinateDilation ρ q) := by
  simp [flowTransportCoefficient, transportCoordinateDilation, sourceTransportFlow,
    transportLabelDilation_inv hρ]

/-- Change of physical time in the published exponential-integral solution.
This is valid for negative as well as positive times
(`app:ch_background:eq:bg-Nsigma`). -/
theorem scalarTransport_source_time (c : ℝ → ℝ) (ρ t : ℝ) :
    scalarTransport (fun s ↦ ρ * c (ρ * s)) 0 ρ t =
      ρ * scalarTransport c 0 1 (ρ * t) := by
  have hi : (∫ s in (0 : ℝ)..t, ρ * c (ρ * s)) = ∫ s in (0 : ℝ)..ρ * t, c s := by
    rw [intervalIntegral.integral_const_mul]
    simpa only [smul_eq_mul, mul_zero] using
      (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := t) c ρ)
  simp only [scalarTransport, transportFactor, hi, mul_one]
  ring

/-- The scaled scalar is the exponential-integral solution with initial scalar
exactly `ρ`, for the conjugated physical flow and footpoint chart. This proves
identification, rather than defining a new solution by pullback
(`app:ch_background:eq:bg-Nsigma`). -/
theorem transportFromFootpoint_sourceTransportFlow
    (c : ℝ × (X × Z) → ℝ) (Φ Y : ℝ × (X × Z) → X × Z)
    {ρ : ℝ} (hρ : ρ ≠ 0) (q : ℝ × (X × Z)) :
    transportFromFootpoint
      (flowTransportCoefficient (fun w ↦ ρ * c (transportCoordinateDilation ρ w))
        (sourceTransportFlow Φ ρ))
      0 (fun _ ↦ ρ) (sourceTransportFlow Y ρ) q =
      ρ * transportFromFootpoint (flowTransportCoefficient c Φ)
        0 (fun _ ↦ 1) Y (transportCoordinateDilation ρ q) := by
  simp only [transportFromFootpoint, characteristicTransport,
    flowTransportCoefficient_sourceTransportFlow c Φ hρ]
  simp only [transportCoordinateDilation, sourceTransportFlow,
    transportCoordinateDilation, transportLabelDilation_inv hρ]
  exact scalarTransport_source_time
    (fun s ↦ flowTransportCoefficient c Φ (s, Y (transportCoordinateDilation ρ q))) ρ q.1

section Regularity

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Smooth coordinate dilation leaves the carrier coordinate unchanged
(`app:ch_background:eq:bg-Nsigma`). -/
theorem contDiff_transportCoordinateDilation (ρ : ℝ) :
    ContDiff ℝ ∞ (transportCoordinateDilation (X := X) (Z := Z) ρ) :=
  (contDiff_const.mul contDiff_fst).prodMk
    ((contDiff_snd.fst.const_smul ρ).prodMk contDiff_snd.snd)

/-- The transformed flow and inverse footpoint are smooth on their literal
inverse-image domains (`app:ch_background:eq:bg-Nsigma`). -/
theorem contDiffOn_sourceTransportFlow {Φ : ℝ × (X × Z) → X × Z}
    {D : Set (ℝ × (X × Z))} (hΦ : ContDiffOn ℝ ∞ Φ D) (ρ : ℝ) :
    ContDiffOn ℝ ∞ (sourceTransportFlow Φ ρ) (transportCoordinateDilation ρ ⁻¹' D) := by
  have h := hΦ.comp (contDiff_transportCoordinateDilation ρ).contDiffOn (fun _ h ↦ h)
  exact (h.fst.const_smul ρ⁻¹).prodMk h.snd

/-- The transformed physical flow solves the normalized direction ODE.
The carrier velocity remains zero (`app:ch_background:eq:bg-Nsigma`). -/
theorem hasDerivAt_sourceTransportFlow
    {Φ : ℝ × (X × Z) → X × Z} {ρ : ℝ} (hρ : ρ ≠ 0)
    {t : ℝ} {p : X × Z} {v : X}
    (hΦ : HasDerivAt (fun s ↦ Φ (s, transportLabelDilation ρ p)) (v, 0) (ρ * t)) :
    HasDerivAt (fun s ↦ sourceTransportFlow Φ ρ (s, p)) (v, 0) t := by
  have hd := hΦ.scomp t ((hasDerivAt_id t).const_mul ρ)
  have hf := (ContinuousLinearMap.fst ℝ X Z).hasFDerivAt.comp_hasDerivAt t hd
  have hs := (ContinuousLinearMap.snd ℝ X Z).hasFDerivAt.comp_hasDerivAt t hd
  have h := (hf.const_smul ρ⁻¹).prodMk hs
  simpa [sourceTransportFlow, transportCoordinateDilation, transportLabelDilation,
    smul_smul, hρ] using h

end Regularity

end JanetCartan.NormalizedBackground.SourceGeometry
