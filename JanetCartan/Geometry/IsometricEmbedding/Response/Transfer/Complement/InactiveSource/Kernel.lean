module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Multiplier
public import JanetCartan.Analysis.Microlocal.Localization.FourierPhase
public import JanetCartan.Analysis.Microlocal.Localization.Vector
public import JanetCartan.Analysis.Microlocal.Localization.SpectralEstimate
public import JanetCartan.Analysis.Microlocal.Localization.ComplexFubini

/-!
# Full-gap inactive carrier kernels

The generalized source-shell argument of
`app:ch_osc:prop:osc-source-shell`, used for inactive factors in
`app:ch_response:thm:response-literal-transfer`. The mask is arbitrary and
bounded; its entire nonzero region, including shoulders and bounded
frequencies, must have the displayed gap on the source buffer.

These estimates consume pointwise amplitude grades. The implication from the
original all-order Sobolev envelope profile is a separate obligation; these
lemmas alone do not assert the original profile theorem.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
open JanetCartan.Localization
namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [CompleteSpace F]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Exact identification of `Carrier.carrier` with Localization's oscillation
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrier_eq_phaseOscillation (ρ : ℝ) (φ : E → ℝ) :
    carrier ρ φ = phaseOscillation (fun x ↦ ρ * φ x) := by
  funext x
  simp only [carrier, phaseOscillation, mul_comm Complex.I]

omit [CompleteSpace F] in
/-- Fourier kernel of the original carrier, with physical covector η and no
projection of the envelope (`app:ch_response:thm:response-literal-transfer`). -/
theorem physicalFourierIntegral_carrier (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (η : E →L[ℝ] ℝ) :
    physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x) η =
      ∫ x, phaseOscillation (fourierPhase φ ρ η) x • f x := by
  unfold physicalFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_smul]
  congr 1
  simp only [phaseOscillation, carrier, fourierPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The fixed derivative-profile constant in the full-gap estimate
(`app:ch_osc:prop:osc-source-shell`). -/
def gapKernelConstant (d : ℕ) (c G : ℝ) (P C : ℕ → ℝ) (q : ℕ) : ℝ :=
  transposeDerivativeConstant (EuclideanSpace.basisFun (Fin d) ℝ)
    (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin d) ℝ)
      (c ^ 2) (max G 1) P) C q 0

/-- Nonnegativity needed to integrate the full-gap estimate
(`app:ch_osc:prop:osc-source-shell`). -/
theorem gapKernelConstant_nonneg (c G : ℝ) (P C : ℕ → ℝ)
    (hC : ∀ j, 0 ≤ C j) (q : ℕ) : 0 ≤ gapKernelConstant d c G P C q :=
  transposeDerivativeConstant_nonneg _
    (phaseCoefficientDerivativeBound_nonneg _ _ _ _) hC q 0

/-- Integration by parts for a vector carrier at a single inactive physical
covector (`app:ch_osc:prop:osc-source-shell`). Reciprocal coefficient bounds
are derived by Localization, rather than postulated. -/
theorem norm_carrier_fourier_of_gap {U S : Set E}
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (φ : E → ℝ) (f : E → F) (η : E →L[ℝ] ℝ) (q : ℕ)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ S) {c G A K ρ : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hgap : ∀ x ∈ U, c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - η‖)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ j, 0 ≤ C j)
    (hphase : ∀ x ∈ tsupport f, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * K ^ j)
    (henv : ∀ x ∈ tsupport f, ∀ j,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C j * (A * K ^ j)) :
    ‖physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x) η‖ ≤
      (gapKernelConstant d c G P C q * A * volume.real S) *
        (K / (ρ + ‖η‖)) ^ q := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hsU := hs.trans hSU
  have hfc : HasCompactSupport f := hS.of_isClosed_subset (isClosed_tsupport _) hs
  have hψ : ContDiffOn ℝ ∞ (fourierPhase φ ρ η) U :=
    (hφ.const_smul ρ).sub η.contDiff.contDiffOn
  have hb := norm_vector_oscillatory_integral_le (μ := volume) hU e
    (fourierPhase φ ρ η) f q hψ hf hsU hfc (sq_pos_of_pos hc) hA hK
    (add_pos_of_pos_of_nonneg hρ (norm_nonneg _))
    (G := max G 1) (P := P) (C := C)
    (fun x hx ↦ by
      rw [phaseGradientSquare_orthonormalBasis,
        fderiv_fourierPhase φ ρ η ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hc.le (by positivity)) (hgap x hx) 2)
    (fun x hx ↦ norm_fderiv_fourierPhase_le hU φ η hφ hρ.le hx (hupper x hx)) hC
    (fun x hx j hj ↦ by
      rw [norm_iteratedFDeriv_fourierPhase hU φ ρ η hφ (hsU hx) hj, abs_of_pos hρ]
      calc
        _ ≤ ρ * (P j * K ^ j) := mul_le_mul_of_nonneg_left (hphase x hx j hj) hρ.le
        _ ≤ P j * (ρ + ‖η‖) * K ^ j := by
          nlinarith [mul_nonneg (mul_nonneg (hP j) (norm_nonneg η)) (pow_nonneg hK j)]) henv
  rw [physicalFourierIntegral_carrier]
  apply hb.trans
  have hv := measureReal_mono (μ := volume) hs hS.measure_ne_top
  have hB := gapKernelConstant_nonneg (d := d) c G P C hC q
  calc
    _ ≤ (gapKernelConstant d c G P C q *
        (A * (K / (ρ + ‖η‖)) ^ q)) * volume.real S := by
      exact mul_le_mul_of_nonneg_left hv
        (mul_nonneg hB (mul_nonneg hA (pow_nonneg (div_nonneg hK (by positivity)) q)))
    _ = _ := by ring

/-- The entire supplied inactive mask satisfies the pointwise source-shell
bound (`app:ch_response:thm:response-literal-transfer`). No radial support or
high-frequency exclusion is used. -/
theorem norm_masked_carrier_fourier_of_gap {U S : Set E}
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (m : BoundedMask d) (φ : E → ℝ) (f : E → F) (q : ℕ)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ S) {c G A K ρ : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hgap : ∀ η, m.symbol η ≠ 0 → ∀ x ∈ U,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - InnerProductSpace.toDual ℝ E η‖)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ j, 0 ≤ C j)
    (hphase : ∀ x ∈ tsupport f, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * K ^ j)
    (henv : ∀ x ∈ tsupport f, ∀ j,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C j * (A * K ^ j)) (η : E) :
    ‖m.symbol η • physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x)
      (InnerProductSpace.toDual ℝ E η)‖ ≤
      (m.bound * gapKernelConstant d c G P C q * A * volume.real S) *
        (K / (ρ + ‖η‖)) ^ q := by
  have hB := gapKernelConstant_nonneg (d := d) c G P C hC q
  have hW := m.bound_nonneg
  by_cases hz : m.symbol η = 0
  · rw [hz, zero_smul, norm_zero]
    positivity
  · rw [norm_smul]
    have hb := norm_carrier_fourier_of_gap hU hS hSU φ f
      (InnerProductSpace.toDual ℝ E η) q hφ hf hs hc hA hK hρ
      (by simpa only [LinearIsometryEquiv.norm_map] using hgap η hz)
      hupper hP hC hphase henv
    simp only [LinearIsometryEquiv.norm_map] at hb
    exact (mul_le_mul (m.norm_le η) hb (norm_nonneg _) m.bound_nonneg).trans_eq (by ring)

/-- Weighted integrability and the full-gap spectral tail are conclusions of
the primitive jet and gap bounds (`app:ch_osc:eq:osc-source-tail`). This
intermediate estimate uses unnormalized physical Fourier integrals. -/
theorem masked_carrier_spectral_tail {U S : Set E}
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (m : BoundedMask d) (φ : E → ℝ) (f : E → F) (q : ℕ)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ S) {c G A K ρ s : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hK : 0 ≤ K) (hρ : 1 ≤ ρ)
    (hspos : 0 ≤ s) (hq : s + (d : ℝ) / 2 < q)
    (hgap : ∀ η, m.symbol η ≠ 0 → ∀ x ∈ U,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - InnerProductSpace.toDual ℝ E η‖)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ j, 0 ≤ C j)
    (hphase : ∀ x ∈ tsupport f, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * K ^ j)
    (henv : ∀ x ∈ tsupport f, ∀ j,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C j * (A * K ^ j)) :
    let H := fun η ↦ m.symbol η • physicalFourierIntegral volume
      (fun x ↦ carrier ρ φ x • f x) (InnerProductSpace.toDual ℝ E η)
    Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖H η‖ ^ 2) ∧
      fourierWeightedL2Norm volume s H ≤
        (m.bound * gapKernelConstant d c G P C q * A * volume.real S *
          Real.sqrt (∫ η : E, (1 + ‖η‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
        (ρ ^ (s + (d : ℝ) / 2) * (K / ρ) ^ q) := by
  dsimp only
  have hfc : HasCompactSupport f := hS.of_isClosed_subset (isClosed_tsupport _) hs
  have hi : Integrable (fun x ↦ carrier ρ φ x • f x) := by
    rw [carrier_eq_phaseOscillation]
    exact integrable_phaseOscillation_smul hU _ f (hφ.const_smul ρ) hf (hs.trans hSU) hfc
  have hm : AEStronglyMeasurable (fun η ↦ m.symbol η •
      physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x)
        (InnerProductSpace.toDual ℝ E η)) volume :=
    (m.measurable.aestronglyMeasurable (μ := volume)).smul
    (((continuous_physicalFourierIntegral volume hi).comp
      (InnerProductSpace.toDual ℝ E).continuous).aestronglyMeasurable)
  have hd := norm_masked_carrier_fourier_of_gap hU hS hSU m φ f q hφ hf hs hc hA hK
    (by linarith) hgap hupper hP hC hphase henv
  have hq' : s + (Module.finrank ℝ E : ℝ) / 2 < q := by simpa using hq
  have hB := gapKernelConstant_nonneg (d := d) c G P C hC q
  have hW := m.bound_nonneg
  refine ⟨integrable_sobolevEnergy_of_scaleRatio hρ hspos hq' hm hd, ?_⟩
  simpa using fourierWeightedL2Norm_le_of_scaleRatio hρ hK hspos hq'
    (by positivity) hm hd

end JanetCartan.ResponseTransfer.Complement.InactiveSource
