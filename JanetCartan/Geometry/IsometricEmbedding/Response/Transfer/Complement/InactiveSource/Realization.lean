module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Kernel

/-!
# The original carrier as an actual L² source

The supplied compact envelope in `app:ch_response:thm:response-literal-transfer`
is modulated before applying the inactive Fourier factor. This module proves
source membership, Fourier identification, and the physical cutoff plateaus
for this same source, with no projection of the envelope.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
open JanetCartan.Localization
namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Local smoothness on a buffer of the entire envelope support gives global
smoothness of the original carrier source
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_carrier_source {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ (fun x ↦ carrier ρ φ x • f x) := by
  rw [carrier_eq_phaseOscillation]
  apply contDiff_of_contDiffOn_support_neighborhood hU _
    ((tsupport_smul_subset_right _ _).trans hs)
  have ho : ContDiffOn ℝ ∞ (phaseOscillation (fun x ↦ ρ * φ x)) U :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ.const_smul ρ)).mul
      contDiffOn_const).cexp
  exact ho.smul hf

/-- The original compactly supported carrier is genuinely in L²
(`app:ch_response:thm:response-literal-transfer`). -/
theorem memLp_carrier_source {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f) :
    MemLp (fun x ↦ carrier ρ φ x • f x) 2 volume :=
  (contDiff_carrier_source hU ρ φ f hφ hf hs).continuous.memLp_of_hasCompactSupport
    hc.smul_left

/-- The actual original supported carrier as a Euclidean L² class in
`app:ch_response:thm:response-literal-transfer`. -/
def carrierSource {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f) : H :=
  (memLp_carrier_source hU ρ φ f hφ hf hs hc).toLp _

/-- The constructed L² source retains its original modulated representative
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierSource_ae {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f) :
    carrierSource hU ρ φ f hφ hf hs hc =ᵐ[volume] fun x ↦ carrier ρ φ x • f x :=
  (memLp_carrier_source hU ρ φ f hφ hf hs hc).coeFn_toLp

/-- A cutoff plateau on the envelope support is a plateau on the constructed
L² carrier (`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierSource_plateau {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f)
    (χ : BoundedMask d) (hχ : ∀ x ∈ tsupport f, χ.symbol x = 1) :
    ∀ᵐ x ∂volume, carrierSource hU ρ φ f hφ hf hs hc x ≠ 0 → χ.symbol x = 1 := by
  filter_upwards [carrierSource_ae hU ρ φ f hφ hf hs hc] with x hx hne
  rw [hx] at hne
  exact χ.carrier_plateau f ρ φ (fun y hy ↦ hχ y (subset_tsupport f hy)) x hne

variable [CompleteSpace F]

/-- The ordinary carrier Fourier integral represents its L² transform at the
physical covector `η = 2πξ`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierSource_fourier_ae {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f) :
    (𝓕 (carrierSource hU ρ φ f hφ hf hs hc) : H) =ᵐ[volume]
      fun ξ ↦ physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x)
        (InnerProductSpace.toDual ℝ E ((2 * Real.pi) • ξ)) := by
  have hi : Integrable (fun x ↦ carrier ρ φ x • f x) :=
    (contDiff_carrier_source hU ρ φ f hφ hf hs).continuous.integrable_of_hasCompactSupport
      hc.smul_left
  have he := carrierSource_ae hU ρ φ f hφ hf hs hc
  have hFourier := fourierTransform_coeFn_ae_integral_hilbert
    (carrierSource hU ρ φ f hφ hf hs hc) (hi.congr he.symm)
  filter_upwards [hFourier] with ξ hξ
  rw [hξ, Real.fourier_congr_ae he]
  rw [physicalFourierIntegral_eq_fourier, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- The actual inactive L² factor has the literal masked carrier Fourier
representative, with physical normalization retained
(`app:ch_response:thm:response-literal-transfer`). -/
theorem masked_carrierSource_fourier_ae {U : Set E} (hU : IsOpen U)
    (m : BoundedMask d) (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f) :
    (𝓕 (m.fourierMultiplier (carrierSource hU ρ φ f hφ hf hs hc)) : H) =ᵐ[volume]
      fun ξ ↦ m.symbol ((2 * Real.pi) • ξ) •
        physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x)
          (InnerProductSpace.toDual ℝ E ((2 * Real.pi) • ξ)) := by
  filter_upwards [m.fourierMultiplier_fourier_ae (carrierSource hU ρ φ f hφ hf hs hc),
    carrierSource_fourier_ae hU ρ φ f hφ hf hs hc] with ξ h₁ h₂
  rw [h₁, h₂]

/-- Exact `A₊-I` on the same original carrier, under physical cutoff plateaus
on its envelope support (`app:ch_response:thm:response-literal-transfer`). -/
theorem localized_carrierSource_sub_identity {U : Set E} (hU : IsOpen U)
    (m χout χin : BoundedMask d) (ρ : ℝ) (φ : E → ℝ) (f : E → F)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ U) (hc : HasCompactSupport f)
    (hin : ∀ x ∈ tsupport f, χin.symbol x = 1)
    (hout : ∀ x ∈ tsupport f, χout.symbol x = 1) :
    let u := carrierSource hU ρ φ f hφ hf hs hc
    m.localized χout χin u - u = -χout.multiply (m.complement.fourierMultiplier u) :=
  m.localized_sub_identity χout χin _
    (carrierSource_plateau hU ρ φ f hφ hf hs hc χin hin)
    (carrierSource_plateau hU ρ φ f hφ hf hs hc χout hout)

end JanetCartan.ResponseTransfer.Complement.InactiveSource
