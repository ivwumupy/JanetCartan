module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Sobolev.Coordinates

/-!
# Sobolev decay of the actual inactive carrier multiplier

The generalized full-gap source-shell estimate of
`app:ch_osc:prop:osc-source-shell` on the actual finite-dimensional vector L²
source, for the inactive factors in
`app:ch_response:thm:response-literal-transfer`.

The pointwise envelope jets are primitive inputs, as in the kernel estimate;
their production from Sobolev envelope profiles belongs to the envelope-jet
construction. No spectral tail or Sobolev estimate is assumed here. The mask
is evaluated at the physical covector `η = 2πξ` throughout, including all its
shoulders and bounded-frequency support.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.Localization
namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ I
local notation "H" => Lp V 2 (volume : Measure E)

/-- The source-shell Sobolev estimate for the actual inactive L² multiplier,
from precisely the full physical-frequency gap and phase/envelope jets of
`app:ch_osc:prop:osc-source-shell`. Consumed by the inactive-source assembly of
`app:ch_response:thm:response-literal-transfer`.

The displayed constant is independent of the amplitude and scales `A`, `K`,
and `ρ`. Membership is included so the real-valued Sobolev norm is finite. -/
theorem masked_carrierSource_sobolev {U S : Set E}
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (m : BoundedMask d) (φ : E → ℝ) (f : E → V) (q : ℕ) (s : ℝ)
    (hφ : ContDiffOn ℝ ∞ φ U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport f ⊆ S) {c G A K ρ : ℝ}
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
    let u := m.fourierMultiplier (carrierSource hU ρ φ f hφ hf (hs.trans hSU)
      (hS.of_isClosed_subset (isClosed_tsupport _) hs))
    MemVectorFourierSobolev s u ∧
      vectorFourierSobolevNorm s u ≤
        ((Fintype.card I : ℝ) * m.bound * gapKernelConstant d c G P C q *
          volume.real S * Real.sqrt
            (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
          A * (ρ ^ (s + (d : ℝ) / 2) * (K / ρ) ^ q) := by
  dsimp only
  let u := m.fourierMultiplier (carrierSource hU ρ φ f hφ hf (hs.trans hSU)
    (hS.of_isClosed_subset (isClosed_tsupport _) hs))
  let Hf : E → V := fun ξ ↦ m.symbol ((2 * Real.pi) • ξ) •
    physicalFourierIntegral volume (fun x ↦ carrier ρ φ x • f x)
      (InnerProductSpace.toDual ℝ E ((2 * Real.pi) • ξ))
  have he : (𝓕 u : H) =ᵐ[volume] Hf :=
    masked_carrierSource_fourier_ae hU m ρ φ f hφ hf (hs.trans hSU)
      (hS.of_isClosed_subset (isClosed_tsupport _) hs)
  have hm : AEStronglyMeasurable Hf volume :=
    (Lp.memLp (𝓕 u : H)).aestronglyMeasurable.congr he
  have hB := gapKernelConstant_nonneg (d := d) c G P C hC q
  have hW := m.bound_nonneg
  have hd : ∀ ξ, ‖Hf ξ‖ ≤
      (m.bound * gapKernelConstant d c G P C q * A * volume.real S) *
        (K / (ρ + ‖ξ‖)) ^ q := by
    intro ξ
    have hnorm : ‖ξ‖ ≤ ‖(2 * Real.pi) • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.two_le_pi, norm_nonneg ξ]
    apply (norm_masked_carrier_fourier_of_gap hU hS hSU m φ f q hφ hf hs hc hA hK
      (by linarith) hgap hupper hP hC hphase henv ((2 * Real.pi) • ξ)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left hK (by positivity) (add_le_add le_rfl hnorm)
  have hq' : s + (Module.finrank ℝ E : ℝ) / 2 < q := by simpa using hq
  have hi := integrable_sobolevEnergy_of_scaleRatio hρ hspos hq' hm hd
  obtain ⟨hmem, hnorm⟩ := vectorSobolev_of_fourier_energy s u Hf hm he hi
  refine ⟨hmem, hnorm.trans ?_⟩
  have htail := fourierWeightedL2Norm_le_of_scaleRatio hρ hK hspos hq'
    (by positivity) hm hd
  calc
    _ ≤ (Fintype.card I : ℝ) *
        (((m.bound * gapKernelConstant d c G P C q * A * volume.real S) *
          Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
            (ρ ^ (s + (d : ℝ) / 2) * (K / ρ) ^ q)) :=
      mul_le_mul_of_nonneg_left (by simpa using htail) (Nat.cast_nonneg _)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.Complement.InactiveSource
