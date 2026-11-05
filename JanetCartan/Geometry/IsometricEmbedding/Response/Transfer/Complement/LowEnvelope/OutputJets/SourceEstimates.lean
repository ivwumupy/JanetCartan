module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades

/-!
# Source integration of actual output jets

The primitive mixed grades are inserted into `norm_sourceKernel_le` for
`app:ch_response:thm:response-literal-transfer`. The original compact source set
controls the volume uniformly in the target position and in the output order.
The consumers are the two differentiated graph kernel estimates in `OutputJets`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison JanetCartan.Localization

variable {n r : ℕ}

/-- At a fixed physical covector, the original uniform source cutoff contains
every output jet's support (`app:ch_response:thm:response-literal-transfer`).
No regularity or support condition at other covectors is needed. -/
theorem tsupport_outputJetAmplitude_subset_of_fixed_covector
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) (η : Euclidean n)
    {K : Set (Euclidean n)} (hK : IsClosed K)
    (hs : ∀ x y, y ∉ K → A x y η = 0) (x : Euclidean n) :
    tsupport (fun y ↦ outputJetAmplitude τ α A x y η) ⊆ K := by
  exact tsupport_outputJetAmplitude_subset τ α (fun z y _ ↦ A z y η)
    hK (fun z y _ hy ↦ hs z y hy) x η

/-- Source integration by parts for the constructed output amplitude, derived
from primitive mixed amplitude and target phase jets. This is the quantitative
assembly for `app:ch_response:thm:response-literal-transfer`: the prefactor is
`a * L^b * (ρ + ‖η‖)^|α|`, with `b` fixed independently of the integration
order `q`. The source phase gap and grades are the separate geometric inputs to
`norm_sourceKernel_le`; no modified-amplitude bound is assumed. -/
theorem norm_sourceKernel_outputJetAmplitude_le
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ψ : Euclidean n → ℝ) (τ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (x η : Euclidean n) (α : List (Fin n)) (q b : ℕ)
    (C : ℕ → ℕ → ℝ) (P Q : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    {c G a L ρ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hρ : 0 < ρ) (hLR : L ≤ ρ + ‖η‖)
    (hψ : ContDiffOn ℝ ∞ ψ Ω)
    (hτ : ContDiff ℝ ∞ (fun z ↦ τ z η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hs : ∀ z y, y ∉ K → A z y η = 0)
    (hgap : ∀ y ∈ Ω, c * (ρ + ‖η‖) ≤ ‖fderiv ℝ ψ y‖)
    (hupper : ∀ y ∈ Ω, ‖fderiv ℝ ψ y‖ ≤ G * (ρ + ‖η‖))
    (hψj : ∀ y ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) ψ y‖ ≤ Q j * (ρ + ‖η‖) * L ^ j)
    (hAj : ∀ (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hτj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ τ w η) z‖ ≤ P j * (ρ + ‖η‖) * L ^ (j - 1)) :
    ‖sourceKernel ψ (outputJetAmplitude τ α A) x η‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          (c ^ 2) G Q) (outputJetAmplitudeGrade P C α.length) q 0 *
        ((a * L ^ b * (ρ + ‖η‖) ^ α.length) * (L / (ρ + ‖η‖)) ^ q)) *
          volume.real K := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ ρ + ‖η‖ := add_nonneg hρ.le (norm_nonneg η)
  have hsupport := tsupport_outputJetAmplitude_subset_of_fixed_covector
    τ α A η hK.isClosed hs x
  have hcompact : HasCompactSupport (fun y ↦ outputJetAmplitude τ α A x y η) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hD := outputJetAmplitudeGrade_nonneg P C hP hC α.length
  have hbound := norm_sourceKernel_le hΩ ψ (outputJetAmplitude τ α A) x η q hψ
    ((contDiff_outputJetAmplitude τ α A η hτ hA).comp
      (contDiff_const.prodMk contDiff_id)).contDiffOn
    (hsupport.trans hKΩ) hcompact hc
    (mul_nonneg (mul_nonneg ha (pow_nonneg hL0 b)) (pow_nonneg hR0 α.length))
    hL0 hρ hgap hupper hD (fun y hy j hj ↦ hψj y (hsupport hy) j hj)
    (fun y _ k ↦ (norm_iteratedFDeriv_outputJetAmplitude_le τ A η C P hC hP
      ha hL hLR b hτ hA hAj hτj α k x y).trans_eq (by rw [pow_add]; ring))
  refine hbound.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono hsupport hK.measure_lt_top.ne) ?_)
  have hconstant := transposeDerivativeConstant_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
      (c ^ 2) G Q) hD q 0
  exact mul_nonneg hconstant (mul_nonneg
    (mul_nonneg (mul_nonneg ha (pow_nonneg hL0 b)) (pow_nonneg hR0 α.length))
    (pow_nonneg (div_nonneg hL0 hR0) q))

/-- Above order one, the reverse source phase has exactly the norm of the
forward demodulated target phase jet. The affine Fourier term contributes zero.
This supplies the source phase grades in
`norm_normalMatrixDerivList_reverseDemodulatedKernel_le`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_iteratedFDeriv_reverseSourcePhase_eq_forwardTargetPhase (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (ρ : ℝ) (y η θ x : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ (j + 1) (reverseSourcePhase S φ ρ y η θ) x‖ =
      ‖iteratedFDeriv ℝ (j + 1) (fun z ↦ forwardTargetPhase S φ ρ z η) x‖ := by
  let ℓ : Euclidean n → ℝ := fun z ↦ inner ℝ y η + inner ℝ θ z
  have hℓ : ContDiff ℝ ∞ ℓ := contDiff_const.add (innerSL ℝ θ).contDiff
  have hd : fderiv ℝ ℓ = fun _ ↦ innerSL ℝ θ := by
    funext z
    exact ((innerSL ℝ θ).hasFDerivAt.const_add (inner ℝ y η)).fderiv
  have hz : iteratedFDeriv ℝ (j + 1) ℓ x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hd,
      iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, norm_zero]
  have he : reverseSourcePhase S φ ρ y η θ =
      ℓ - (fun z ↦ forwardTargetPhase S φ ρ z η) := by
    funext z
    simp only [reverseSourcePhase, Pi.sub_apply, ℓ, forwardTargetPhase,
      real_inner_comm θ z]
    ring
  rw [he, iteratedFDeriv_sub_apply (g := fun z ↦ forwardTargetPhase S φ ρ z η) (hℓ.contDiffAt.of_le (by simp))
    ((hS.sub (contDiff_const.mul hφ)).contDiffAt.of_le (by simp)), hz, zero_sub, norm_neg]

end JanetCartan.ResponseTransfer.LowEnvelope
