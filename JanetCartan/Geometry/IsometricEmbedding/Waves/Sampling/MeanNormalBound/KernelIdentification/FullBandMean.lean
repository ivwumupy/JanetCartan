module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.FullBand

/-!
# The original unmasked mean as a spectator integral

This is the exact column-kernel disintegration of the right side of
`norm_refinedKernelPrefix_mean_le_unmasked`, from
`app:ch_waves:eq:sampling-prefix-normal`. No torus output, transported measure,
normal estimate, or normal matching premise is used.

The continuous square root realizes the *original* weight exactly. Its
smoothness is not asserted. Before applying smooth full-phase calculus, a
smooth angular majorant or a direct weighted cross-kernel argument is still
required, together with the literal normalized forward-kernel identification.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling BackgroundQuadrature ContinuumRow

variable {n J : ℕ} {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
  [LocallyCompactSpace Q]

/-- Operator-norm integrability of the full-band normal over the spectator
follows from the original compact patch and the proved slice identity
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_fullBandKernelOperator_sqrt_normal
    (D : BandKernelData (Fin J × Q) n) (j : Fin J) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B C : ℝ} (hψ : PatchBounds ψ B C) (hc : Continuous ψ) :
    Integrable (fun v : Euclidean 2 ↦
      atomNormal (fullBandKernelOperator D (fun z ↦ (j, q z))
        (continuous_const.prodMk hq) (fun z ↦ Real.sqrt (ψ z))
        (Real.continuous_sqrt.comp hc) j.val B v)) := by
  simp_rw [fullBandKernelOperator_sqrt_normal D _ _ hψ hc]
  exact (carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable
    (integrable_wideBand_patch_normal D j q hq hψ hc)).integral_prod_right

/-- The actual largest-prefix mean is the spectator integral of the constructed
full-band normals, with the original weight and both sharp components already
reassembled (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_refinedKernelPrefix_normal_eq_fullBand
    (D : BandKernelData (Fin J × Q) n) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B C : ℝ} (hψ : PatchBounds ψ B C) (hc : Continuous ψ) :
    (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D J (q z))) =
      ∑ j : Fin J, ∫ v : Euclidean 2,
        atomNormal (fullBandKernelOperator D (fun z ↦ (j, q z))
          (continuous_const.prodMk hq) (fun z ↦ Real.sqrt (ψ z))
          (Real.continuous_sqrt.comp hc) j.val B v) := by
  simp_rw [fullBandKernelOperator_sqrt_normal D _ _ hψ hc]
  exact integral_refinedKernelPrefix_normal_eq_spectator D q hq hψ hc

/-- All charts and colors in the exact unmasked sampling normal are retained
in the full-band disintegration (`app:ch_waves:eq:sampling-prefix-normal`).
The output remains the entire vector-valued Euclidean L² space. -/
theorem sum_integral_refinedKernelPrefix_normal_eq_fullBand
    {A : Type*} [Fintype A] {p : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ : A → Point → ℝ} {B : ℝ} {C : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (C a)) (hc : ∀ a, Continuous (ψ a)) :
    (∑ a, ∑ c, ∫ z : Point, ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) =
      ∑ a, ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
        atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          (fun z ↦ Real.sqrt (ψ a z)) (Real.continuous_sqrt.comp (hc a)) j.val B v) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact integral_refinedKernelPrefix_normal_eq_fullBand (D a) (fun z ↦ (c, z))
    (continuous_const.prodMk continuous_id) (hψ a) (hc a)

/-- Both physical real quadratures of the constructed full band have the
literal factor-four slice normal. The same complex input is regarded as real;
no imaginary input is dropped (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_fullBandKernelOperator_sqrt_normal
    (D : BandKernelData Q n) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B C : ℝ} (hψ : PatchBounds ψ B C) (hc : Continuous ψ)
    (j : ℕ) (v : Euclidean 2) :
    realQuadratureChannel (fullBandKernelOperator D q hq (fun z ↦ Real.sqrt (ψ z))
      (Real.continuous_sqrt.comp hc) j B v) ∘L
      (realQuadratureChannel (fullBandKernelOperator D q hq (fun z ↦ Real.sqrt (ψ z))
        (Real.continuous_sqrt.comp hc) j B v)).adjoint =
      (4 : ℝ) • realOutputCompression
        (∫ s : ℝ, ψ (carrierSamplingEquiv (s, v)) •
          atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v))))) := by
  rw [realQuadratureChannel_normal_eq_four_realPart]
  change (4 : ℝ) • realOutputCompression (atomNormal _) = _
  rw [fullBandKernelOperator_sqrt_normal D q hq hψ hc]

end JanetCartan.Sampling.MeanNormalBound
