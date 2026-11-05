module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.SpectatorSupport

/-!
# The unmasked sampling mean and the actual full-phase normals

This assembles the literal Euclidean bridge needed on the unmasked right side
of `norm_refinedKernelPrefix_mean_le_unmasked`, in the mask-free proof after
`app:ch_waves:eq:sampling-operator-bounds`. Both sharp components are reassembled
before the full-phase identification. The finite band sum is inside the
spectator integral, so the consumer can estimate the sum by frequency overlap.

The only matching inputs are pointwise phase, measured amplitude, and input
support identities. They include the transverse square-root Jacobian, the
half derivative, and the actual Fourier normalization. Their producers are
`RawPrimary.Construction.fullPrimaryWave`, `Leading`, and `FullPhaseCharts`;
the sampling parent retains their same-object instantiation. All normal
identities and operator-valued integrability are deductions from these inputs.
The smooth cutoff is constructed in `SmoothMajorant` before any band or color.
The original weight is kept on the left of the comparison.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling BackgroundQuadrature ContinuumRow
open NormalComparison ColoredNormalComparison NormalizedFullPhase

private theorem samplingOutputConjugation_real_smul {n : ℕ} (t : ℝ)
    (X : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    samplingOutputConjugation n (t • X) = t • samplingOutputConjugation n X :=
  ((samplingOutputConjugation n).toContinuousLinearMap.restrictScalars ℝ).map_smul t X

variable {A : Type*} [Fintype A] {m J p : ℕ}
  (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1))
  {χ : A → Point → ℝ} {R : A → ℝ}
  (hχ : ∀ a, PatchBounds (χ a) (R a) 1) (hχc : ∀ a, Continuous (χ a))
  {G : A → UniformNormalGeometry (m + 1) (m + 1)} {C : A → ℕ → ℝ}
  (F : (a : A) → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 →
    UniformNormalData (G a) (C a))
  (ε : A → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 → ℝ)
  (hε : ∀ a c j v, ε a c j v ∈ Set.Icc 0 (G a).ε₀)
  (hphase : ∀ a c (j : Fin J) v,
    ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x,
      (D a).phase (((j, (c, carrierSamplingEquiv (u.1, v))),
        (2 : ℝ) ^ j.val • u.2), x) =
        (2 : ℝ) ^ j.val * (F a c j v).phase (ε a c j v) x (fullInputCoordinates m u))
  (hamplitude : ∀ a c (j : Fin J) v,
    ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x i,
      (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) *
        (χ a (carrierSamplingEquiv (u.1, v)) : ℂ) *
        (Real.sqrt ‖(2 : ℝ) ^ j.val • u.2‖ : ℂ) * (D a).mask ((2 : ℝ) ^ j.val • u.2) *
        (D a).amplitude (((j, (c, carrierSamplingEquiv (u.1, v))),
          (2 : ℝ) ^ j.val • u.2), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        (F a c j v).amplitude (ε a c j v) x (fullInputCoordinates m u) i)
  (hsupport : ∀ a c j v w, w ∉ fullInputDomain m 0 (R a) → ∀ x,
    (F a c j v).amplitude (ε a c j v) x w = 0)

omit [Fintype A] in
include hχ hχc hε hphase hamplitude hsupport in
/-- Every actual full-phase normal is Bochner integrable in the literal
Lebesgue spectator variable. Compact patch bounds and the proved column
identification supply integrability; it is not an additional analytic premise
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_matched_uniformNormal (a : A) (c : Fin 3 → Fin (p + 1)) (j : Fin J) :
    Integrable (fun v : Euclidean 2 ↦
      ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  apply (integrable_samplingOutputConjugation_iff _).mp
  have h := integrable_fullBandKernelOperator_cutoff_normal (D a) j (fun z ↦ (c, z))
    (continuous_const.prodMk continuous_id) (hχ a) (hχc a)
  have he (v : Euclidean 2) := fullBandKernelOperator_normal_eq_uniform (D a)
    (fun z ↦ (j, (c, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (χ a) (hχc a) j.val (R a) v (F a c j v) (hε a c j v)
    (hphase a c j v) (hamplitude a c j v) (hsupport a c j v)
  simpa only [he] using h

omit [Fintype A] in
include hχ hχc hε hphase hamplitude hsupport in
/-- The entire finite band sum is integrable before it is estimated. This
places frequency overlap inside the spectator integral, as required by the
mask-free proof of `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem integrable_matched_uniformNormal_sum (a : A) (c : Fin 3 → Fin (p + 1)) :
    Integrable (fun v : Euclidean 2 ↦ ∑ j : Fin J,
      ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) :=
  integrable_finsetSum _ (fun j _ ↦
    integrable_matched_uniformNormal D hχ hχc F ε hε hphase hamplitude hsupport a c j)

omit [Fintype A] in
include hχ hχc hε hphase hamplitude hsupport in
/-- The actual uniform normal vanishes off the fixed spectator ball selected
with the angular cutoff. Its support is derived from the full-band forward
kernel, and is uniform in all bands and colors
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem matched_uniformNormal_eq_zero_off_spectator_ball
    (a : A) (c : Fin 3 → Fin (p + 1)) (j : Fin J) (v : Euclidean 2)
    (hv : v ∉ Metric.closedBall 0 (2 * R a)) :
    ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
      ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint = 0 := by
  apply (samplingOutputConjugation (m + 1)).injective
  rw [map_zero, ← fullBandKernelOperator_normal_eq_uniform (D a) (fun z ↦ (j, (c, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (χ a) (hχc a) j.val (R a) v (F a c j v) (hε a c j v)
    (hphase a c j v) (hamplitude a c j v) (hsupport a c j v)]
  rw [fullBandKernelOperator_eq_zero_off_spectator_ball (D a) _ _ (hχ a) (hχc a) j.val hv]
  ext1 f
  rfl

omit [Fintype A] in
include hχ hχc hε hphase hamplitude hsupport in
/-- The spectator integral of the whole band sum is a literal integral over
one fixed finite-volume ball, not an integral of a constant over all of
Euclidean space. This is the support identity needed when the parent applies
its uniform dyadic estimate (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem integral_matched_uniformNormal_sum_eq_ball
    (a : A) (c : Fin 3 → Fin (p + 1)) :
    (∫ v : Euclidean 2, ∑ j : Fin J,
      ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) =
      ∫ v in Metric.closedBall (0 : Euclidean 2) (2 * R a), ∑ j : Fin J,
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint := by
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  exact Finset.sum_eq_zero fun j _ ↦ matched_uniformNormal_eq_zero_off_spectator_ball
    D hχ hχc F ε hε hphase hamplitude hsupport a c j v hv

include hχ hχc hε hphase hamplitude hsupport in
/-- Exact identification of the smooth majorant's full-band sum with the
actual full-phase normal sum. The output coordinate conjugation is isometric;
the spectator measure is still Lebesgue measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_integral_fullBand_normal_eq_uniformNormal (P : A → ℝ) :
    (∑ a, P a • ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
      atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (χ a) (hχc a) j.val (R a) v)) =
      samplingOutputConjugation (m + 1)
        (∑ a, P a • ∑ c, ∫ v : Euclidean 2, ∑ j : Fin J,
          ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).comp
              ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [samplingOutputConjugation_real_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_finsetSum _ (fun j _ ↦
    integrable_matched_uniformNormal D hχ hχc F ε hε hphase hamplitude hsupport a c j),
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [samplingOutputConjugation_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  exact fullBandKernelOperator_normal_eq_uniform (D a) (fun z ↦ (j, (c, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (χ a) (hχc a) j.val (R a) v (F a c j v) (hε a c j v)
    (hphase a c j v) (hamplitude a c j v) (hsupport a c j v)

include hχ hχc hε hphase hamplitude hsupport in
/-- The norm of the whole smooth full-band sum is preserved, including all
chart weights and colors. This is an exact coordinate identity, not an
oscillatory estimate (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_sum_integral_fullBand_normal_eq_uniformNormal (P : A → ℝ) :
    ‖∑ a, P a • ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
      atomNormal (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (χ a) (hχc a) j.val (R a) v)‖ =
      ‖∑ a, P a • ∑ c, ∫ v : Euclidean 2, ∑ j : Fin J,
        ((F a c j v).uniformOscillatoryOperator
          ((2 : ℝ) ^ j.val) (ε a c j v)).comp
            ((F a c j v).uniformOscillatoryOperator
          ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint‖ := by
  rw [sum_integral_fullBand_normal_eq_uniformNormal D hχ hχc F ε hε hphase
    hamplitude hsupport P, norm_samplingOutputConjugation]

include hχ hχc hε hphase hamplitude hsupport in
/-- Operator-order domination of the *original* unmasked mean by the actual
smooth full-phase normal sum, retaining every original band and color. This
is the bridge consumed after `norm_refinedKernelPrefix_mean_le_unmasked`.
No regularity of `sqrt ψ`, normal estimate, or normal-matching premise is used
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem sum_integral_refinedKernelPrefix_normal_le_uniformNormal
    {ψ : A → Point → ℝ} {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hplateau : ∀ a z, ψ a z ≠ 0 → χ a z = 1) :
    (∑ a, ∑ c, ∫ z : Point,
      ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) ≤
      samplingOutputConjugation (m + 1)
        (∑ a, P a • ∑ c, ∫ v : Euclidean 2, ∑ j : Fin J,
          ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).comp
              ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  rw [← sum_integral_fullBand_normal_eq_uniformNormal D hχ hχc F ε hε hphase
    hamplitude hsupport P]
  exact sum_integral_refinedKernelPrefix_normal_le_cutoff_fullBand D hψ hψc hχ hχc hplateau

omit [Fintype A] in
include hε hphase hamplitude hsupport in
/-- Both physical quadratures of the full smooth band have the actual full
normal and the exact factor four. The entire complex input is regarded as
real; no input quadrature is removed (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_fullBandKernelOperator_normal_eq_uniformNormal
    (a : A) (c : Fin 3 → Fin (p + 1)) (j : Fin J) (v : Euclidean 2) :
    realQuadratureChannel (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (χ a) (hχc a) j.val (R a) v) ∘L
      (realQuadratureChannel (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (χ a) (hχc a) j.val (R a) v)).adjoint =
      samplingRealNormal (m + 1)
        (((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  rw [realQuadratureChannel_normal_eq_four_realPart]
  change (4 : ℝ) • realOutputCompression (atomNormal _) = _
  rw [fullBandKernelOperator_normal_eq_uniform (D a) (fun z ↦ (j, (c, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (χ a) (hχc a) j.val (R a) v (F a c j v) (hε a c j v)
    (hphase a c j v) (hamplitude a c j v) (hsupport a c j v)]
  rfl

include hχ hχc hε hphase hamplitude hsupport in
/-- The physical full-band sum, using the actual real adjoints and both input
quadratures, is the spectator integral of the full-phase sum followed by the
exact `4 Re` map. All integral interchanges use the proved compact-support
integrability (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_integral_real_fullBand_normal_eq_uniformNormal (P : A → ℝ) :
    (∑ a, P a • ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2,
      realQuadratureChannel (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (χ a) (hχc a) j.val (R a) v) ∘L
        (realQuadratureChannel (fullBandKernelOperator (D a) (fun z ↦ (j, (c, z)))
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          (χ a) (hχc a) j.val (R a) v)).adjoint) =
      samplingRealNormal (m + 1)
        (∑ a, P a • ∑ c, ∫ v : Euclidean 2, ∑ j : Fin J,
          ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).comp
              ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_finsetSum _ (fun j _ ↦
    integrable_matched_uniformNormal D hχ hχc F ε hε hphase hamplitude hsupport a c j),
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [samplingRealNormal_integral
    (integrable_matched_uniformNormal D hχ hχc F ε hε hphase hamplitude hsupport a c j)]
  apply integral_congr_ae
  filter_upwards [] with v
  exact real_fullBandKernelOperator_normal_eq_uniformNormal D hχc F ε hε hphase
    hamplitude hsupport a c j v

end JanetCartan.Sampling.MeanNormalBound
