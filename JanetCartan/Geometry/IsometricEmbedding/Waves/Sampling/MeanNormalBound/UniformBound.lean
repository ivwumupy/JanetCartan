module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformDyadicBound
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.MaskRemoval

/-!
# The literal largest-prefix sampling mean bound

The mask-free proof after `app:ch_waves:eq:sampling-operator-bounds`: remove
the color masks by positivity, reassemble the sharp Hilbert pieces, compare
with smooth angular majorants, and bound the complete dyadic sum before its
compact spectator integral. All constants precede the band count, kernels,
radial/color data and mesh. The output and carrier measures remain Lebesgue.

The primitive gap is required only on nonzero slices of the fixed angular
cutoff. `CanonicalBound` obtains it from the actual full-phase chart theorem;
no gap is imposed at spectators outside the chart. Primitive measured
amplitude matching and uniform jets must still be instantiated on the SAME
`RawPrimary.Construction.fullPrimaryWave` by the sampling parent.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling BackgroundQuadrature ContinuumRow
open NormalComparison ColoredNormalComparison NormalizedFullPhase
open Realization

/-- A vanishing angular slice gives the zero full-band operator directly
from its forward columns. This permits the actual chart gap to be used only
where the measurement cutoff is nonzero
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullBandKernelOperator_eq_zero_of_cutoff_slice
    {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q] [LocallyCompactSpace Q]
    {n : ℕ} (D : BandKernelData Q n) (q : Point → Q) (hq : Continuous q)
    (χ : Point → ℝ) (hχc : Continuous χ) (j : ℕ) (R : ℝ) (v : Euclidean 2)
    (hv : ∀ t, χ (carrierSamplingEquiv (t, v)) = 0) :
    fullBandKernelOperator D q hq χ hχc j R v = 0 := by
  ext1 f
  rw [fullBandKernelOperator_apply]
  simp only [fullBandColumn, hv, zero_smul, smul_zero, integral_zero, zero_apply]

/-- Uniform `O(1)` estimate for the LITERAL largest-prefix colored mean and
its physical `4 Re` normal. The only analytic inputs are primitive chart and
amplitude budgets and phase/amplitude/support matching; neither a whole-row
estimate nor a summed-amplitude estimate is assumed. The gap is restricted
to active angular slices and is produced in `CanonicalBound` from the actual
full-phase charts. Specializing `J = cutoffCount Λ`, the original convolved
window and `h = samplingMesh ε Λ` supplies exactly `hmean` in
`Sampling.exists_threshold_refinedKernelPrefix_realization`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_refinedKernelPrefix_mean_bound
    {A : Type*} [Fintype A] {m p : ℕ}
    {ψ χ : A → Point → ℝ} {B : ℝ} {P R : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    (hχ : ∀ a, PatchBounds (χ a) (R a) 1) (hχc : ∀ a, Continuous (χ a))
    (hplateau : ∀ a z, ψ a z ≠ 0 → χ a z = 1)
    (G : A → UniformNormalGeometry (m + 1) (m + 1)) (C : A → ℕ → ℝ)
    {γ : A → ℝ} (hγ : ∀ a, 0 < γ a) :
    ∃ M > 0, ∀ (J : ℕ)
      (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1))
      (F : (a : A) → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 →
        UniformNormalData (G a) (C a))
      (ε : A → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 → ℝ),
      (∀ a c j v, ε a c j v ∈ Set.Icc 0 (G a).ε₀) →
      (∀ a c (j : Fin J) v,
        ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x,
          (D a).phase (((j, (c, carrierSamplingEquiv (u.1, v))),
            (2 : ℝ) ^ j.val • u.2), x) =
            (2 : ℝ) ^ j.val * (F a c j v).phase (ε a c j v) x
              (fullInputCoordinates m u)) →
      (∀ a c (j : Fin J) v,
        ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x i,
          (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) *
            (χ a (carrierSamplingEquiv (u.1, v)) : ℂ) *
            (Real.sqrt ‖(2 : ℝ) ^ j.val • u.2‖ : ℂ) *
            (D a).mask ((2 : ℝ) ^ j.val • u.2) *
            (D a).amplitude (((j, (c, carrierSamplingEquiv (u.1, v))),
              (2 : ℝ) ^ j.val • u.2), x) i =
          (normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
            (F a c j v).amplitude (ε a c j v) x (fullInputCoordinates m u) i) →
      (∀ a c j v w, w ∉ fullInputDomain m 0 (R a) → ∀ x,
        (F a c j v).amplitude (ε a c j v) x w = 0) →
      (∀ a c j v, (∃ t, χ a (carrierSamplingEquiv (t, v)) ≠ 0) →
        ∀ x ∈ (G a).X₀, ∀ y ∈ (G a).X₀, ∀ u ∈ (G a).D₀,
          γ a ≤ ‖averagedGradient ((F a c j v).phase (ε a c j v)) x y u‖) →
      ∀ (w : ℝ → ℝ), WindowBounds p w 1 → Continuous w → ∀ h : ℝ, h ≠ 0 →
        let E := ∑ a, patchMeanNormal p B (ψ a) w h
          (fun c z ↦ refinedKernelPrefix (D a) J (c, z))
        ‖E‖ ≤ M ∧ ‖(4 : ℝ) • realOutputCompression E‖ ≤ 4 * M := by
  classical
  choose b hb hbound using fun a ↦ exists_uniform_powTwoNormal_bound (G a) (C a) (hγ a)
  let L := ∑ a, ‖P a‖ * ∑ _c : Fin 3 → Fin (p + 1),
    b a * volume.real (Metric.closedBall (0 : Euclidean 2) (2 * R a))
  have hL : 0 ≤ L := Finset.sum_nonneg fun a _ ↦ mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hb a).le (measureReal_nonneg))
  refine ⟨L + 1, by linarith, ?_⟩
  intro J D F ε hε hphase hamplitude hsupport hgap w hw hwc h hh
  have hslice (a : A) (c : Fin 3 → Fin (p + 1)) (v : Euclidean 2) :
      ‖∑ j : Fin J,
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint‖
        ≤ b a := by
    by_cases hv : ∃ t, χ a (carrierSamplingEquiv (t, v)) ≠ 0
    · exact hbound a J (fun j ↦ F a c j v) (fun j ↦ ε a c j v)
        (fun j ↦ hε a c j v) (fun j ↦ hgap a c j v hv)
    · have hz (j : Fin J) :
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
            ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint
              = 0 := by
        apply (samplingOutputConjugation (m + 1)).injective
        rw [map_zero, ← fullBandKernelOperator_normal_eq_uniform (D a)
          (fun z ↦ (j, (c, z)))
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          (χ a) (hχc a) j.val (R a) v (F a c j v) (hε a c j v)
          (hphase a c j v) (hamplitude a c j v) (hsupport a c j v)]
        rw [fullBandKernelOperator_eq_zero_of_cutoff_slice]
        · ext1 f
          rfl
        · simpa only [not_exists, not_not] using hv
      simpa only [hz, Finset.sum_const_zero, norm_zero] using (hb a).le
  have hint (a : A) (c : Fin 3 → Fin (p + 1)) :
      ‖∫ v : Euclidean 2, ∑ j : Fin J,
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint‖
        ≤ b a * volume.real (Metric.closedBall (0 : Euclidean 2) (2 * R a)) := by
    rw [integral_matched_uniformNormal_sum_eq_ball D hχ hχc F ε hε hphase hamplitude hsupport]
    exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top
      (fun v _ ↦ hslice a c v)
  have hfull :
      ‖∑ a, P a • ∑ c : Fin 3 → Fin (p + 1), ∫ v : Euclidean 2, ∑ j : Fin J,
        ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).comp
          ((F a c j v).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint‖
        ≤ L := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ hint a c)) (norm_nonneg _)
  have hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ L + 1 := by
    apply (norm_refinedKernelPrefix_mean_le_unmasked D hw hψ hψc hwc hh).trans
    apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (sum_integral_refinedKernelPrefix_normal_le_uniformNormal D hχ hχc F ε hε
        hphase hamplitude hsupport hψ hψc hplateau) ?_).trans
    · rw [norm_samplingOutputConjugation]
      exact hfull.trans (by linarith)
    · exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun c _ ↦
        integral_nonneg fun z ↦ smul_nonneg ((hψ a).nonneg z) (atomNormal_nonneg _)
  refine ⟨hmean, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left ((realOutputCompression_norm_le _).trans hmean)
    (by norm_num)

end JanetCartan.Sampling.MeanNormalBound
