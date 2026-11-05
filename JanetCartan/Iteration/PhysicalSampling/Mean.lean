module

public import JanetCartan.Iteration.PhysicalSampling.Normal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformBound

/-!
# Reassemble the same scalar full-band normal into the actual sampling mean

This deduction consumes the scalar family constructed from the original current
immersion in `FullGeometry`, not a measured-stress row. Every smooth band and both
sharp Hilbert refinements stay on the original grouped input. The original patch
weight and colored window are removed only by positivity. The resulting bound
has no band-count or individual-channel square-root loss.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation FullPhaseCharts
open Sampling Sampling.RawKernel Sampling.MeasuredAmplitude Sampling.MeanNormalBound
open Sampling.MeanNormalBound.NormalizedFullPhase Sampling.MeanNormalBound.CanonicalGap
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition PhysicalMean ContinuumRow
open NormalComparison ColoredNormalComparison SeparatedSampling Sampling.Realization

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (χ : ContDiffBump (0 : Euclidean (m + 1)))
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
  (Bdet : ℝ) (hBdet : 0 ≤ Bdet) (hdB : ∀ η, ‖detectorMask angular H η‖ ≤ Bdet)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => retainedScalarKernelData (J := J) T Q χ a hρ hP hcarrier
  angular H ha hH hH₀ Bdet hBdet hdB τ hτ₀

/-- The original scalar full-normal family controls the SAME weighted sampling
mean and both real quadratures. The family and its uniform sum are produced in
`FullGeometry`; the actual original-data application must retain that family,
all masks, and the sampling nodes unchanged (`new:eq:amplitude-test`). -/
theorem retainedScalarKernelData_mean_le
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall a.1 (ρ / 2))
    (ψ : Point → ℝ) {B : ℝ} (hψ : PatchBounds ψ B 1) (hψc : Continuous ψ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (hscale : ∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ))
    {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}
    {Cmean : ℝ} (hCmean : 0 ≤ Cmean)
    (hfamily : ∀ v : Euclidean 2, (∃ t, ψ (carrierSamplingEquiv (t, v)) ≠ 0) →
      ∃ Ns : ℕ → UniformNormalData G Cnormal,
        (∀ j, (Ns j).phase = fun ε x u ↦
          normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u)) ∧
        (∀ j, (Ns j).amplitude = fun ε x u ↦
          (scalarNormalizedAmplitude T χ ψ angular H j (ε, v, x, u)).ofLp) ∧
        ∀ (J' : ℕ) (ε : Fin J' → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
          ‖∑ j : Fin J', ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Cmean)
    (hε : ∀ color (j : Fin J), (τ color) * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (φ : Point → ℝ) (Bφ Pφ : ℝ) (hφ : PatchBounds φ Bφ Pφ) (hφc : Continuous φ)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (w : ℝ → ℝ) (hw : WindowBounds p w 1) (hwc : Continuous w) {h : ℝ} (hh : h ≠ 0) :
    let Emean := patchMeanNormal p Bφ φ w h
      (fun color z ↦ refinedKernelPrefix (D) J (color, z))
    let Ccolored := ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
      Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B))
    ‖Emean‖ ≤ Ccolored ∧ ‖(4 : ℝ) • realOutputCompression Emean‖ ≤ 4 * Ccolored := by
  classical
  dsimp only
  let Op := fun (color : Fin 3 → Fin (p + 1)) (j : Fin J) (v : Euclidean 2) ↦
    fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) ψ hψc j.val B v
  have hslice (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2) :
      ‖∑ j : Fin J, atomNormal (Op color j v)‖ ≤ Cmean := by
    by_cases hv : ∃ t, ψ (carrierSamplingEquiv (t, v)) ≠ 0
    · obtain ⟨Ns, hNp, hNa, hNsbound⟩ := hfamily v hv
      have hnormal (j : Fin J) := retainedScalarKernelData_normal_eq_uniform
        T Q χ a hρ hP hcarrier angular H ha hH hH₀ Bdet hBdet hdB τ hτ₀
        hphase hχ ψ hψ hψc hψgraph hψchart j color v (hscale color j)
        (Ns j.val) (hNp j.val) (hNa j.val) (hε color j)
      have heq : (∑ j : Fin J, atomNormal (Op color j v)) =
          samplingOutputConjugation (m + 1) (∑ j : Fin J,
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
              ((τ color) * (2 : ℝ) ^ j.val)).comp
              ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
                ((τ color) * (2 : ℝ) ^ j.val)).adjoint) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ ↦ hnormal j)
      rw [heq, norm_samplingOutputConjugation]
      exact hNsbound J (fun j ↦ τ color * (2 : ℝ) ^ j.val) (hε color)
    · have hz (j : Fin J) : Op color j v = 0 :=
        fullBandKernelOperator_eq_zero_of_cutoff_slice (D) _ _ ψ hψc
          j.val B v (by simpa only [not_exists, not_not] using hv)
      simpa only [hz, atomNormal, map_zero, ContinuousLinearMap.zero_comp,
        Finset.sum_const_zero, norm_zero] using hCmean
  have hi (color : Fin 3 → Fin (p + 1)) (j : Fin J) :
      Integrable (fun v : Euclidean 2 ↦ atomNormal (Op color j v)) :=
    integrable_fullBandKernelOperator_cutoff_normal (D) j (fun z ↦ (color, z))
      (continuous_const.prodMk continuous_id) hψ hψc
  have hint (color : Fin 3 → Fin (p + 1)) :
      ‖∑ j : Fin J, ∫ v : Euclidean 2, atomNormal (Op color j v)‖ ≤
        Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B)) := by
    rw [← integral_finsetSum _ (fun j _ ↦ hi color j)]
    have heq : (∫ v : Euclidean 2, ∑ j : Fin J, atomNormal (Op color j v)) =
        ∫ v in closedBall (0 : Euclidean 2) (2 * B),
          ∑ j : Fin J, atomNormal (Op color j v) := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro v hv
      apply Finset.sum_eq_zero
      intro j _
      have hz : Op color j v = 0 := fullBandKernelOperator_eq_zero_off_spectator_ball
        (D) _ _ hψ hψc j.val hv
      simp only [hz, atomNormal, map_zero, ContinuousLinearMap.zero_comp]
    rw [heq]
    exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top
      (fun v _ ↦ hslice color v)
  have horder : (∑ color : Fin 3 → Fin (p + 1), ∫ z : Point,
      φ z • atomNormal (refinedKernelPrefix (D) J (color, z))) ≤
      Pφ • ∑ color : Fin 3 → Fin (p + 1), ∑ j : Fin J,
        ∫ v : Euclidean 2, atomNormal (Op color j v) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum fun color _ ↦
      integral_refinedKernelPrefix_normal_le_cutoff_fullBand (D) (fun z ↦ (color, z))
        (continuous_const.prodMk continuous_id) hφ hφc hψ hψc hplateau
  have hmean : ‖patchMeanNormal p Bφ φ w h
      (fun color z ↦ refinedKernelPrefix (D) J (color, z))‖ ≤
      ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
        Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B)) := by
    have hmask := norm_refinedKernelPrefix_mean_le_unmasked
      (A := Unit) (fun _ ↦ (D)) hw (fun _ ↦ hφ) (fun _ ↦ hφc) hwc hh
    simp only [Fintype.sum_unique] at hmask
    apply hmask.trans
    apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg horder ?_).trans
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun color _ ↦ hint color)) (norm_nonneg _)
    · exact Finset.sum_nonneg fun color _ ↦ integral_nonneg fun z ↦
        smul_nonneg (hφ.nonneg z) (atomNormal_nonneg _)
  refine ⟨hmean, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left ((realOutputCompression_norm_le _).trans hmean) (by norm_num)

end JanetCartan.PhysicalSampling
