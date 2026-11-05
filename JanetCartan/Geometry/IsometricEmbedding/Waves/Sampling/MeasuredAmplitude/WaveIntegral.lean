module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MatrixRepresentation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.IntegralSum

/-!
# The measured polynomial integral is the actual raw wave derivative

The consumer is the sharp sampling-band estimate, before passing to its L²
norm. The polynomial, original smooth bands and tensor measurement are those
already used by the retained kernel construction. Differentiation of the raw
wave and integrability come from the existing raw-family results. No equality
of operators or estimate is assumed. All coefficients below are the SAME
retained leading and correction fields (`app:ch_waves:eq:individual-representation`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open RawInputPartition RawPrimary.SliceBounds RawKernel

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℂ]
    EuclideanSpace ℂ (Fin n)) (χ : Euclidean n → ℝ)
  {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
  (hΩ : IsOpen Ω) (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
  (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
  (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
  (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
  (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
  {τ : ℝ} (hτ : τ ≠ 0)

include hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ in
/-- Identify the nonzero measured polynomial with the original derivative
amplitude on its retained working domain. The four smooth coefficients are
outputs of the retained reconstruction, not a polynomial-matching premise
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem fullMeasuredDerivativePolynomial_eq_amplitude
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ τ w.2.1 w.1 w.2.2 =
      (χ w.1 : ℂ) • measurement w.1
        (fullDerivativeAmplitude T Q F row col Φ Y r τ w) := by
  unfold fullMeasuredDerivativePolynomial
  rw [fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r hτ
    (((contDiffOn_fullPhase T Q hphase).contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
    ((hν₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
    ((hν₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
    ((hV₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
    ((hV₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))]

private theorem wideBand_subset_ceiling (j : Fin J) :
    wideBand n j.val ⊆ closedBall 0 ((2 : ℝ) ^ J) := by
  apply Subset.trans sdiff_subset
  apply closedBall_subset_closedBall
  have hpow : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [dyadicScale]
  rw [pow_succ] at hpow
  linarith

variable (z : Euclidean 3) {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
  (hζ : T.reference.spatialPatch z ∈ V)
  (hproduct : ∀ q ∈ X ×ˢ V, (q.1, (z, q.2)) ∈ Ω)
  (hshift : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ J), T.reference.spatialPatch z + τ • η ∈ V)
  {d : Euclidean (n - 1) → ℂ} {Md : ℝ}
  (hd : Measurable d) (hdb : ∀ η, ‖d η‖ ≤ Md)

include hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ hζ hproduct hshift hd hdb in
/-- Pass the SAME tensor measurement through each original smooth-band
integral. The polynomial is identified only where that band contributes;
the actual compact-band integrability is proved before commuting the
measurement with the Bochner integral
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem rawSliceBandIntegral_measuredPolynomial
    (j : Fin J) (f : WideBandL2 n j.val) {x : Euclidean n}
    (hx : χ x ≠ 0 → x ∈ X) :
    rawSliceBandIntegral (phase T Q)
      (fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ τ z)
      (fun _ ↦ 1) (T.reference.spatialPatch z) τ (weightedRadialBand d j.val) j.val f x =
      (χ x : ℂ) • measurement x
        (rawSliceBandIntegral (phase T Q)
          (fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, η)))
          (fun _ ↦ 1) (T.reference.spatialPatch z) τ
          (weightedRadialBand d j.val) j.val f x) := by
  by_cases hχ : χ x = 0
  · simp [rawSliceBandIntegral, rawPrimaryDemodulatedIntegral,
      fullMeasuredDerivativePolynomial, hχ]
  have hxX := hx hχ
  have hmap : ContDiffOn ℝ ∞
      (fun q : Euclidean n × Euclidean (n - 1) ↦ (q.1, (z, q.2))) (X ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
  have hS := (contDiffOn_fullPhase T Q hphase).comp hmap hproduct
  have hA := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ).2.comp hmap hproduct
  have hsh : ∀ η ∈ wideBand n j.val, T.reference.spatialPatch z + τ • η ∈ V :=
    fun η hη ↦ hshift η (wideBand_subset_ceiling j hη)
  have hatom := (contDiffOn_rawPrimaryDemodulatedAtom
    (A := fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, η)))
    hS hA hζ hsh).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun η hη ↦ ⟨hxX, hη⟩)
  have hi := integrable_weightedWideBand_atom hd hdb j.val f _ hatom
  have hi' : Integrable (fun η ↦
      Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
        (T.reference.spatialPatch z) τ x η : ℂ)) •
        (((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η * f η) •
          fullDerivativeAmplitude T Q F row col Φ Y r τ
            (x, (z, T.reference.spatialPatch z + τ • η)))) := by
    exact hi.congr (Filter.Eventually.of_forall fun η ↦ smul_comm _ _ _)
  simp only [rawSliceBandIntegral, Complex.ofReal_one, one_smul]
  unfold rawPrimaryDemodulatedIntegral
  rw [← (measurement x).integral_comp_comm hi', ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  by_cases hη : η ∈ wideBand n j.val
  · rw [fullMeasuredDerivativePolynomial_eq_amplitude T Q F row col Φ Y r measurement χ
      hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ
      (hproduct (x, T.reference.spatialPatch z + τ • η) ⟨hxX, hsh η hη⟩),
      map_smul, map_smul]
    simp only [smul_smul]
    congr 1
    ring
  · rw [weightedRadialBand_eq_zero_off_wideBand (n := n) d hη]
    simp only [mul_zero, zero_mul, zero_smul, smul_zero, map_zero]

include hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ hζ hproduct hshift hd hdb in
/-- The sum of measured polynomial bands is exactly the differential of
the SAME full primary wave on the SAME wide input, with the physical cutoff
applied only to the output. This supplies the physical representative needed
to transfer the actual raw-slice estimate to sampling
(`app:ch_waves:eq:individual-representation`,
`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_measuredPolynomial_bandIntegral_eq_wave_derivative
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hX : IsOpen X) (hV : IsOpen V) (v : WideInput n J)
    (hχ : Function.support χ ⊆ X) (x : Euclidean n) :
    (∑ j : Fin J, rawSliceBandIntegral (phase T Q)
      (fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ τ z)
      (fun _ ↦ 1) (T.reference.spatialPatch z) τ
      (weightedRadialBand d j.val) j.val (v j) x) =
      (χ x : ℂ) • measurement x
        (Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
          RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
            (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x)) := by
  trans (χ x : ℂ) • measurement x
    (∑ j : Fin J, rawSliceBandIntegral (phase T Q)
      (fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, η)))
      (fun _ ↦ 1) (T.reference.spatialPatch z) τ
      (weightedRadialBand d j.val) j.val (v j) x)
  · rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦
      rawSliceBandIntegral_measuredPolynomial T Q F row col Φ Y r measurement χ
        hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ z hζ hproduct hshift hd hdb j (v j)
        (fun hn ↦ hχ hn))
  by_cases hx : χ x = 0
  · simp only [hx, Complex.ofReal_zero, zero_smul]
  have hxX := hχ hx
  have hmap : ContDiffOn ℝ ∞
      (fun q : Euclidean n × Euclidean (n - 1) ↦ (q.1, (z, q.2))) (X ×ˢ V) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
  have hS := (contDiffOn_fullPhase T Q hphase).comp hmap hproduct
  have hA := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ).2
  have hA' := hA.comp hmap hproduct
  have hatom (j : Fin J) : ContinuousOn
      (fun η : Euclidean (n - 1) ↦
        Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
          (T.reference.spatialPatch z) τ x η : ℂ)) •
          fullDerivativeAmplitude T Q F row col Φ Y r τ
            (x, (z, T.reference.spatialPatch z + τ • η))) (wideBand n j.val) := by
    have hsh : ∀ η ∈ wideBand n j.val, T.reference.spatialPatch z + τ • η ∈ V :=
      fun η hη ↦ hshift η (wideBand_subset_ceiling (n := n) j hη)
    have hc := (contDiffOn_rawPrimaryDemodulatedAtom
      (A := fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, η)))
      hS hA' hζ hsh).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun η hη ↦ ⟨hxX, hη⟩)
    exact hc
  have hsum := sum_rawSliceBandIntegral_eq_weightedWideDensity (n := n) (phase T Q)
    (fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (x, (z, η)))
    (fun _ ↦ 1) (T.reference.spatialPatch z) τ hd hdb v x (fun _ j ↦ hatom j)
  simp only [Complex.ofReal_one, one_smul] at hsum
  have hrep := fullPrimaryWave_differentialMatrix_representation T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hA z hX hV hζ hproduct hshift
    hd ((norm_nonneg (d 0)).trans (hdb 0)) hdb v hxX
  exact congrArg (fun W ↦ (χ x : ℂ) • measurement x W) (hsum.trans hrep.symm)

end JanetCartan.Sampling.MeasuredAmplitude
