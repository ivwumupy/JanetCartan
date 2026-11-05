module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothMap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData

/-!
# Boundedness of the actual corrected raw map

Construct the continuity witness needed by `CanonicalChange.smoothRawCrossOperator`
from the existing corrected kernel and the original compact slice cutoff.
The constants precede the Hilbert datum and all retained prefixes. They are
qualitative full-band constants: the sharp uniform profiles remain the
raw-atom producer's obligation (`main:eq:old-canonical`). No estimate of the
desired canonical input or final mean is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open CanonicalAtomRealization RawPrimary RawInputPartition RawInputRealization CorrectedAtoms AmplitudeBound
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1))
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ O ×ˢ V, (p.1, (z, ζ + τ • p.2)) ∈ Ω)
    (hτ : τ ≠ 0) (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ O)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

include hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
  hd hM hb hψ hs hcell hbox

/-- The literal corrected raw map has a finite L² continuity bound, derived
from its smooth kernel on the supplied compact cutoff and frequency ceiling
(`app:ch_mean_pairs:defn:mean-canonical`). The same witness bounds every
original prefix; it is not used as a uniform sharp raw estimate. -/
theorem exists_smoothCorrectedWideDerivative_l2_bound :
    let G := smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
      hd hM hb ψ hψ hs hcell hbox
    ∃ CG : ℝ, 0 ≤ CG ∧
      (∀ v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖) ∧
      ∀ (L : ℕ) (v : RefinedInput n J),
        periodicL2Norm (fun x ↦ (canonicalWidePrefixRawMap G L v).val x ()) ≤ CG * ‖v‖ := by
  let G := smoothCorrectedWideDerivative T Q F row col Φ Y χ B τ r z ζ
    hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil
    hd hM hb ψ hψ hs hcell hbox
  let A := correctedWideKernel T Q F row col Φ Y χ B τ r z ζ
  have hcompact : IsCompact (tsupport ψ) :=
    (isCompact_fundamentalCell n).of_isClosed_subset (isClosed_tsupport ψ)
      (fun x hx i ↦ abs_le.mp ((hbox x hx i).trans hcell.le))
  have hzero : (0 : Euclidean (n - 1)) ∈ V :=
    hceil (Metric.mem_closedBall_self (by positivity))
  have hA : ContinuousOn A (tsupport ψ ×ˢ Metric.closedBall 0 ((2 : ℝ) ^ J)) :=
    (contDiffOn_correctedWideKernel T Q F row col Φ Y χ B τ r z ζ
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hzero).continuousOn.mono
        (fun _ hp ↦ ⟨hs hp.1, hceil hp.2⟩)
  obtain ⟨Cψ, hCψ⟩ := hcompact.exists_bound_of_continuousOn hψ.continuous.continuousOn
  obtain ⟨CA, hCA⟩ := (hcompact.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn hA
  let Cfour := Real.sqrt (∑ j : RefinedIndex J, (Real.sqrt (refinedRadius j) * M *
    Real.sqrt ((annularMeasure n (refinedRadius j) univ).toReal)) ^ 2)
  have hCfour : 0 ≤ Cfour := Real.sqrt_nonneg _
  have hfour (v : WideInput n J) : (∫ η, ‖weightedWideDensity d v η‖) ≤ Cfour * ‖v‖ := by
    have heq : (∫ η, ‖weightedWideDensity d v η‖) =
        ∫ η, ‖density (fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val) (wideRefinement n J v) η‖ :=
      integral_congr_ae ((weightedWideDensity_eq_refined hd hM hb v).mono (fun _ hη ↦ congrArg norm hη))
    rw [heq]
    simpa only [LinearIsometryEquiv.norm_map] using
      integral_norm_density_le (n := n) (radius := refinedRadius (J := J))
        (fun j : RefinedIndex J ↦ measurable_weightedRadialBand hd j.1.val) hM
        (fun j : RefinedIndex J ↦ norm_weightedRadialBand_le hb j.1.val) (wideRefinement n J v)
  have hsuper (v : WideInput n J) (x : Euclidean n) (hx : x ∈ tsupport ψ) :
      ‖wideSuperposition A d v x‖ ≤ max CA 0 * (Cfour * ‖v‖) := by
    calc
      _ ≤ ∫ η, max CA 0 * ‖weightedWideDensity d v η‖ := by
        apply norm_integral_le_of_norm_le ((integrable_wideDensity hd hM hb v).norm.const_mul _)
        filter_upwards [] with η
        by_cases hη : η ∈ Metric.closedBall 0 ((2 : ℝ) ^ J)
        · rw [norm_smul, mul_comm (max CA 0)]
          exact mul_le_mul_of_nonneg_left ((hCA (x, η) ⟨hx, hη⟩).trans (le_max_left _ _)) (norm_nonneg _)
        · rw [wideDensity_eq_zero_of_ceiling_le d v (le_of_lt (by simpa using hη))]
          simp
      _ = max CA 0 * (∫ η, ‖weightedWideDensity d v η‖) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfour v) (le_max_right _ _)
  let CG := max Cψ 0 * max CA 0 * Cfour
  have hCG : 0 ≤ CG := by dsimp only [CG]; positivity
  have hbound (v : WideInput n J) : periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG * ‖v‖ := by
    apply periodicL2Norm_le_of_bound _ (mul_nonneg hCG (norm_nonneg _))
    intro x
    rw [smoothCorrectedWideDerivative_apply]
    by_cases hx : centeredTorusRepresentative x ∈ tsupport ψ
    · rw [correctedWideDerivative_eq_superposition T Q F row col Φ Y χ B τ r z ζ
        hΩ hspace hphase hF hi hrank hα hnonzero hresponse hshift hτ hO hV hceil hd hM hb v (hs hx), norm_smul]
      calc
        _ ≤ max Cψ 0 * (max CA 0 * (Cfour * ‖v‖)) :=
          mul_le_mul ((hCψ _ hx).trans (le_max_left _ _)) (hsuper v _ hx)
            (norm_nonneg _) (le_max_right _ _)
        _ = CG * ‖v‖ := by dsimp only [CG]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero]
      exact mul_nonneg hCG (norm_nonneg _)
  refine ⟨CG, hCG, hbound, ?_⟩
  intro L v
  simpa only [max_eq_left hCG] using periodicL2Norm_canonicalWidePrefixRawMap_le G CG hbound L v

end JanetCartan.CurrentMean
