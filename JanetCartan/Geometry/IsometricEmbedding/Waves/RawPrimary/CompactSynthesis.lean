module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LebesgueData
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Basic

/-!
# Smooth superposition of the actual annular data

The Fourier density of an arbitrary Hilbert datum need not be continuous.
For `app:ch_waves:eq:individual-representation`, its proved `L¹` property and
compact Fourier support nevertheless allow differentiation of the same integral
field. Smooth atoms on an open product supply domination by compactness; no
derivative-interchange or output-smoothness hypothesis is used.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary

section Compact

variable {E Z F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {U : Set E} {V K : Set Z} {A : E × Z → F} {μ : Measure Z}
  [IsFiniteMeasure (μ.restrict K)] {f : Z → ℂ}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ Z] [CompleteSpace F] in
/-- Compact frequency support makes the actual weighted atoms integrable,
even when the Fourier datum is merely `L¹` (`app:ch_waves:thm:individual`). -/
theorem integrableOn_weightedAtom (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : IntegrableOn f K μ) (hA : ContinuousOn A (U ×ˢ V))
    {x : E} (hx : x ∈ U) : IntegrableOn (fun η ↦ f η • A (x, η)) K μ := by
  have hc : ContinuousOn (fun η ↦ A (x, η)) K :=
    hA.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hη ↦ ⟨hx, hKV hη⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact MeasureEnvelopes.integrable_weightedAtoms hf
    (integrableOn_compactParameter hK hKV hA hx).aestronglyMeasurable
    ((ae_restrict_mem hK.measurableSet).mono (fun η hη ↦ hC η hη))

omit [CompleteSpace F] in
/-- Differentiation of a Fourier superposition is proved from local joint
smoothness and an integrable density (`app:ch_waves:eq:individual-representation`). -/
theorem hasFDerivAt_weightedCompactIntegral (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : IntegrableOn f K μ)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ η in K, f η • A (y, η) ∂μ)
      (∫ η in K, f η • fderiv ℝ (fun y ↦ A (y, η)) x ∂μ) x := by
  obtain ⟨r, hr, hrU, C, hC⟩ := exists_bound_parameterFDeriv hU hV hK hKV hA hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y η ↦ f η • fderiv ℝ (fun y ↦ A (y, η)) y)
    (s := Metric.ball x r) (bound := fun η ↦ ‖f η‖ * C)
    (Metric.ball_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (integrableOn_weightedAtom hK hKV hf hA.continuousOn hy).aestronglyMeasurable
  · exact integrableOn_weightedAtom hK hKV hf hA.continuousOn hx
  · exact hf.aestronglyMeasurable.smul
      (integrableOn_parameterFDeriv hU hV hK hKV hA hx).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with η hη y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hC y (Metric.ball_subset_closedBall hy) η hη) (norm_nonneg _)
  · exact hf.norm.mul_const C
  · filter_upwards [ae_restrict_mem hK.measurableSet] with η hη y hy
    have hyU := hrU (Metric.ball_subset_closedBall hy)
    have hAy := hA.contDiffAt ((hU.prod hV).mem_nhds
      (show (y, η) ∈ U ×ˢ V from ⟨hyU, hKV hη⟩))
    exact (((hAy.comp y (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by simp)).hasFDerivAt).const_smul (f η)

/-- Arbitrary Hilbert data give the same smooth integral fields, including
all finite-dimensional spectator parameters (`app:ch_waves:thm:individual`). -/
theorem contDiffOn_weightedCompactIntegral (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : IntegrableOn f K μ)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun y ↦ ∫ η in K, f η • A (y, η) ∂μ) U := by
  have aux (r : ℕ) : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
      [CompleteSpace G] (B : E × Z → G), ContDiffOn ℝ ∞ B (U ×ˢ V) →
      ContDiffOn ℝ r (fun y ↦ ∫ η in K, f η • B (y, η) ∂μ) U := by
    induction r with
    | zero =>
      intro G _ _ _ B hB
      exact contDiffOn_zero.mpr (fun x hx ↦
        (hasFDerivAt_weightedCompactIntegral hU hV hK hKV hf hB hx).continuousAt.continuousWithinAt)
    | succ r ih =>
      intro G _ _ _ B hB
      rw [show ((r + 1 : ℕ) : WithTop ℕ∞) = r + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · intro x hx
        exact (hasFDerivAt_weightedCompactIntegral hU hV hK hKV hf hB hx).differentiableAt.differentiableWithinAt
      · exact (ih _ (contDiffOn_parameterFDeriv hU hV hB)).congr fun x hx ↦
          (hasFDerivAt_weightedCompactIntegral hU hV hK hKV hf hB hx).fderiv
  exact contDiffOn_infty.mpr fun r ↦ aux r A hA

end Compact

open RawInputPartition

variable {n J : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Literal Fourier superposition on the original smooth-band Hilbert input.
The atom may be the canonical displacement or its differentiated amplitude;
this operation does not add a spatial cutoff (`app:ch_waves:eq:WKB-W`). -/
def wideSuperposition (A : E × Euclidean (n - 1) → F)
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) (x : E) : F :=
  ∫ η, weightedWideDensity d v η • A (x, η)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The full integral equals its integral over the actual Fourier ceiling,
without modifying its atom (`app:ch_waves:eq:individual-representation`). -/
theorem wideSuperposition_eq_compact (A : E × Euclidean (n - 1) → F)
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) (x : E) :
    wideSuperposition A d v x =
      ∫ η in Metric.closedBall 0 ((2 : ℝ) ^ J), weightedWideDensity d v η • A (x, η) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro η hη
  have hη' : (2 : ℝ) ^ J ≤ ‖η‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using (le_of_lt
      (show (2 : ℝ) ^ J < ‖η‖ from by simpa using hη))
  rw [wideDensity_eq_zero_of_ceiling_le d v hη', zero_smul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Integrability for the original wide input is derived from the actual
density and the compact atom section (`app:ch_waves:eq:WKB-W`). -/
theorem integrable_wideSuperposition {U : Set E} {V : Set (Euclidean (n - 1))}
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : E × Euclidean (n - 1) → F} (hA : ContinuousOn A (U ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : E} (hx : x ∈ U) : Integrable (fun η ↦ weightedWideDensity d v η • A (x, η)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      ((2 : ℝ) ^ J))) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall _ _).measure_lt_top.ne
  apply (integrableOn_weightedAtom (isCompact_closedBall _ _) hVceil
    (integrable_wideDensity hd hM hb v).integrableOn hA hx).integrable_of_forall_notMem_eq_zero
  intro η hη
  have hη' : (2 : ℝ) ^ J ≤ ‖η‖ := le_of_lt (by simpa using hη)
  rw [wideDensity_eq_zero_of_ceiling_le d v hη', zero_smul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The original density's almost-everywhere additivity gives pointwise
additivity of its genuine integral (`app:ch_waves:eq:WKB-W`). -/
theorem wideSuperposition_add {U : Set E} {V : Set (Euclidean (n - 1))}
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : E × Euclidean (n - 1) → F} (hA : ContinuousOn A (U ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v w : WideInput n J)
    {x : E} (hx : x ∈ U) :
    wideSuperposition A d (v + w) x = wideSuperposition A d v x + wideSuperposition A d w x := by
  unfold wideSuperposition
  rw [← integral_add (integrable_wideSuperposition hVceil hA hd hM hb v hx)
    (integrable_wideSuperposition hVceil hA hd hM hb w hx)]
  apply integral_congr_ae
  filter_upwards [wideDensity_add hd hb v w] with η hη
  rw [hη, add_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The same raw integral preserves complex scaling, hence both quadratures
(`app:ch_waves:eq:WKB-W`). -/
theorem wideSuperposition_smul (A : E × Euclidean (n - 1) → F)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M) (c : ℂ) (v : WideInput n J) (x : E) :
    wideSuperposition A d (c • v) x = c • wideSuperposition A d v x := by
  unfold wideSuperposition
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [wideDensity_smul hd hb c v] with η hη
  rw [hη, mul_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The order-zero raw bound uses only the atomic bound on the actual Fourier
ceiling. Its data constant has exactly the source power `K^(n/2)` and is
independent of band count (`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_wideSuperposition_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    (A : E × Euclidean (n - 1) → F) {d : Euclidean (n - 1) → ℂ} {M C : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (hC : 0 ≤ C)
    (v : WideInput n (cutoffCount K)) (x : E)
    (hA : ∀ η ∈ Metric.closedBall 0 (4 * K), ‖A (x, η)‖ ≤ C) :
    ‖wideSuperposition A d v x‖ ≤
      (C * (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2))) *
        K ^ ((n : ℝ) / 2) * ‖v‖ := by
  have hi := integrable_wideDensity hd hM hb v
  calc
    _ ≤ ∫ η, C * ‖weightedWideDensity d v η‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul C)
      filter_upwards [] with η
      by_cases hη : ‖η‖ ≤ 4 * K
      · rw [norm_smul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hA η (by simpa using hη)) (norm_nonneg _)
      · rw [wideDensity_eq_zero_of_four_mul_le hK d v (le_of_lt (lt_of_not_ge hη))]
        simp
    _ = C * ∫ η, ‖weightedWideDensity d v η‖ := integral_const_mul _ _
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left
        (integral_norm_weightedWideDensity_rounded_le hn hK hd hM hb v) hC using 1
      ring

/-- Smoothness of the same raw integral for arbitrary `X_K` data is a
consequence of smooth atoms on the original buffered domain
(`app:ch_waves:thm:individual`). -/
theorem contDiffOn_wideSuperposition {U : Set E} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : E × Euclidean (n - 1) → F} (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiffOn ℝ ∞ (wideSuperposition A d v) U := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      ((2 : ℝ) ^ J))) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall _ _).measure_lt_top.ne
  simpa only [← wideSuperposition_eq_compact] using
    contDiffOn_weightedCompactIntegral hU hV (isCompact_closedBall _ _) hVceil
      (integrable_wideDensity hd hM hb v).integrableOn hA

omit [CompleteSpace F] in
/-- The actual spatial derivative of the wide-band superposition is the
integral of the atomic derivative; smoothness and domination of the Fourier
datum are not assumed (`app:ch_waves:eq:individual-representation`). -/
theorem hasFDerivAt_wideSuperposition {U : Set E} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : E × Euclidean (n - 1) → F} (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (wideSuperposition A d v)
      (wideSuperposition (fun p ↦ fderiv ℝ (fun y ↦ A (y, p.2)) p.1) d v x) x := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      ((2 : ℝ) ^ J))) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall _ _).measure_lt_top.ne
  change HasFDerivAt (fun y ↦ wideSuperposition A d v y) _ x
  simp_rw [wideSuperposition_eq_compact]
  exact hasFDerivAt_weightedCompactIntegral hU hV (isCompact_closedBall _ _) hVceil
    (integrable_wideDensity hd hM hb v).integrableOn hA hx

end JanetCartan.RawPrimary
