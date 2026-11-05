module

public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-!
# Output jets under the compact carrier integral

The differentiation step of `app:ch_regular:lem:finite-chain`, used by
`iteratedFDeriv_fourierKernel_eq_integral`. Local domination is constructed
from joint smoothness on a compact output ball times the integration carrier.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FiniteChain.Retarded.KernelDecay

variable {V Z F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness of the output jets used for compact domination in
`app:ch_regular:lem:finite-chain`. -/
theorem contDiff_outputJet {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : V × Z => iteratedFDeriv ℝ m (fun y => f (y, p.2)) p.1) := by
  induction m with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ V F).symm.contDiff.comp hf
  | succ m ih =>
    have hd : ContDiff ℝ ∞ (fun p : V × Z =>
        fderiv ℝ (fun y => iteratedFDeriv ℝ m (fun t => f (t, p.2)) y) p.1) := by
      apply ContDiff.fderiv (m := ∞) (g := Prod.fst) _ contDiff_fst (by simp)
      exact ih.comp (contDiff_snd.prodMk contDiff_fst.snd)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) F).symm.contDiff.comp hd

variable [FiniteDimensional ℝ V] [MeasurableSpace Z] [BorelSpace Z]
  {μ : Measure Z} {K : Set Z}

omit [FiniteDimensional ℝ V] in
/-- Every output jet is integrable on the fixed compact carrier. Consumed by
`iteratedFDeriv_fourierKernel_eq_integral` (`app:ch_regular:lem:finite-chain`). -/
theorem integrableOn_outputJet [IsFiniteMeasure (μ.restrict K)]
    {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K) (m : ℕ) (x : V) :
    IntegrableOn (fun z => iteratedFDeriv ℝ m (fun y => f (y, z)) x) K μ :=
  JanetCartan.integrableOn_compactParameter (U := univ) (V := univ)
    hK (subset_univ _) (contDiff_outputJet hf m).continuous.continuousOn (mem_univ x)

/-- All orders of output differentiation pass through the compact carrier
integral. Compactness supplies the local integrable dominators; no derivative
identity is a premise (`app:ch_regular:lem:finite-chain`). -/
theorem iteratedFDeriv_compactCarrierIntegral [IsFiniteMeasure (μ.restrict K)]
    {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K) (m : ℕ) (x : V) :
    iteratedFDeriv ℝ m (fun y => ∫ z in K, f (y, z) ∂μ) x =
      ∫ z in K, iteratedFDeriv ℝ m (fun y => f (y, z)) x ∂μ := by
  let : ProperSpace V := FiniteDimensional.proper_rclike ℝ V
  have hb (j : ℕ) : ∃ C : ℝ, ∀ y ∈ Metric.closedBall x 1, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (fun t => f (t, z)) y‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn
      (contDiff_outputJet hf j).continuous.continuousOn
    exact ⟨C, fun y hy z hz => hC (y,z) ⟨hy,hz⟩⟩
  choose C hC using hb
  apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
    (r := m) (b := fun j _ => C j) Metric.isOpen_ball
  · exact ae_of_all _ fun z y _ =>
      ((hf.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
  · intro j _ y _
    exact (integrableOn_outputJet hf hK j y).aestronglyMeasurable
  · intro j _
    exact integrable_const _
  · intro j _
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz y hy
    exact hC j y (Metric.ball_subset_closedBall hy) z hz
  · exact le_rfl
  · exact Metric.mem_ball_self zero_lt_one

omit [FiniteDimensional ℝ V] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Output jets vanish off a common carrier since the whole output section
vanishes there (`app:ch_regular:lem:finite-chain`). -/
theorem outputJet_eq_zero_off_carrier {f : V × Z → F}
    (hs : ∀ y z, z ∉ K → f (y, z) = 0) (m : ℕ) (y : V) {z : Z} (hz : z ∉ K) :
    iteratedFDeriv ℝ m (fun t => f (t, z)) y = 0 := by
  have he : (fun t => f (t, z)) = fun _ => 0 := funext fun t => hs t z hz
  rw [he]
  simp

omit [FiniteDimensional ℝ V] in
/-- Common compact support and joint smoothness supply integrability of
all output jets in the normalized half-space measure
(`app:ch_regular:lem:finite-chain`). -/
theorem integrable_outputJet_commonCarrier [IsFiniteMeasureOnCompacts μ]
    {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hs : ∀ y z, z ∉ K → f (y, z) = 0) (m : ℕ) (y : V) :
    Integrable (fun z => iteratedFDeriv ℝ m (fun t => f (t, z)) y) μ := by
  apply ((contDiff_outputJet hf m).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz
  by_contra h
  exact hz (outputJet_eq_zero_off_carrier hs m y h)

/-- Differentiation under a measure integral with a common compact carrier,
used for both literal Fourier kernels in `app:ch_regular:lem:finite-chain`.
All domination and integrability conditions have been discharged. -/
theorem iteratedFDeriv_integral_commonCarrier [IsFiniteMeasureOnCompacts μ]
    {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hs : ∀ y z, z ∉ K → f (y, z) = 0) (m : ℕ) (x : V) :
    iteratedFDeriv ℝ m (fun y => ∫ z, f (y, z) ∂μ) x =
      ∫ z, iteratedFDeriv ℝ m (fun y => f (y, z)) x ∂μ := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have he : (fun y => ∫ z, f (y,z) ∂μ) = fun y => ∫ z in K, f (y,z) ∂μ := by
    funext y
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs y)).symm
  rw [he, iteratedFDeriv_compactCarrierIntegral hf hK]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => outputJet_eq_zero_off_carrier hs m x hz)

/-- Smoothness of the normalized integral on its fixed carrier, consumed by
output differentiation of the Fourier normalizing scalar
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_integral_commonCarrier [CompleteSpace F] [IsFiniteMeasureOnCompacts μ]
    {f : V × Z → F} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hs : ∀ y z, z ∉ K → f (y, z) = 0) :
    ContDiff ℝ ∞ (fun y => ∫ z, f (y, z) ∂μ) := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have he : (fun y => ∫ z, f (y,z) ∂μ) = fun y => ∫ z in K, f (y,z) ∂μ := by
    funext y
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs y)).symm
  rw [he, ← contDiffOn_univ]
  exact JanetCartan.contDiffOn_compactParameterIntegral (U := univ) (V := univ)
    isOpen_univ isOpen_univ hK (subset_univ _) hf.contDiffOn

end JanetCartan.FiniteChain.Retarded.KernelDecay
