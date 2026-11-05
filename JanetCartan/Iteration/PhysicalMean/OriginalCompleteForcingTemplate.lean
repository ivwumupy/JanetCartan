module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurementTemplate
public import JanetCartan.Iteration.PhysicalSmoothing.MeasurementProfiles

/-!
# Measure the actual finite-moment defect, on the same history

The target summand in `new:eq:mean-source` is not the background quadrature
error.  This calculation uses the literal signed `historyDefect`, the given
smoothing domain and the prescribed finite moment order.  No periodic model
of the physical prefix or second smoothed tensor is chosen.  Only the numerical
frequency threshold and estimates are selected, before the target and history.
The native application supplies its existing measurement and profile from 98;
its domain is the final common core, as in `main:lem:smoothing`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open OriginalCanonicalMeasurement AmplitudeBound DefectSmoothing LocalSobolev
  AuxiliaryRawBand CurrentMean PhysicalSmoothing

/-- All cell faces have the same physical measurement jets: the support gap is
uniform in the tested tensor, not a pointwise intersection of infinitely many
neighborhoods (`new:eq:mean-source`). -/
theorem measurement_cell_profile {n reserve : ℕ}
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    {b T : ℝ} {A : ℕ → ℝ} (hb : b < 1 / 2)
    (hs : tsupport C ⊆ {x | ∀ i, |x i| ≤ b})
    (hp : HasDerivativeProfile (fundamentalCell n) C reserve T A) :
    HasDerivativeProfile (fundamentalCell n) (periodicLift (nativeMeasurement C)) reserve T A := by
  have he (x : Euclidean n) (hx : x ∈ fundamentalCell n) :
      periodicLift (nativeMeasurement C) =ᶠ[𝓝 x] C := by
    have hg : ∀ᶠ y in 𝓝 x, ∀ i, |y i| < 1 - b := by
      apply eventually_all.mpr
      intro i
      apply (isOpen_lt (EuclideanSpace.proj i).continuous.abs continuous_const).mem_nhds
      exact (abs_le.mpr (hx i)).trans_lt (by linarith)
    filter_upwards [hg] with y hy
    ext H i
    have hs' : SupportedInCenteredBox b (fun z : Euclidean n ↦ (C z H i : ℂ)) := by
      intro z hz
      apply hs (subset_tsupport _ _)
      intro heq
      apply hz
      simp [heq]
    have h := periodicLift_amplitudePeriodization_eq_of_lt hb hs' hy
    simpa only [periodicLift, nativeMeasurement, amplitudePeriodization, Function.comp_apply,
      Complex.ofReal_re] using congrArg Complex.re h
  intro k
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he k]
  exact hp k

/-- Retain just the frequency, chart containment, and physical jets from the
original finite-moment producer. The field in this statement is a definition,
not an existential approximation. -/
theorem original_normalized_estimates (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) :
    ∃ Rmin : ℝ, 1 ≤ Rmin ∧ ∃ L : ℕ → ℝ, ∀ R : ℝ, Rmin ≤ R →
      ∀ e : MetricField n, ContDiffOn ℝ ∞ e (D.chart n) →
      ∀ δ : ℝ, 0 < δ → cNorm (D.core n) 0 e ≤ δ ^ 2 →
      let f := revisedFiniteMomentSource D R m δ e
      ContDiff ℝ ∞ f ∧ tsupport f ⊆ D.chart n ∧ ∀ q : ℕ,
        cartesianJetNorm univ q (fun a ↦ iteratedFDeriv ℝ a f) ≤
          L q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
  obtain ⟨K,Rmin,L,_,hK,hRmin,_,_,_,h⟩ := exists_revisedFiniteMomentSource_bounds (n := n) D m hm
  refine ⟨Rmin,hRmin,L,?_⟩
  intro R hR e he δ hδ hsmall f
  obtain ⟨hsm,hs,_,_,_,hj,_,_⟩ := h R hR e he δ hδ hsmall
  exact ⟨hsm,hs.trans hK,fun q ↦ (le_add_of_nonneg_left (cNorm_nonneg univ q f)).trans (hj q)⟩

/-- Numerical stage threshold for the *specified* finite-moment field. -/
def targetFrequency (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  (original_normalized_estimates n D m hm).choose

/-- Exact tensor periodization cost for the same normalized finite-moment field. -/
def torusJetCost (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) (q : ℕ) : ℝ :=
  Real.sqrt (q.factorial : ℝ) * (original_normalized_estimates n D m hm).choose_spec.2.choose q

/-- The entire cost depends only on the original chart, order, and measurement
budget, not the current scale, metric, history, or Picard prefix. -/
def targetBudget (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) (CM : ℕ → ℝ) (q : ℕ) : ℝ :=
  coefficientBandConstant n q CM (torusJetCost n D m hm)

theorem targetBudget_nonneg (n : ℕ) (D : LocalDomain) (m : ℕ) (hm : 1 ≤ m) (CM : ℕ → ℝ) :
    ∀ q, 0 ≤ targetBudget n D m hm CM q := fun q ↦ coefficientBandConstant_nonneg n q _ _

/-- Apply the measurement to `e_R/b²` itself.  The metric input `gs` here is
the target at the chosen dilation; its only analytic hypotheses are chart
smoothness and the *original* signed metric defect bound in `main:thm:step`.
In particular no source estimate, smoothing success, frequency-capacity bound,
or equation for the desired increment is a hypothesis. -/
theorem measure_normalized_history {n : ℕ} (D : LocalDomain) (G : FlatReference n)
    (CM : ℕ → ℝ) (hCM : ∀ q, 0 ≤ CM q) (R₀ : ℝ) (hR₀ : 2 ≤ R₀) (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (reserve : ℕ) (Cper : Torus n → MetricTensor n →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (hprofile : HasDerivativeProfile (fundamentalCell n) (periodicLift Cper) reserve
      (currentCoefficientScale R₀ j) CM)
    (m : ℕ) (hm : 1 ≤ m) (gs : MetricField n) (hgs : ContDiffOn ℝ ∞ gs (D.chart n))
    (δ : ℝ) (hδ : 0 < δ) (hR : targetFrequency n D m hm ≤ iterationScale R₀ growthExponent j)
    (hsmall : cNorm (D.core n) 0 (inducedMetric (RevisedGlobal.finiteMap G.map u) - gs) ≤ δ ^ 2) :
    let R := iterationScale R₀ growthExponent j
    ∃ target : SmoothResidual n,
      (∀ z, target.val z () = Cper z (tensorPeriodization (normalizedSource D R m δ gs G.map u) z)) ∧
      (∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
        targetBudget n D m hm CM q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
      ∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
        targetBudget n D m hm CM q * R ^ (-separationExponent) * R ^ (q - RevisedScales.sourceOrder n) := by
  intro R
  let e := historyDefect gs G.map u
  have he := contDiffOn_historyDefect hgs G.contDiff u
  have hsmall' : cNorm (D.core n) 0 e ≤ δ ^ 2 := by
    change cNorm _ 0 (gs - inducedMetric (RevisedGlobal.finiteMap G.map u)) ≤ _
    rw [← neg_sub (inducedMetric (RevisedGlobal.finiteMap G.map u)) gs, cNorm_neg]
    exact hsmall
  obtain ⟨hs,hsupp,hjets⟩ := (original_normalized_estimates n D m hm).choose_spec.2.choose_spec
    R hR e he δ hδ hsmall'
  let f := normalizedSource D R m δ gs G.map u
  have hf : IsSmoothPeriodic (tensorPeriodization f) :=
    isSmoothPeriodic_tensorPeriodization D.chartRadius_lt_half hsupp hs
  let target : SmoothResidual n := ⟨fun z _ ↦ Cper z (tensorPeriodization f z),
    fun _ ↦ ⟨hCper.1.clm_apply hf.1,hCper.2.clm_apply hf.2⟩⟩
  have hRone : 1 ≤ R := (original_normalized_estimates n D m hm).choose_spec.1.trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hT := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith) j
  have hTR : currentCoefficientScale R₀ j ≤ R := by
    change R ^ coefficientExponent ≤ R
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hRone
      (show coefficientExponent ≤ 1 by norm_num [coefficientExponent])
  have hsplit (q : ℕ) : R ^ q * R ^ (-2 * RevisedScales.forcingExponent n) =
      R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    ring
  have hfield (q : ℕ) : periodicSobolevNorm q (tensorPeriodization f) ≤
      torusJetCost n D m hm q * R ^ q * R ^ (-2 * RevisedScales.forcingExponent n) := by
    apply ((periodicSobolevNorm_tensorPeriodization_le D.chartRadius_lt_half hsupp hs q).trans
      (mul_le_mul_of_nonneg_left (hjets q) (Real.sqrt_nonneg _))).trans_eq
    rw [mul_assoc (torusJetCost n D m hm q), hsplit]
    unfold torusJetCost
    ring
  have hb (q : ℕ) : periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
      targetBudget n D m hm CM q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
    apply (periodicSobolevNorm_clm_apply_le_of_profiles q CM (torusJetCost n D m hm)
      Cper (tensorPeriodization f) hCper hf hT hTR (Real.rpow_nonneg hRpos.le _)
      (fun k _ ↦ (hprofile k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hT (Nat.sub_le k reserve)) (hCM k))) (fun k _ ↦ hfield k)).trans_eq
    rw [mul_assoc, hsplit]
    rfl
  refine ⟨target,fun _ ↦ rfl,hb,?_⟩
  intro q
  apply (hb q).trans
  rw [mul_assoc, ← Real.rpow_natCast R (q - RevisedScales.sourceOrder n), ← Real.rpow_add hRpos]
  apply mul_le_mul_of_nonneg_left _ (targetBudget_nonneg n D m hm CM q)
  apply Real.rpow_le_rpow_of_exponent_le hRone
  have hq : (q : ℝ) ≤ (RevisedScales.sourceOrder n : ℝ) + ((q - RevisedScales.sourceOrder n : ℕ) : ℝ) := by
    exact_mod_cast (show q ≤ RevisedScales.sourceOrder n + (q - RevisedScales.sourceOrder n) by omega)
  have hg := (RevisedScales.source_order_and_forcing_gap n).2.2.1
  have hβ : separationExponent ≤ 1 := by norm_num [separationExponent]
  linarith

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end
