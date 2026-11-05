module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputGrades

/-!
# Buffered supports of differentiated graph amplitudes

The comparable-frequency estimate in `app:ch_regular:eq:chain-tail` needs a gap
on every actual output jet, not only on the original amplitude. Output
differentiation preserves the closed complementary support. Consequently the
same chart bounds and buffers give one gap for every output order. The basis
comparison below accommodates the product norm on the five joint variables.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph
open FourierIntegral KernelEstimates
variable {n r : ℕ}

/-- Output differentiation retains both the full input support and the closed
support of `1-mo`, including its identity term. Consumer: the differentiated
kernel gap in `app:ch_regular:eq:chain-tail`. -/
theorem outputJetAmplitude_tsupport_input_complement
    (backward : Bool) (ρ : ℝ) (φ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (ho : ContDiff ℝ ∞ mo) (m : ℕ) (v : Fin m → Euclidean n)
    {p : JointVariables (Euclidean n)}
    (hp : p ∈ tsupport (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v)) :
    (y, p.2.2.1) ∈ tsupport mi ∧
      (x, p.2.2.2) ∈ tsupport (fun q => 1 - mo q) := by
  constructor
  · exact (jointAmplitude_tsupport_subset ρ A mi (fun _ => 0) χA χo 0 y
      (tsupport_outputJetAmplitude_subset backward ρ φ A mi mo χA χo x y ho m v hp)).1
  · apply closure_minimal (s := Function.support
      (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v))
      (t := (fun q : JointVariables (Euclidean n) => (x, q.2.2.2)) ⁻¹'
        tsupport (fun q => 1 - mo q))
      _ ((isClosed_tsupport _).preimage (by fun_prop)) hp
    intro q hq
    by_contra hout
    have he := notMem_tsupport_iff_eventuallyEq.mp hout
    have ht : Filter.Tendsto (fun t : Euclidean n => (x + t, q.2.2.2))
        (𝓝 0) (𝓝 (x, q.2.2.2)) := by
      have ht' : Continuous (fun t : Euclidean n => (x + t, q.2.2.2)) := by fun_prop
      simpa only [add_zero] using ht'.tendsto 0
    have hz : (fun t : Euclidean n =>
        Complex.exp ((inner ℝ t (ρ • q.2.2.2) : ℂ) * Complex.I) *
          (1 - (mo (x + t, q.2.2.2) : ℂ))) =ᶠ[𝓝 0] 0 := by
      filter_upwards [ht.eventually he] with t hh
      have hm : mo (x + t, q.2.2.2) = 1 := (sub_eq_zero.mp hh).symm
      simp only [hm, Complex.ofReal_one, sub_self, mul_zero, Pi.zero_apply]
    have hd := (hz.iteratedFDeriv ℝ m).eq_of_nhds
    apply hq
    rw [outputJetAmplitude_eq_symbolJet backward ρ φ A mi mo χA χo x y m v ho q,
      hd, iteratedFDeriv_zero]
    simp

/-- Low inverse-chart geometry gives a gap on every differentiated amplitude.
There is no analytic gap premise; the separation comes from the constructed
localizers, and all five stationary equations enter the chart-distance bound
(`app:ch_regular:eq:joint-stationary`, `app:ch_regular:eq:chain-tail`). -/
theorem outputJetAmplitude_jointDerivative_gap
    (backward : Bool) (φ : Euclidean n → Euclidean n → ℝ)
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    {I D : Set (Euclidean n × Euclidean n)} {a b δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : if backward then ReverseChartControl φ κ I D a b
      else ForwardChartControl φ κ I D a b)
    {mi mo : LocalizerSymbol n} (hi : tsupport mi ⊆ I)
    (ho : ContDiff ℝ ∞ mo)
    (hbuffer : ∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q),
      δ ≤ dist (κ q) q')
    (ρ : ℝ) (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
    {p : JointVariables (Euclidean n)}
    (hp : p ∈ tsupport (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v))
    (hD : (p.1.1, p.2.1) ∈ D) :
    δ / graphGapConstant a b ≤ ‖fderiv ℝ (jointPhase backward φ x y) p‖ := by
  obtain ⟨hpi, hpo⟩ :=
    outputJetAmplitude_tsupport_input_complement backward ρ φ A mi mo χA χo x y ho m v hp
  have hI := hi hpi
  have hs := hbuffer _ hpi _ hpo
  rw [dist_comm] at hs
  apply (div_le_iff₀ (graphGapConstant_pos ha hb)).mpr
  cases backward
  · have hd := forward_chart_distance_le_jointDerivative φ x y p.1.1 p.1.2 p.2.1
      p.2.2.1 p.2.2.2 (κ (y,p.2.2.1)).1 (κ (y,p.2.2.1)).2
      (H.differentiable _ _ hD) (H.relation _ _ hI) ha hb
      (H.inverse_bound _ _ hI _ _ hD) (H.covector_variation _ _ hI _ _ hD)
      (H.base_variation _ _ hI _ _ hD)
    simpa only [mul_comm] using hs.trans hd
  · have hd := reverse_chart_distance_le_jointDerivative φ x y p.1.1 p.1.2 p.2.1
      p.2.2.1 p.2.2.2 (κ (y,p.2.2.1)).1 (κ (y,p.2.2.1)).2
      (H.differentiable _ _ hD) (H.relation _ _ hI) ha hb
      (H.inverse_bound _ _ hI _ _ hD) (H.base_variation _ _ hI _ _ hD)
      (H.covector_variation _ _ hI _ _ hD)
    simpa only [mul_comm] using hs.trans hd

/-- A fixed coordinate loss converts the product operator norm into the actual
sum of squared directional derivatives used in integration by parts. It is
independent of phase, scales, output order and requested accuracy
(`app:ch_regular:eq:chain-tail`). -/
def jointDirectionLoss {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n))) : ℝ :=
  max 1 ((Fintype.card ι : ℝ) * ‖e.equivFunL.toContinuousLinearMap‖)

/-- Positivity of the fixed coordinate loss (`app:ch_regular:eq:chain-tail`). -/
theorem jointDirectionLoss_pos {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n))) :
    0 < jointDirectionLoss e := zero_lt_one.trans_le (le_max_left _ _)

/-- Convert an actual packed derivative gap into the denominator of the
nonstationary field. This avoids assigning an incompatible Hilbert norm to
the five-variable product (`app:ch_regular:eq:chain-tail`). -/
theorem jointDerivative_gap_phaseGradientSquare {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (F : JointVariables (Euclidean n) → ℝ) (p : JointVariables (Euclidean n))
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : δ ≤ ‖fderiv ℝ F p‖) :
    (δ / jointDirectionLoss e) ^ 2 ≤ Localization.phaseGradientSquare e F p := by
  classical
  let S := Localization.phaseGradientSquare e F p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcomponent (i : ι) : ‖fderiv ℝ F p (e i)‖ ≤ Real.sqrt S := by
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs, sq_abs, S, Localization.phaseGradientSquare] using
      (Finset.single_le_sum (fun j _ => sq_nonneg (fderiv ℝ F p (e j)))
        (Finset.mem_univ i))
  have hn := e.opNorm_le (Real.sqrt_nonneg S) hcomponent
  have hnorm : ‖fderiv ℝ F p‖ ≤ jointDirectionLoss e * Real.sqrt S := by
    apply hn.trans
    simpa only [nsmul_eq_mul, jointDirectionLoss] using mul_le_mul_of_nonneg_right
      (le_max_right 1 ((Fintype.card ι : ℝ) * ‖e.equivFunL.toContinuousLinearMap‖))
      (Real.sqrt_nonneg S)
  have hh : δ / jointDirectionLoss e ≤ Real.sqrt S :=
    (div_le_iff₀ (jointDirectionLoss_pos e)).mpr (by
      simpa only [mul_comm] using hgap.trans hnorm)
  exact (Real.le_sqrt (div_nonneg hδ (jointDirectionLoss_pos e).le) hS).mp hh

/-- The same constructed masks protect every output jet, uniformly over the
phase family, before the frequency or derivative order is chosen. The input
shoulders are included (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_bufferedLocalizers_outputJet_gap
    {P : Type*} (backward : Bool)
    {K I J O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hKI : K ⊆ I)
    (hJ : IsCompact J) (hO : IsOpen O) (hJO : J ⊆ O)
    (φ : P → Euclidean n → Euclidean n → ℝ)
    (κ : P → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (D : P → Set (Euclidean n × Euclidean n))
    (himage : ∀ t p, p ∈ I → κ t p ∈ J)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : ∀ t, if backward then ReverseChartControl (φ t) (κ t) I (D t) a b
      else ForwardChartControl (φ t) (κ t) I (D t) a b) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧ IsBufferedLocalizer mo J O ∧
      (∀ t q, q ∈ tsupport mi → κ t q ∈ interior {q | mo q = 1}) ∧
      ∀ t (r : ℕ) (ρ : ℝ) (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
        (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
        (p : JointVariables (Euclidean n)),
        p ∈ tsupport (outputJetAmplitude backward ρ (φ t) A mi mo χA χo x y m v) →
        (p.1.1, p.2.1) ∈ D t →
        δ ≤ ‖fderiv ℝ (jointPhase backward (φ t) x y) p‖ := by
  obtain ⟨mi, mo, δ, hδ, hi, ho, hbuffer, hsep⟩ :=
    exists_bufferedLocalizers_of_image_envelope hK hI hKI hJ hO hJO κ himage
  refine ⟨mi, mo, δ / graphGapConstant a b,
    div_pos hδ (graphGapConstant_pos ha hb), hi, ho, hbuffer, ?_⟩
  intro t r ρ A χA χo x y m v p hp hD
  exact outputJetAmplitude_jointDerivative_gap backward (φ t) (κ t) ha hb (H t)
    hi.support_subset ho.smooth (fun q hq q' hq' => (hsep t q hq q' hq').le)
    ρ A χA χo x y m v hp hD

/-- The fixed constructed output mask supplies all normalized joint cutoff
grades before the scale is chosen. No separate analytic premise is needed for
this factor in `norm_iteratedFDeriv_regularizedJointKernel_le_of_buffer`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem IsBufferedLocalizer.exists_output_mask_profile
    {mo : LocalizerSymbol n} {K O : Set (Euclidean n × Euclidean n)}
    (ho : IsBufferedLocalizer mo K O) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ (ρ : ℝ), 1 ≤ ρ →
      ∀ (x : Euclidean n) (p : Euclidean n × Euclidean n) (j : ℕ),
      ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
        (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) p‖ ≤ B j := by
  have hb j := (ho.compactSupport.iteratedFDeriv (𝕜 := ℝ) j).exists_bound_of_continuous
    ((ho.smooth.iteratedFDeriv_right (m := ∞) (i := j) (by simp)).continuous)
  choose B hB using hb
  refine ⟨fun j => max 0 (B j), fun j => le_max_left _ _, ?_⟩
  intro ρ hρ x p j
  exact (norm_iteratedFDeriv_rescaled_graphMask_le ho.smooth hρ x j p).trans
    ((hB j _).trans (le_max_right _ _))

/-- The diagonal phase discharges every inverse-chart premise in the
all-output-order buffer theorem. The masks cover the entire source support,
including shoulders, for either literal orientation
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_diagonal_bufferedLocalizers_outputJet_gap (backward : Bool)
    {K I J O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hKI : K ⊆ I)
    (hJ : IsCompact J) (hO : IsOpen O) (hJO : J ⊆ O) (hIJ : I ⊆ J) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧ IsBufferedLocalizer mo J O ∧
      tsupport mi ⊆ interior {q | mo q = 1} ∧
      ∀ (r : ℕ) (ρ : ℝ) (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
        (x y : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n)
        (p : JointVariables (Euclidean n)),
        p ∈ tsupport (outputJetAmplitude backward ρ (fun u ξ => inner ℝ u ξ)
          A mi mo χA χo x y m v) →
        δ ≤ ‖fderiv ℝ (jointPhase backward (fun u ξ => inner ℝ u ξ) x y) p‖ := by
  have H : ∀ _ : Unit, if backward then
      ReverseChartControl (fun u ξ => inner ℝ u ξ) id I univ 1 1
      else ForwardChartControl (fun u ξ => inner ℝ u ξ) id I univ 1 1 := by
    intro t
    cases backward
    · exact diagonal_forwardChartControl I univ
    · exact diagonal_reverseChartControl I univ
  obtain ⟨mi, mo, δ, hδ, hi, ho, hbuffer, hgap⟩ :=
    exists_uniform_bufferedLocalizers_outputJet_gap backward hK hI hKI hJ hO hJO
      (fun _ : Unit => fun u ξ => inner ℝ u ξ) (fun _ : Unit => id)
      (fun _ : Unit => univ) (fun _ _ hp => hIJ hp)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) H
  exact ⟨mi, mo, δ, hδ, hi, ho, hbuffer (),
    fun r ρ A χA χo x y m v p hp => hgap () r ρ A χA χo x y m v p hp (mem_univ _)⟩

end JanetCartan.FiniteChain.Graph
