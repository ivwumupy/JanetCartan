module

public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives

/-!
# Parameter differentiation on the original open neighborhood

The compact-kernel step of `app:ch_response:thm:response-literal-transfer`.
The consumer is `iteratedFDeriv_parameterGraphIntegral`. Joint smoothness and
one compact integration support imply all local dominators. In particular,
smoothness on the compact parameter box alone is not used as a substitute for
smoothness on its open neighborhood.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set P} {f : P × Z → F}

/-- Joint regularity of all parameter jets, used to obtain compact local
dominators (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_parameterIteratedFDeriv (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : P × Z ↦
      iteratedFDeriv ℝ j (fun b ↦ f (b, p.2)) p.1) (U ×ˢ univ) := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ P F).symm.contDiff.comp_contDiffOn hf
  | succ j ih =>
    have hd := contDiffOn_parameterFDeriv hU isOpen_univ ih
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ P) F).symm.contDiff
        |>.comp_contDiffOn hd

variable [MeasurableSpace Z] [BorelSpace Z] {μ : Measure Z} {K : Set Z}

/-- Compact support gives integrability of each actual parameter jet.
The support hypothesis concerns the original kernel only; jet support is
derived by locality (`app:ch_response:thm:response-literal-transfer`). -/
theorem integrable_parameterJet_of_compactSupport [IsFiniteMeasureOnCompacts μ]
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) (hK : IsCompact K)
    (hs : ∀ b ∈ U, ∀ z ∉ K, f (b, z) = 0) (j : ℕ) {c : P} (hc : c ∈ U) :
    Integrable (fun z ↦ iteratedFDeriv ℝ j (fun b ↦ f (b, z)) c) μ := by
  have hz {z : Z} (hz : z ∉ K) : iteratedFDeriv ℝ j (fun b ↦ f (b, z)) c = 0 := by
    have he : (fun b ↦ f (b, z)) =ᶠ[𝓝 c] fun _ ↦ (0 : F) :=
      Filter.mem_of_superset (hU.mem_nhds hc) fun b hb ↦ hs b hb z hz
    simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds
  have hcont : Continuous (fun z ↦ iteratedFDeriv ℝ j (fun b ↦ f (b, z)) c) := by
    rw [← continuousOn_univ]
    exact (contDiffOn_parameterIteratedFDeriv hU hf j).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ ↦ ⟨hc, mem_univ _⟩)
  apply hcont.integrable_of_hasCompactSupport
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz'
  by_contra hn
  exact hz' (hz hn)

variable [FiniteDimensional ℝ P]

/-- All finite parameter derivatives pass through the compact kernel integral.
The proof constructs a bound on a closed parameter ball times the original
integration support, then applies dominated differentiation. Consumed by the
literal graph theorem (`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_integral_parameterCompactSupport [IsFiniteMeasureOnCompacts μ]
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) (hK : IsCompact K)
    (hs : ∀ b ∈ U, ∀ z ∉ K, f (b, z) = 0) (j : ℕ) {c : P} (hc : c ∈ U) :
    iteratedFDeriv ℝ j (fun b ↦ ∫ z, f (b, z) ∂μ) c =
      ∫ z, iteratedFDeriv ℝ j (fun b ↦ f (b, z)) c ∂μ := by
  let : ProperSpace P := FiniteDimensional.proper_rclike ℝ P
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  have hb (i : ℕ) : ∃ C : ℝ, ∀ b ∈ Metric.closedBall c ε, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ i (fun a ↦ f (a, z)) b‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_closedBall c ε).prod hK).exists_bound_of_continuousOn
      ((contDiffOn_parameterIteratedFDeriv hU hf i).continuousOn.mono
        (Set.prod_mono hεU (subset_univ _)))
    exact ⟨C, fun b hb z hz ↦ hC (b, z) ⟨hb, hz⟩⟩
  choose C hC using hb
  have hd : iteratedFDeriv ℝ j (fun b ↦ ∫ z in K, f (b, z) ∂μ) c =
      ∫ z in K, iteratedFDeriv ℝ j (fun b ↦ f (b, z)) c ∂μ := by
    apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
      (r := j) (b := fun i _ ↦ C i) Metric.isOpen_ball
    · exact ae_of_all _ fun z b hb ↦
        ((hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds
          ⟨hεU (Metric.ball_subset_closedBall hb), mem_univ z⟩)).comp b
          (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
    · intro i _ b hb
      exact (integrableOn_compactParameter hK (subset_univ _)
        (contDiffOn_parameterIteratedFDeriv hU hf i).continuousOn
          (hεU (Metric.ball_subset_closedBall hb))).aestronglyMeasurable
    · intro i _
      exact integrable_const _
    · intro i _
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz b hb
      exact hC i b (Metric.ball_subset_closedBall hb) z hz
    · exact le_rfl
    · exact Metric.mem_ball_self hε
  have he : (fun b ↦ ∫ z, f (b, z) ∂μ) =ᶠ[𝓝 c]
      (fun b ↦ ∫ z in K, f (b, z) ∂μ) :=
    Filter.mem_of_superset (hU.mem_nhds hc) fun b hb ↦
      (setIntegral_eq_integral_of_forall_compl_eq_zero (hs b hb)).symm
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds, hd]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hez : (fun b ↦ f (b, z)) =ᶠ[𝓝 c] fun _ ↦ (0 : F) :=
    Filter.mem_of_superset (hU.mem_nhds hc) fun b hb ↦ hs b hb z hz
  simpa using (hez.iteratedFDeriv ℝ j).eq_of_nhds

/-- Smoothness of the same compact-supported integral on the original open
parameter set (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_integral_parameterCompactSupport [CompleteSpace F]
    [IsFiniteMeasureOnCompacts μ]
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) (hK : IsCompact K)
    (hs : ∀ b ∈ U, ∀ z ∉ K, f (b, z) = 0) :
    ContDiffOn ℝ ∞ (fun b ↦ ∫ z, f (b, z) ∂μ) U := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply (contDiffOn_compactParameterIntegral (μ := μ) hU isOpen_univ hK (subset_univ _) hf).congr
  intro b hb
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs b hb)).symm

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
