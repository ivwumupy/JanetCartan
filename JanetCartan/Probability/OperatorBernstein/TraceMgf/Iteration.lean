module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity
public import JanetCartan.Probability.OperatorBernstein.SingleMgf
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Integration
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Jensen
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Independence.Integration

/-!
# Independent-family trace cumulant bound

The iteration of Lieb's Jensen inequality preceding Minsker (3.4), used in
`app:ch_waves:thm:sampling` of `paper.tex`. Independence identifies the joint law
of a partial sum and the next summand with the product of their laws. Fubini and
the one-variable Jensen theorem then replace that summand by its log-MGF.
Induction keeps an arbitrary deterministic Hermitian offset.

All integrability follows from the almost-sure operator bounds. Integration uses
the Frobenius norm, and `operatorNorm` is the explicit Euclidean operator norm.
Both the family index type and the matrix index type may be empty.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {A B : Ω → Matrix d d ℂ}

/-- Independence replaces a continuous function of two random matrices by its
product-space expectation, as used in the iteration preceding Minsker (3.4)
(`app:ch_waves:thm:sampling`). -/
theorem integral_independent_matrix_pair (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ) (hAB : IndepFun A B μ)
    (f : Matrix d d ℂ × Matrix d d ℂ → ℝ) (hf : Continuous f) :
    (∫ ω, f (A ω, B ω) ∂μ) =
      ∫ p : Ω × Ω, f (A p.1, B p.2) ∂μ.prod μ := by
  rw [← integral_map (hA.aemeasurable.prodMk hB.aemeasurable) hf.aestronglyMeasurable,
    hAB.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable,
    Measure.map_prod_map_of_aemeasurable μ μ hA.aemeasurable hB.aemeasurable,
    integral_map (hA.aemeasurable.prodMap hB.aemeasurable)
      hf.aestronglyMeasurable]
  rfl

/-- The trace exponential of two bounded random matrices on the product space
is integrable, with arbitrary deterministic offset. This supplies Fubini's
hypothesis in Minsker (3.4) (`app:ch_waves:thm:sampling`). -/
theorem integrable_realTrace_exp_add_pair (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ) {RA RB : ℝ}
    (hbA : ∀ᵐ ω ∂μ, operatorNorm (A ω) ≤ RA)
    (hbB : ∀ᵐ ω ∂μ, operatorNorm (B ω) ≤ RB)
    (H : Matrix d d ℂ) (θ : ℝ) :
    Integrable (fun p : Ω × Ω =>
      realTrace (NormedSpace.exp (H + θ • (A p.1 + B p.2)))) (μ.prod μ) := by
  apply integrable_realTrace
  apply integrable_continuous_of_operatorNorm_le
    (f := fun X : Matrix d d ℂ => NormedSpace.exp (H + θ • X))
    (hA.comp_fst.add hB.comp_snd) (R := RA + RB)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbA,
      Measure.quasiMeasurePreserving_snd.ae hbB] with p hpA hpB
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := d) (A p.1 + B p.2)‖ ≤ RA + RB
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add hpA hpB)
  · exact NormedSpace.exp_continuous.comp
      (continuous_const.add (continuous_const_smul θ))

/-- Fubini for the trace exponential of two independent bounded random matrices,
used before Minsker (3.4) (`app:ch_waves:thm:sampling`). No extra integrability
hypothesis is needed. -/
theorem integral_realTrace_exp_add_pair_eq (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ) (hAB : IndepFun A B μ) {RA RB : ℝ}
    (hbA : ∀ᵐ ω ∂μ, operatorNorm (A ω) ≤ RA)
    (hbB : ∀ᵐ ω ∂μ, operatorNorm (B ω) ≤ RB)
    (H : Matrix d d ℂ) (θ : ℝ) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • (A ω + B ω))) ∂μ) =
      ∫ ω, ∫ ω', realTrace (NormedSpace.exp (H + θ • (A ω + B ω'))) ∂μ ∂μ := by
  rw [integral_independent_matrix_pair hA hB hAB
    (fun p => realTrace (NormedSpace.exp (H + θ • (p.1 + p.2))))
    (continuous_realTrace.comp (NormedSpace.exp_continuous.comp
      (continuous_const.add ((continuous_fst.add continuous_snd).const_smul θ))))]
  exact integral_prod _ (integrable_realTrace_exp_add_pair hA hB hbA hbB H θ)

/-- One independence/Jensen step: replace the second summand by its deterministic
log-MGF, retaining the first summand and the Hermitian offset. This is the
iteration preceding Minsker (3.4) (`app:ch_waves:thm:sampling`). -/
theorem integral_realTrace_exp_add_independent_le
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hAB : IndepFun A B μ)
    (hHermA : ∀ᵐ ω ∂μ, (A ω).IsHermitian)
    (hHermB : ∀ᵐ ω ∂μ, (B ω).IsHermitian) {RA RB θ : ℝ}
    (hbA : ∀ᵐ ω ∂μ, operatorNorm (A ω) ≤ RA)
    (hbB : ∀ᵐ ω ∂μ, operatorNorm (B ω) ≤ RB) (hθ : 0 ≤ θ)
    {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • (A ω + B ω))) ∂μ) ≤
      ∫ ω, realTrace (NormedSpace.exp
        (H + CFC.log (∫ ω', NormedSpace.exp (θ • B ω') ∂μ) + θ • A ω)) ∂μ := by
  rw [integral_realTrace_exp_add_pair_eq hA hB hAB hbA hbB H θ]
  apply integral_mono_ae
    (integrable_realTrace_exp_add_pair hA hB hbA hbB H θ).integral_prod_left
    (integrable_realTrace (integrable_continuous_of_operatorNorm_le hA hbA
      (NormedSpace.exp_continuous.comp (continuous_const.add (continuous_const_smul θ)))))
  filter_upwards [hHermA] with ω hω
  have hj := integral_realTrace_exp_add_smul_le_of_bounded hB hHermB hbB hθ
    (hH.add (hω.smul (show IsSelfAdjoint θ from isSelfAdjoint_iff.mpr (star_trivial θ))))
  simpa only [Function.comp_apply, Pi.add_apply, smul_add, add_assoc, add_left_comm, add_comm] using hj

variable {ι : Type*} [Fintype ι] {Y : ι → Ω → Matrix d d ℂ} {R θ : ℝ}

/-- The finite-set cumulant bound with a deterministic Hermitian offset,
preceding Minsker (3.4) (`app:ch_waves:thm:sampling`). Centering is unnecessary
for this expectation-to-cumulant step. All analytic hypotheses follow from the
almost-sure operator bounds. -/
theorem integral_realTrace_exp_add_finset_sum_le_sum_log_mgf
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) (hθ : 0 ≤ θ)
    (s : Finset ι) {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • ∑ i ∈ s, Y i ω)) ∂μ) ≤
      realTrace (NormedSpace.exp
        (H + ∑ i ∈ s, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ))) := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | @insert i s his ih =>
    have hsmeas : AEStronglyMeasurable (fun ω => ∑ j ∈ s, Y j ω) μ :=
      Finset.aestronglyMeasurable_fun_sum s (fun j _ => hY j)
    have hsbound : ∀ᵐ ω ∂μ, operatorNorm (∑ j ∈ s, Y j ω) ≤ ∑ _j ∈ s, R := by
      filter_upwards [ae_all_iff.mpr hbound] with ω hω
      unfold operatorNorm at *
      rw [map_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hω j)
    have hsHerm : ∀ᵐ ω ∂μ, (∑ j ∈ s, Y j ω).IsHermitian := by
      filter_upwards [ae_all_iff.mpr hHerm] with ω hω
      exact (isSelfAdjoint_sum s fun j _ => (hω j).isSelfAdjoint).isHermitian
    have hsi : IndepFun (fun ω => ∑ j ∈ s, Y j ω) (Y i) μ := by
      simpa only [Finset.sum_fn] using
        hIndep.indepFun_finsetSum_of_notMem₀ (fun j => (hY j).aemeasurable) his
    have hj := integral_realTrace_exp_add_independent_le hsmeas (hY i) hsi
      hsHerm (hHerm i) hsbound (hbound i) hθ hH
    have hh := ih (H := H + CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ))
      (hH.add (IsSelfAdjoint.log).isHermitian)
    simp only [Finset.sum_insert his]
    simpa only [add_assoc, add_comm, add_left_comm] using hj.trans hh

/-- The independent-family cumulant bound with a deterministic Hermitian offset
in the centered Bernstein setting, preceding Minsker (3.4)
(`app:ch_waves:thm:sampling`). -/
theorem integral_realTrace_exp_add_sum_le_sum_log_mgf
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (_hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (_hR : 0 < R) (hθ : 0 ≤ θ)
    {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • ∑ i, Y i ω)) ∂μ) ≤
      realTrace (NormedSpace.exp
        (H + ∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ))) :=
  integral_realTrace_exp_add_finset_sum_le_sum_log_mgf
    hIndep hY hHerm hbound hθ Finset.univ hH

/-- The independent-family trace cumulant bound preceding Minsker (3.4), used by
`app:ch_waves:thm:sampling`. This is the result of successively applying Lieb's
Jensen inequality; it holds also for empty families and empty matrix index types.
All integrability and independence/Fubini steps are discharged from the stated
bounded-matrix hypotheses. -/
theorem integral_realTrace_exp_sum_le_sum_log_mgf
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hθ : 0 ≤ θ) :
    (∫ ω, realTrace (NormedSpace.exp (θ • ∑ i, Y i ω)) ∂μ) ≤
      realTrace (NormedSpace.exp
        (∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ))) := by
  simpa only [zero_add] using
    integral_realTrace_exp_add_sum_le_sum_log_mgf hIndep hY hHerm hcenter hbound hR hθ
      (H := 0) Matrix.isHermitian_zero

end JanetCartan.OperatorBernstein
