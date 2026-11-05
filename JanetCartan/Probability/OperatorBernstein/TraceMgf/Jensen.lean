module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity
public import JanetCartan.Probability.OperatorBernstein.SingleMgf
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Integration
public import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality for the Lieb trace functional

The one-variable expectation step preceding Minsker (3.4), used by
`app:ch_waves:thm:sampling` of `paper.tex`. A spectral bound places the exponential
in a closed convex cone bounded below by a positive scalar matrix. Lieb concavity
and continuity of the logarithm then allow the integral form of Jensen's inequality.

Integration uses the Frobenius norm; the almost-sure bound uses the explicit
Euclidean `operatorNorm`. The matrix index type may be empty.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- A uniform positive lower bound for the matrix exponential, used to choose
the closed Jensen domain in Minsker (3.4) (`app:ch_waves:thm:sampling`). -/
theorem exp_neg_bound_smul_one_le_exp_smul {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {R θ : ℝ} (hθ : 0 ≤ θ) (hbound : operatorNorm A ≤ R) :
    Real.exp (-(θ * R)) • (1 : Matrix d d ℂ) ≤ NormedSpace.exp (θ • A) := by
  cases isEmpty_or_nonempty d with
  | inl hd => exact le_of_eq (Subsingleton.elim _ _)
  | inr hd =>
    have hsa : IsSelfAdjoint A := hA
    have hθsa : IsSelfAdjoint θ := isSelfAdjoint_iff.mpr (star_trivial θ)
    have h := (cfc_le_iff (fun _ : ℝ => Real.exp (-(θ * R)))
      (fun x : ℝ => Real.exp (θ * x)) A).2 (fun x hx => by
        apply Real.exp_le_exp.mpr
        have hxR : |x| ≤ R := (spectrum.norm_le_norm_of_mem hx).trans hbound
        have hxlow : -R ≤ x := (abs_le.mp hxR).1
        nlinarith)
    have he : cfc (fun x : ℝ => Real.exp (θ * x)) A = NormedSpace.exp (θ • A) := by
      change cfc (Real.exp ∘ (fun x : ℝ => θ • x)) A = _
      rw [cfc_comp Real.exp (fun x : ℝ => θ • x) A hsa,
        cfc_smul_id θ A hsa, CFC.real_exp_eq_normedSpace_exp (hθsa.smul hsa)]
    rw [he, cfc_const _ A hsa, Algebra.algebraMap_eq_smul_one] at h
    exact h

open scoped Matrix.Norms.L2Operator in
/-- The closed cone above a positive scalar matrix lies in Lieb's domain
(Minsker Fact 5 and (3.4), `app:ch_waves:thm:sampling`). -/
theorem posDef_of_pos_smul_one_le {c : ℝ} (hc : 0 < c) {A : Matrix d d ℂ}
    (hA : c • (1 : Matrix d d ℂ) ≤ A) : A.PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.of_le (IsStrictlyPositive.smul hc isStrictlyPositive_one) hA)

open scoped Matrix.Norms.L2Operator in
/-- Continuity of matrix logarithm on Lieb's positive-definite domain
(Minsker Fact 5 and (3.4), `app:ch_waves:thm:sampling`). -/
theorem continuousOn_log_posDef : ContinuousOn CFC.log {A : Matrix d d ℂ | A.PosDef} :=
  CFC.continuousOn_log.mono (fun _ hA => ⟨hA.isHermitian, hA.isUnit⟩)

/-- Continuity of Lieb's trace functional on the positive-definite cone, needed
for integral Jensen in Minsker (3.4) (`app:ch_waves:thm:sampling`). -/
theorem continuousOn_realTrace_exp_add_log (H : Matrix d d ℂ) :
    ContinuousOn (fun A : Matrix d d ℂ => realTrace (NormedSpace.exp (H + CFC.log A)))
      {A : Matrix d d ℂ | A.PosDef} :=
  continuous_realTrace.comp_continuousOn
    (NormedSpace.exp_continuous.comp_continuousOn
      (continuousOn_const.add continuousOn_log_posDef))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Matrix d d ℂ} {R θ : ℝ}

/-- The bounded one-variable Jensen step preceding Minsker (3.4), from Lieb's
Fact 5 (`app:ch_waves:thm:sampling`). All continuity and integrability requirements
follow from the matrix hypotheses. This step does not require centering. -/
theorem integral_realTrace_exp_add_smul_le_of_bounded
    (hX : AEStronglyMeasurable X μ) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (hθ : 0 ≤ θ)
    {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • X ω)) ∂μ) ≤
      realTrace (NormedSpace.exp (H + CFC.log (∫ ω, NormedSpace.exp (θ • X ω) ∂μ))) := by
  let c := Real.exp (-(θ * R))
  let s : Set (Matrix d d ℂ) := Set.Ici (c • (1 : Matrix d d ℂ))
  let f := fun A : Matrix d d ℂ => realTrace (NormedSpace.exp (H + CFC.log A))
  have hs : s ⊆ {A : Matrix d d ℂ | A.PosDef} :=
    fun _ hA => posDef_of_pos_smul_one_le (Real.exp_pos _) hA
  have hc : ConcaveOn ℝ s f :=
    (LiebConcavity.concaveOn_realTrace_exp_add_log hH).subset hs (convex_Ici _)
  have hcont : ContinuousOn f s := (continuousOn_realTrace_exp_add_log H).mono hs
  have hae : ∀ᵐ ω ∂μ, NormedSpace.exp (θ • X ω) ∈ s := by
    filter_upwards [hHerm, hbound] with ω hω hb
    exact exp_neg_bound_smul_one_le_exp_smul hω hθ hb
  have heq : (fun ω => f (NormedSpace.exp (θ • X ω))) =ᵐ[μ]
      (fun ω => realTrace (NormedSpace.exp (H + θ • X ω))) := by
    filter_upwards [hHerm] with ω hω
    dsimp [f]
    rw [CFC.log_exp _ ((isSelfAdjoint_iff.mpr (star_trivial θ)).smul hω.isSelfAdjoint)]
  have hi : Integrable (fun ω => realTrace (NormedSpace.exp (H + θ • X ω))) μ := by
    apply integrable_realTrace
    exact integrable_continuous_of_operatorNorm_le hX hbound
      (NormedSpace.exp_continuous.comp (continuous_const.add (continuous_const_smul θ)))
  have hj := hc.le_map_integral hcont (isClosed_Ici : IsClosed s) hae
    (integrable_exp_smul_of_operatorNorm_le hX hbound θ) (hi.congr heq.symm)
  exact (integral_congr_ae heq).symm.trans_le hj

/-- The one-variable Jensen step in the bounded centered Bernstein setting
preceding Minsker (3.4) (`app:ch_waves:thm:sampling`). The centering and positive
radius assumptions are retained to match the single-matrix MGF hypotheses. -/
theorem integral_realTrace_exp_add_smul_le
    (hX : AEStronglyMeasurable X μ) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (_hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (_hR : 0 < R) (hθ : 0 ≤ θ)
    {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (∫ ω, realTrace (NormedSpace.exp (H + θ • X ω)) ∂μ) ≤
      realTrace (NormedSpace.exp (H + CFC.log (∫ ω, NormedSpace.exp (θ • X ω) ∂μ))) :=
  integral_realTrace_exp_add_smul_le_of_bounded hX hHerm hbound hθ hH

end JanetCartan.OperatorBernstein
