module

public import JanetCartan.Probability.HilbertOperatorBernstein.FiniteDimensional

/-!
# Bernstein for compact Hilbert-space operators

The whole-output concentration step of `app:ch_waves:thm:sampling` in
`paper.tex`, lines 5949–5959. Independent centered compact self-adjoint operators
are compressed to finite-dimensional subspaces, where matrix Bernstein applies.
The compact-sum limit then gives the full operator-norm tail.

This is a conditional analytic deduction: the sampling construction must supply
independence, centering, the almost-sure bound, the variance and diagonal trace
bounds, and an increasing dense sequence of finite-dimensional subspaces. No
finite-compression concentration inequality is assumed. The positive variance
upper parameter also permits zero actual variance.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators Topology

namespace JanetCartan.HilbertOperatorBernstein

variable {H Ω ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Compression as a continuous linear map on operator spaces, used to preserve
independence and expectation in `app:ch_waves:thm:sampling`. -/
def restrictCompressionCLM (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    (H →L[ℂ] H) →L[ℂ] (U →L[ℂ] U) :=
  (ContinuousLinearMap.postcomp U U.orthogonalProjectionOnto).comp
    (ContinuousLinearMap.precomp H U.subtypeL)

omit [CompleteSpace H] in
/-- Evaluation of the continuous compression map (`app:ch_waves:thm:sampling`). -/
@[simp] theorem restrictCompressionCLM_apply (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (T : H →L[ℂ] H) :
    restrictCompressionCLM U T = OperatorCompression.restrictCompression U T := rfl

/-- Restricting orthogonal compression preserves self-adjointness
(`app:ch_waves:thm:sampling`). -/
theorem isSelfAdjoint_restrictCompression (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] [CompleteSpace U]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (OperatorCompression.restrictCompression U T) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪U.orthogonalProjectionOnto (T x), y⟫_ℂ =
    ⟪x, U.orthogonalProjectionOnto (T y)⟫_ℂ
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT.isSymmetric x y

/-- Compact compression convergence turns Borel measurability into strong
measurability for the original family (`app:ch_waves:thm:sampling`). This avoids
any change of representatives, hence preserves its independence. -/
theorem stronglyMeasurable_of_compact
    [MeasurableSpace Ω] [MeasurableSpace (H →L[ℂ] H)] [BorelSpace (H →L[ℂ] H)]
    (U : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (U n)]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    (Y : Ω → H →L[ℂ] H) (hY : Measurable Y)
    (hc : ∀ ω, IsCompactOperator (Y ω)) (hsa : ∀ ω, IsSelfAdjoint (Y ω)) :
    StronglyMeasurable Y := by
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun n ω => OperatorCompression.compress (U n).starProjection (Y ω))
  · intro n
    let : MeasurableSpace (U n →L[ℂ] U n) := borel _
    have hm' : Measurable (restrictCompressionCLM (U n)) :=
      (restrictCompressionCLM (U n)).continuous.measurable
    have hm := (hm'.comp hY).stronglyMeasurable
    have he : Continuous (fun S : U n →L[ℂ] U n =>
        (U n).subtypeL ∘L S ∘L (U n).orthogonalProjectionOnto) := by fun_prop
    convert he.comp_stronglyMeasurable hm using 1
    ext ω x
    rfl
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact OperatorCompression.tendsto_compress (fun n => (U n).starProjection)
      (fun n => (U n).starProjection_norm_le)
      (fun n => isSelfAdjoint_starProjection (U n))
      (fun x => Submodule.starProjection_tendsto_self U hmono x hdense.ge)
      (Y ω) (hc ω) (hsa ω)

variable [Fintype ι] [MeasurableSpace Ω]
  [MeasurableSpace (H →L[ℂ] H)] [BorelSpace (H →L[ℂ] H)]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ι → Ω → H →L[ℂ] H}

/-- Full operator-norm Bernstein inequality from the actual probabilistic and
moment hypotheses in `app:ch_waves:thm:sampling`. The constant is `14 τ / v`,
with the unnormalized finite orthonormal diagonal bound `τ`. Compactness and
self-adjointness are pointwise so the compact-compression limit applies directly;
no modification of the independent family is required. -/
theorem operatorBernstein
    (U : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (U n)]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    (hIndep : iIndepFun Y μ) (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hc : ∀ i ω, IsCompactOperator (Y i ω))
    (hsa : ∀ i ω, IsSelfAdjoint (Y i ω))
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    {R v τ t : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ R)
    (hR : 0 < R) (hv : 0 < v) (V : H →L[ℂ] H) (hVnorm : ‖V‖ ≤ v)
    (hV : ∀ x, ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ Complex.re ⟪x, V x⟫_ℂ)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℂ e →
      ∑ j, Complex.re ⟪e j, V (e j)⟫_ℂ ≤ τ)
    (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ {ω | t < ‖∑ i, Y i ω‖} ≤ OperatorCompression.bernsteinTail R v τ t := by
  classical
  have hint : ∀ i ∈ (Finset.univ : Finset ι), ∀ x,
      Integrable (fun ω => ‖Y i ω x‖ ^ 2) μ :=
    fun i _ x => integrable_norm_sq_apply (hY i) (hbound i) x
  apply OperatorCompression.bernstein_of_finite_compressions μ U hmono hdense
    Finset.univ Y (fun i _ => hc i) (fun i _ => hsa i) R v τ ?_ hR.le hv t ht hthreshold
  intro n u _ hv' hu hthreshold'
  let : MeasurableSpace (U n →L[ℂ] U n) := borel _
  let C := restrictCompressionCLM (U n)
  have hCY : ∀ i, AEStronglyMeasurable (fun ω => C (Y i ω)) μ :=
    fun i => C.continuous.comp_aestronglyMeasurable (hY i)
  have hCbound : ∀ i, ∀ᵐ ω ∂μ, ‖C (Y i ω)‖ ≤ R := by
    intro i
    filter_upwards [hbound i] with ω hω
    exact (OperatorCompression.norm_restrictCompression_le (U n) (Y i ω)).trans hω
  have hCmeas : Measurable C := C.continuous.measurable
  have hCIndep : iIndepFun (fun i ω => C (Y i ω)) μ :=
    hIndep.comp (fun _ => C) (fun _ => hCmeas)
  refine finiteDimensional_bernstein hCIndep hCY
    (fun i => Filter.Eventually.of_forall fun ω =>
      isSelfAdjoint_restrictCompression (U n) (Y i ω) (hsa i ω))
    (fun i => ?_) hCbound hR hv' ?_ (OperatorCompression.restrictCompression (U n) V) ?_
    (OperatorCompression.re_trace_restrictCompression_le (U n) V τ htrace) hu hthreshold'
  · rw [C.integral_comp_comm (𝕜 := ℂ) (Fₗ := U n →L[ℂ] U n) (Integrable.of_bound (hY i) R (hbound i)), hcenter i, map_zero]
  · exact OperatorCompression.sum_integral_restrict_variance_le_norm μ Finset.univ Y
      (U n) V hint hV v hVnorm
  · exact OperatorCompression.sum_integral_restrict_variance_le μ Finset.univ Y (U n) V hint hV

/-- The whole-output Bernstein inequality for a Borel measurable independent
family of compact self-adjoint operators (`app:ch_waves:thm:sampling`). All
strong measurability and integrability requirements are consequences of the
listed hypotheses. The sampling consumer must construct the family and supply
the displayed variance and finite orthonormal diagonal bounds. -/
theorem operatorBernstein_of_measurable
    (U : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (U n)]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    (hIndep : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (hc : ∀ i ω, IsCompactOperator (Y i ω))
    (hsa : ∀ i ω, IsSelfAdjoint (Y i ω))
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    {R v τ t : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ R)
    (hR : 0 < R) (hv : 0 < v) (V : H →L[ℂ] H) (hVnorm : ‖V‖ ≤ v)
    (hV : ∀ x, ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ Complex.re ⟪x, V x⟫_ℂ)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℂ e →
      ∑ j, Complex.re ⟪e j, V (e j)⟫_ℂ ≤ τ)
    (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ {ω | t < ‖∑ i, Y i ω‖} ≤ OperatorCompression.bernsteinTail R v τ t := by
  exact operatorBernstein U hmono hdense hIndep
    (fun i => (stronglyMeasurable_of_compact U hmono hdense (Y i) (hY i)
      (hc i) (hsa i)).aestronglyMeasurable)
    hc hsa hcenter hbound hR hv V hVnorm hV htrace ht hthreshold

end JanetCartan.HilbertOperatorBernstein
