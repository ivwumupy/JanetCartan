module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.CoefficientBudgets.Integrand
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Finite mixed budgets for the normalized parameter phase coefficient

The coefficient `C_c` following the averaged mixed matrix in
`app:ch_response:thm:response-literal-transfer` is the integral of a bilinear
contraction of the primitive covector Hessian and the carrier differential.
Composition and product bounds are proved in `CoefficientBudgets.Integrand`;
here they justify differentiating the actual integral and give the coefficient
budgets needed for `app:ch_response:eq:direct-envelope-profile`.

All variables `(x, ε, c)` are differentiated jointly, so the operator norm bounds
control every mixed derivative. The phase chart is open and convex in its
covector variable, and the normalized segments stay inside it. No smoothness at
zero covector is imposed. The primitive functions are smooth on the chart, but
the quantitative bound at order `N` uses only Hessian jets through `N` and
carrier jets through `N+1`. There is no frequency in the constants.

The consuming parameter-phase construction must supply the primitive chart,
carrier and jet hypotheses. These conditional estimates do not assert their
realization or the final operator envelope theorem.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer

set_option maxSynthPendingDepth 4

section
variable {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)}
  {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hH : ContDiffOn ℝ ∞
    (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))
  (hζ : ContDiffOn ℝ ∞ ζ C)

include hX hD hcD hζD hbuffer hH in
/-- The coefficient in `app:ch_response:thm:response-literal-transfer` equals
the integral of the actual contracted Hessian, by continuity on the segment. -/
theorem parameterPhaseCoefficient_eq_integral
    {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    parameterPhaseCoefficient S ζ q.1 q.2.1 q.2.2 =
      ∫ t in (0 : ℝ)..1, parameterCoefficientIntegrand S ζ t q := by
  have hh : ContinuousOn (fun t : ℝ ↦
      fderiv ℝ (fderiv ℝ (S q.1)) (ζ q.2.2 + t • q.2.1)) (Icc 0 1) := by
    intro t ht
    exact ((hH.contDiffAt ((hX.prod hD).mem_nhds
      ⟨hq.1, hcD.add_smul_mem (hζD _ hq.2.2)
        (hbuffer _ hq.2.2 _ hq.2.1) ht⟩)).continuousAt.comp
      (continuousAt_const.prodMk
        (continuousAt_const.add (continuousAt_id.smul continuousAt_const)))).continuousWithinAt
  rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hh
  have hi : IntervalIntegrable (fun t : ℝ ↦
      fderiv ℝ (fderiv ℝ (S q.1)) (ζ q.2.2 + t • q.2.1)) MeasureTheory.volume 0 1 :=
    hh.intervalIntegrable
  exact ((parameterCoefficientContraction n p (fderiv ℝ ζ q.2.2)).intervalIntegral_comp_comm hi).symm

include hX hD hV hC hcD hζD hbuffer hH hζ

/-- Smoothness of the actual coefficient is a consequence of primitive
smoothness and compact integration, not an input
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterPhaseCoefficient_contDiffOn :
    ContDiffOn ℝ ∞ (fun q : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ q.1 q.2.1 q.2.2) (X ×ˢ V ×ˢ C) := by
  have hi : ContDiffOn ℝ ∞ (fun q : ParameterCoefficientSpace n p ↦
      ∫ t in (0 : ℝ)..1, parameterCoefficientIntegrand S ζ t q) (X ×ˢ V ×ˢ C) := by
    apply contDiffOn_fixedIntervalIntegral (a := (0 : ℝ)) (b := 1)
      (F := fun z : ℝ × ParameterCoefficientSpace n p ↦ parameterCoefficientIntegrand S ζ z.1 z.2)
      (hX.prod (hV.prod hC))
    intro z hz
    exact parameterCoefficientIntegrand_contDiffAt hX hD hC hcD hζD hbuffer hH hζ
      (by simpa using hz)
  exact hi.congr fun q hq ↦ parameterPhaseCoefficient_eq_integral hX hD hcD hζD hbuffer hH hq

/-- Differentiation under the unit-interval integral for the actual parameter
coefficient. Domination follows from the primitive finite jets
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem iteratedFDeriv_parameterPhaseCoefficient {N k : ℕ} {A M : ℝ}
    (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) q =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (parameterCoefficientIntegrand S ζ t) q := by
  have he : (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) =ᶠ[𝓝 q]
      (fun w ↦ ∫ t in (0 : ℝ)..1, parameterCoefficientIntegrand S ζ t w) := by
    filter_upwards [(hX.prod (hV.prod hC)).mem_nhds hq] with w hw
    exact parameterPhaseCoefficient_eq_integral hX hD hcD hζD hbuffer hH hw
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  apply NormalComparison.iteratedFDeriv_unitIntervalIntegral
    (H := fun z ↦ parameterCoefficientIntegrand S ζ z.1 z.2)
    (B := fun j ↦ parameterCoefficientJetBudget n p j A M) (hX.prod (hV.prod hC))
    (fun z hz ↦ parameterCoefficientIntegrand_contDiffAt hX hD hC hcD hζD hbuffer hH hζ hz)
    _ hq
  intro j hj t ht w hw
  exact norm_parameterCoefficientIntegrand_jet_le hX hD hV hC hcD hζD hbuffer hH hζ
    hM hA hb (hj.trans hk) ht hw

/-- Explicit finite mixed physical/normalized-covector/parameter derivative
budget for the actual `C_c` in `app:ch_response:eq:direct-envelope-profile`.
Only the primitive Hessian and carrier jets are bounded as hypotheses. -/
theorem norm_iteratedFDeriv_parameterPhaseCoefficient_le {N k : ℕ} {A M : ℝ}
    (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) q‖ ≤
      parameterCoefficientJetBudget n p k A M := by
  rw [iteratedFDeriv_parameterPhaseCoefficient hX hD hV hC hcD hζD hbuffer hH hζ hM hA hb hk hq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (fun t ht ↦ norm_parameterCoefficientIntegrand_jet_le hX hD hV hC hcD hζD hbuffer hH hζ
      hM hA hb hk (by simpa using uIoc_subset_uIcc ht) hq)

/-- The sum-of-suprema budget on any closed parameter box (or any other subset
of the buffered domain). This is the finite seminorm used in
`app:ch_response:eq:direct-envelope-profile`; no smoothness of the coefficient
is assumed. -/
theorem cNorm_parameterPhaseCoefficient_le {N : ℕ} {A M : ℝ}
    (hA₀ : 0 ≤ A) (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    {K : Set (ParameterCoefficientSpace n p)} (hK : K ⊆ X ×ˢ V ×ˢ C) :
    cNorm K N (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) ≤
        ∑ k ∈ Finset.range (N + 1), parameterCoefficientJetBudget n p k A M := by
  apply cNorm_le_sum_of_bounds
  · intro k _
    unfold parameterCoefficientJetBudget
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    positivity
  · intro k hk q hq
    exact norm_iteratedFDeriv_parameterPhaseCoefficient_le hX hD hV hC hcD hζD hbuffer hH hζ
      hM hA hb hk (hK hq)

/-- Evaluation in arbitrary physical, normalized covector and parameter
 directions gives the mixed derivative bounds consumed by the transfer
 induction (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_parameterPhaseCoefficient_mixedJet_le {N k : ℕ} {A M : ℝ}
    (hM : 0 ≤ M)
    (hA : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ A)
    (hb : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C)
    (v : Fin k → ParameterCoefficientSpace n p) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) q v‖ ≤
      parameterCoefficientJetBudget n p k A M * ∏ i, ‖v i‖ := by
  apply (ContinuousMultilinearMap.le_opNorm _ v).trans
  exact mul_le_mul_of_nonneg_right
    (norm_iteratedFDeriv_parameterPhaseCoefficient_le hX hD hV hC hcD hζD hbuffer hH hζ
      hM hA hb hk hq) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

end
end JanetCartan.ResponseTransfer
