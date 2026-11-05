module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.CoefficientBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets

/-!
# Carrier parameter phase and amplitude calculus

The parameter identity and finite mixed budgets used in
`app:ch_response:thm:response-literal-transfer` before
`app:ch_response:eq:direct-envelope-profile`.

* `carrierParameterPhase_identity_and_mixedJet_bound` combines the exact phase
  trade with joint physical/normalized-covector/parameter coefficient bounds.
  The unit-interval Hessian integral is differentiated from primitive smoothness
  and finite jet bounds, not from hypotheses on the resulting coefficient.
* `carrierParameterAmplitude_mixedJet_bound` bounds all joint jets of the full
  selected amplitude on the same carrier chart. Both physical positions and
  selector derivatives remain present. The first-order chain rule is
  `hasFDerivAt_parameterSelectedAmplitude`.
* `normalizedParameterAmplitude_eq_parameterSelectedAmplitude` gives the exact
  physical substitution `δ = ρ ε`. The identity
  `iteratedFDeriv_normalizedCovector_eq` and the estimate
  `norm_iteratedFDeriv_normalizedCovector_le` prove that each carrier factor of
  `ρ` cancels one primitive physical-covector weight `ρ⁻¹`, including for
  already differentiated physical amplitudes.

All budget constants are explicit and contain no frequency. Bounds hold on an
open buffer, hence on any fixed compact parameter box inside it. Covectors are
physical; unit-torus integer frequencies still enter as `2π k`.

These deductions are conditional on primitive phase homogeneity and smoothness,
buffered chart geometry, carrier jets, normalized Hessian jets, and the unshifted
amplitude and selector jets. `jc-compatible-phase-geometry` and
`jc-finite-fio-calculus` produce these inputs. Consumers `jc-response-near-carrier`
and `jc-response-complement` must instantiate them uniformly on actual supports.
No operator envelope theorem or comparison of torus and Lebesgue data is claimed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open scoped Matrix.Norms.Frobenius
open FourierIntegral

/-- Assembly of the exact identity and its joint coefficient budget on the
buffered carrier chart (`app:ch_response:thm:response-literal-transfer`,
`app:ch_response:eq:direct-envelope-profile`). The displacement is physical:
`δ = ρ ε`. Only primitive phase and carrier data are assumed; all segment,
physical differentiability, and coefficient regularity premises are discharged.
The constants are independent of `ρ`. -/
theorem carrierParameterPhase_identity_and_mixedJet_bound
    {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
    {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)}
    {C : Set (Euclidean p)}
    (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
    (hcD : Convex ℝ D) (hD0 : (0 : Euclidean n) ∉ D)
    (hζD : ∀ c ∈ C, ζ c ∈ D)
    (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
    (hS : ∀ x ∈ X, ContDiffOn ℝ ∞ (S x) D)
    (hhom : ∀ x ∈ X, PosHomogeneousOne (S x))
    (hH : ContDiffOn ℝ ∞
      (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))
    (hζ : ContDiffOn ℝ ∞ ζ C)
    {N k : ℕ} {H M : ℝ} (hM : 0 ≤ M)
    (hHjet : ∀ j ≤ N, ∀ z ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) z‖ ≤ H)
    (hζjet : ∀ j ≤ N + 1, ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) (hk : k ≤ N)
    {z : ParameterCoefficientSpace n p} (hz : z ∈ X ×ˢ V ×ˢ C)
    (v : Fin k → ParameterCoefficientSpace n p) :
    HasFDerivAt (fun c ↦ phaseIncrement S (ζ c) ρ z.1 (ρ • z.2.1))
      (parameterPhaseCoefficient S ζ z.1 z.2.1 z.2.2 (ρ • z.2.1)) z.2.2 ∧
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) z v‖ ≤
        parameterCoefficientJetBudget n p k H M * ∏ i, ‖v i‖ := by
  constructor
  · have hn : ρ⁻¹ • (ρ • z.2.1) = z.2.1 := by simp [smul_smul, hρ.ne']
    have hdζ := (hζ.contDiffAt (hC.mem_nhds hz.2.2)).differentiableAt (by simp)
    simpa only [hn] using hasFDerivAt_phaseIncrement_parameter_of_chart
      hD hcD hD0 (hS _ hz.1) (hhom _ hz.1) hdζ (hζD _ hz.2.2) hρ
      (δ := ρ • z.2.1) (by simpa only [hn] using hbuffer _ hz.2.2 _ hz.2.1)
  · exact norm_parameterPhaseCoefficient_mixedJet_le hX hD hV hC hcD hζD hbuffer
      hH hζ hM hHjet hζjet hk hz v

/-- Mixed amplitude budgets on the same buffered carrier chart, with both
physical positions and all selector derivatives retained
(`app:ch_response:eq:direct-envelope-profile`). The geometric mapping premises
of the composition estimate are derived from `hbuffer`. These pointwise bounds
hold on every compact box inside the open product domain. The primitive
normalized amplitude bounds must be supplied uniformly in frequency by the
actual FIO producer. -/
theorem carrierParameterAmplitude_mixedJet_bound
    {n r p : ℕ} {A : FullAmplitude n r} {q : Euclidean p × Euclidean n → ℂ}
    {ζ : Euclidean p → Euclidean n} {X Y V D : Set (Euclidean n)}
    {C : Set (Euclidean p)}
    (hX : IsOpen X) (hY : IsOpen Y) (hV : IsOpen V) (hD : IsOpen D) (hC : IsOpen C)
    (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
    {ρ : ℝ} {N k : ℕ}
    (hA : ContDiffOn ℝ N (normalizedFullAmplitude A ρ) (X ×ˢ Y ×ˢ D))
    (hq : ContDiffOn ℝ N q (C ×ˢ V)) (hζ : ContDiffOn ℝ N ζ C)
    {M Z : ℝ} {Q : ℕ → ℝ}
    (hAjet : ∀ i ≤ N, ∀ w ∈ X ×ˢ Y ×ˢ D,
      ‖iteratedFDeriv ℝ i (normalizedFullAmplitude A ρ) w‖ ≤ M)
    (hqjet : ∀ i ≤ N, ∀ w ∈ C ×ˢ V, ‖iteratedFDeriv ℝ i q w‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z)
    (hk : k ≤ N) {z : ParameterAmplitudePoint n (Euclidean p)}
    (hz : z ∈ (X ×ˢ Y ×ˢ V) ×ˢ C)
    (v : Fin k → ParameterAmplitudePoint n (Euclidean p)) :
    ‖iteratedFDeriv ℝ k (normalizedParameterAmplitude A q ζ ρ) z v‖ ≤
      parameterAmplitudeJetBudget M Q Z k * ∏ i, ‖v i‖ := by
  exact norm_normalizedParameterAmplitude_mixedJet_le
    ((hX.prod (hY.prod hV)).prod hC) (hX.prod (hY.prod hD)) (hC.prod hV) hC
    hA hq hζ
    (fun w hw ↦ ⟨hw.1.1, hw.1.2.1, hbuffer _ hw.2 _ hw.1.2.2⟩)
    (fun w hw ↦ ⟨hw.2, hw.1.2.2⟩) (fun w hw ↦ hw.2)
    hAjet hqjet hζjet hk hz v

end JanetCartan.ResponseTransfer
