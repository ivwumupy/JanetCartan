module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ComplexWKB.Operator

/-!
# WKB cancellation for the published full-modulation correction

The SAME `fullCorrectionCovector` is the complex orthogonal restricted inverse
correction of `app:ch_waves:eq:primary-algebraic-correction`. Its cancellation
is obtained by instantiating `WKB.algebraicCorrection_cancel`, and the concrete
Christoffel-inclusive operator has the exact cubic residual of
`app:ch_waves:eq:WKB-residual`.

The scalar PDE and leading differentiability inputs are supplied by
`FullModulation.scalarAmplitude_spec` on its open flow domain. Differentiability
of the actual correction is an explicit input to the residual, owned by
`Correction/JointRegularity`; final assembly must instantiate it. These are
conditional local identities, not an unconditional existence or estimate theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
  {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}

/-- The primitive leading inputs give the physical differentiability consumed
by the WKB product rule (`app:ch_waves:eq:WKB-residual`). -/
theorem fullLeadingCovector_differentiableAt
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1) :
    DifferentiableAt ℝ (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 :=
  hα.smul ((differentiableAt_piLp 2).mpr hk)

/-- Physical phase differentiability follows from the published phase on its
larger open box, rather than being an extra WKB assumption
(`app:ch_waves:eq:WKB-residual`). -/
theorem fullPhase_physical_differentiableAt
    (hw : (w.1, w.2.2) ∈ phaseDomain T) :
    DifferentiableAt ℝ (fun x ↦ phase T Q x w.2.2) w.1 := by
  have hs := (phase_smooth T Q).mono
    (ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius))
  have hd := ((hs.differentiableOn (by simp)) (w.1, w.2.2) hw).differentiableAt
    (isOpen_ball.mem_nhds hw)
  have hi : DifferentiableAt ℝ (fun x : Euclidean n ↦ (x, w.2.2)) w.1 :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have hc := hd.comp w.1 hi
  exact hc

/-- The exact eikonal cancellation for the actual leading covector under the
concrete WKB principal symbol (`app:ch_waves:eq:WKB-residual`). -/
theorem fullLeadingCovector_principalSymbol_null
    (hw : (w.1, w.2.2) ∈ phaseDomain T) (hQ : ∀ i, (Q.1 w.1 i).IsSymm) :
    WKB.principalSymbol (complexReducedDerivative Q.1) (fun x ↦ phase T Q x w.2.2) w.1
      (euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r w)) = 0 := by
  rw [complexReduced_principalSymbol Q.1 _ _ hQ, complexSymbolMap_inclusion]
  have he : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).toEuclideanLin
      (fullLeadingCovector T Q F row col Φ Y r w) = 0 := by
    apply WithLp.ofLp_injective
    exact fullLeadingCovector_null T Q F row col Φ Y r hw
  change euclideanComplexInclusion
    ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).toEuclideanLin _) = 0
  rw [he, map_zero]

/-- On the transport-solvable input the published correction is literally
`WKB.algebraicCorrection` for the proved complex restricted equivalence.
The membership premise is discharged from the scalar PDE in
`fullCorrectionCovector_wkb_cancel_of_scalar_transport`
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_eq_algebraicCorrection
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hp : euclideanComplexInclusion (WithLp.toLp 2 (reducedOperator F Q.1
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1)) ∈
        complexSymbolRangePerp (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) row) :
    fullCorrectionCovector T Q F row col Φ Y r w =
      WKB.algebraicCorrection _ _ (complexOrthogonalSymbolEquiv (phase_characteristic T Q hw) hm)
        ⟨euclideanComplexInclusion (WithLp.toLp 2 (reducedOperator F Q.1
          (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1)), hp⟩ := by
  rw [WKB.algebraicCorrection, complexOrthogonalSymbolEquiv_symm_apply,
    complexSymbolMap_inclusion]
  rfl

/-- The scalar PDE puts both quadratures in the actual complex range, and
the proved restricted equivalence instantiates `WKB.algebraicCorrection_cancel`.
No cancellation or inverse existence is assumed
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_wkb_cancel_of_scalar_transport
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0)
    (hpde : fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
      (transportDirection T Q row col w) + transportPotential T Q F row col w *
        scalarAmplitude T Q F row col Φ Y r w = 0) :
    Complex.I • WKB.principalSymbol (complexReducedDerivative Q.1)
      (fun x ↦ phase T Q x w.2.2) w.1 (fullCorrectionCovector T Q F row col Φ Y r w) +
      WKB.firstOrderApply (complexReducedDerivative Q.1) (complexReducedValue F Q.1)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
          w.1 = 0 := by
  have ha := fullLeadingCovector_differentiableAt T Q F row col Φ Y r hα hk
  have hc : DifferentiableAt ℝ (fun x ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    euclideanComplexInclusion.differentiableAt.comp w.1 ha
  have hp : euclideanComplexInclusion (WithLp.toLp 2 (reducedOperator F Q.1
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1)) ∈
        complexSymbolRangePerp (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) row := by
    rw [mem_complexSymbolRangePerp]
    simp only [euclideanComplexInclusion_apply, Complex.ofReal_re,
      Complex.ofReal_im]
    constructor
    · exact fullLeadingCovector_solvable_of_scalar_transport T Q F row col Φ Y r hQ hα hk hd hpde
    · simp [dotProduct]
  rw [← complexReducedOperator_eq_firstOrder F Q.1 hc,
    complexReducedOperator_inclusion F Q.1 hQ ha,
    fullCorrectionCovector_eq_algebraicCorrection T Q F row col Φ Y r hw hm hp]
  apply WKB.algebraicCorrection_cancel
  intro v
  rw [complexReduced_principalSymbol Q.1 _ _ hQ]
  rfl

/-- Exact cubic residual for the SAME two-term covector used by
`fullPrimaryAtom`, with every inverse-frequency power retained
(`app:ch_waves:eq:WKB-residual`). The scalar PDE comes from
`FullModulation.scalarAmplitude_spec`; `hb` is supplied by
`Correction/JointRegularity` and must be discharged in final assembly. -/
theorem fullTwoTermWave_reduced_residual
    {lam : ℝ} (hlam : lam ≠ 0)
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0)
    (hpde : fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
      (transportDirection T Q row col w) + transportPotential T Q F row col w *
        scalarAmplitude T Q F row col Φ Y r w = 0)
    (hb : DifferentiableAt ℝ (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) :
    complexReducedOperator F Q.1
      (twoTermWave lam (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 =
      waveCarrier lam (fun x ↦ phase T Q x w.2.2) w.1 •
        (((lam : ℂ)⁻¹)^3 • complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) := by
  have hφ := fullPhase_physical_differentiableAt T Q hw
  have ha : DifferentiableAt ℝ (fun x ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    euclideanComplexInclusion.differentiableAt.comp w.1
      (fullLeadingCovector_differentiableAt T Q F row col Φ Y r hα hk)
  have ht : DifferentiableAt ℝ
      (twoTermWave lam (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    (hasFDerivAt_waveCarrier hφ).differentiableAt.smul
      ((ha.add (hb.const_smul ((lam : ℂ)⁻¹))).const_smul (((lam : ℂ)⁻¹)^2))
  rw [complexReducedOperator_eq_firstOrder F Q.1 ht,
    complexReducedOperator_eq_firstOrder F Q.1 hb]
  exact WKB.firstOrder_twoTermWave_residual _ _ hlam hφ ha hb
    (fullLeadingCovector_principalSymbol_null T Q F row col Φ Y r hw hQ)
    (fullCorrectionCovector_wkb_cancel_of_scalar_transport T Q F row col Φ Y r
      hw hm hQ hα hk hd hpde)

/-- The manuscript's small-parameter form `P vτ = exp(i S/τ) τ³ P b₁`, for
the literal amplitudes in `fullPrimaryAtom`. This is the reduced-vector identity
of `app:ch_waves:eq:WKB-residual`, under the same primitive scalar PDE and
correction differentiability inputs as `fullTwoTermWave_reduced_residual`. -/
theorem fullTwoTermWave_reduced_residual_tau
    {τ : ℝ} (hτ : τ ≠ 0)
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0)
    (hpde : fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
      (transportDirection T Q row col w) + transportPotential T Q F row col w *
        scalarAmplitude T Q F row col Φ Y r w = 0)
    (hb : DifferentiableAt ℝ (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) :
    complexReducedOperator F Q.1
      (twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
        ((τ : ℂ)^3 • complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) := by
  simpa only [LeadingWave.waveCarrier_inv_eq_exp_div, Complex.ofReal_inv, inv_inv] using
    fullTwoTermWave_reduced_residual T Q F row col Φ Y r (inv_ne_zero hτ)
      hw hm hQ hα hk hd hpde hb

end JanetCartan.RawPrimary
