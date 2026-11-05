module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Algebra

/-!
# Cancellation from the literal scalar transport equation

The inverse identities are specialized to the current full-modulation phase.
The actual scalar PDE, produced by `FullModulation.scalarAmplitude_spec`, gives
the cancellation for the SAME `fullCorrectionCovector` from `Construction`.
The reduced operator retains the induced Christoffel terms. This is the
algebraic step of `app:ch_waves:thm:wkb`, with both complex quadratures retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- Real-to-complex extension of the proved orthogonal inverse cancellation.
This is equality in the full complex vector space
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_complex_cancel {n : ℕ} {H : MetricTensor n}
    {row col : Fin n} (hH : H.det = 0) (hm : H.adjugate row col ≠ 0)
    {v : Fin n → ℝ} (hv : leftNullvector H row ⬝ᵥ v = 0) :
    Complex.I • (H.map Complex.ofReal *ᵥ
      (Complex.I • (fun j ↦ ((orthogonalSymbolInverse H col *ᵥ v) j : ℂ)))) +
      (fun i ↦ (v i : ℂ)) = 0 := by
  have he : H.map Complex.ofReal *ᵥ
      (fun j ↦ ((orthogonalSymbolInverse H col *ᵥ v) j : ℂ)) = fun i ↦ (v i : ℂ) := by
    funext i
    change (H.map Complex.ofRealHom *ᵥ
      (Complex.ofRealHom ∘ (orthogonalSymbolInverse H col *ᵥ v))) i = _
    rw [← RingHom.map_mulVec, symbol_orthogonalSymbolInverse hH hm hv]
    rfl
  rw [mulVec_smul, he, smul_smul, Complex.I_mul_I, neg_one_smul, neg_add_cancel]

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))

/-- The published current phase supplies characteristicity for completion
invertibility; only the fixed minor remains as a primitive gap input
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullSymbolCompletion_isUnit
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0) :
    IsUnit (orthogonalSymbolCompletion
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) col) :=
  orthogonalSymbolCompletion_isUnit (phase_characteristic T Q hw) hm

/-- Identification of the concrete full-phase inverse with the orthogonal
restricted inverse, without a separate eikonal hypothesis
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullSymbolInverse_eq_equiv_symm_projection
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (v : Euclidean n) :
    let H := reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)
    (orthogonalSymbolInverse H col).toEuclideanLin v =
      ((orthogonalSymbolEquiv (phase_characteristic T Q hw) hm).symm
        ((symbolRangePerp H row).orthogonalProjectionOnto v) : Euclidean n) :=
  orthogonalSymbolInverse_eq_equiv_symm_projection (phase_characteristic T Q hw) hm v

/-- The literal scalar PDE implies solvability of the actual covariant
reduced operator. The PDE and differentiability inputs are produced by
`FullModulation.scalarAmplitude_spec` on its open flow domain
(`app:ch_waves:thm:leading`). -/
theorem fullLeadingCovector_solvable_of_scalar_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0)
    (hpde : fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
      (transportDirection T Q row col w) + transportPotential T Q F row col w *
        scalarAmplitude T Q F row col Φ Y r w = 0) :
    conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 = 0 :=
  (scalar_reduction_iff T Q F row col hQ hα hk hd).mpr hpde

/-- Cancellation for the published `fullCorrectionCovector`, derived from
the actual scalar transport equation and fixed minor. No correction identity,
inverse existence, or reduced solvability is assumed
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_cancel_of_scalar_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T)
    (hm : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : DifferentiableAt ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0)
    (hpde : fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
      (transportDirection T Q row col w) + transportPotential T Q F row col w *
        scalarAmplitude T Q F row col Φ Y r w = 0) :
    Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
      Complex.ofReal *ᵥ (fun j ↦ fullCorrectionCovector T Q F row col Φ Y r w j)) +
      (fun i ↦ (reducedOperator F Q.1
        (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0 := by
  simpa only [fullCorrectionCovector, PiLp.smul_apply, euclideanComplexInclusion_apply,
    PiLp.toLp_apply, Pi.smul_def] using orthogonalSymbolInverse_complex_cancel
      (H := reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2))
      (phase_characteristic T Q hw) hm
      (fullLeadingCovector_solvable_of_scalar_transport T Q F row col Φ Y r hQ hα hk hd hpde)

/-- The real quadrature of the concrete correction vanishes, as prescribed
by the factor `i` in `app:ch_waves:eq:primary-algebraic-correction`. -/
theorem fullCorrectionCovector_re (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (j : Fin n) :
    (fullCorrectionCovector T Q F row col Φ Y r w j).re = 0 := by
  simp [fullCorrectionCovector]

/-- The imaginary quadrature is precisely the real orthogonal inverse of
the covariant reduced operator (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_im (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (j : Fin n) :
    (fullCorrectionCovector T Q F row col Φ Y r w j).im =
      (orthogonalSymbolInverse
        (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) col *ᵥ
        reducedOperator F Q.1 (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1) j := by
  simp [fullCorrectionCovector]

end JanetCartan.RawPrimary
