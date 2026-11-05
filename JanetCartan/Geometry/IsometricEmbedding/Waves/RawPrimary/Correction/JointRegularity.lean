module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.NormalizedCoefficients

/-!
# Joint regularity of the literal full-modulation correction

For `app:ch_waves:eq:primary-algebraic-correction` and `app:ch_waves:thm:wkb`,
the SAME `fullCorrectionCovector` from `RawPrimary.Construction` is smooth in
`(x,z,ζ)`. The covariant reduced operator retains every Christoffel term.

The primitive inputs are the smooth immersion on `U`, the actual `Q` already
supplied to `T`, containment in `U` and the retained phase domain, and the fixed
nonzero adjugate entry. `FullModulation.exists_actual_positive_amplitude`
supplies the domain containments, using
`UniformCoefficients.exists_uniform_denominator_neighborhood` for the
denominator gap. The parent must retain the fixed nonzero adjugate entry on
its common refinement; a denominator gap alone is not used as that premise
here. The smoothness and literal
scalar PDE for `scalarAmplitude T Q F row col Φ Y r` are the first and sixth
conclusions of `LeadingWave.FullModulation.scalarAmplitude_spec`, for the SAME
flow, footpoint and initial datum. No regularity or cancellation of the
correction is assumed. The parent construction must instantiate these inputs
on its common family domain; this module does not assert that construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
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
  {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

-- Convert the coordinate product norm to the established Frobenius norm.
private def fullSymbolFromEntries : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

private theorem contDiffOn_fullStress_entry
    (hspace : ∀ w ∈ Ω, w.1 ∈ U) (i a b : Fin n) :
    ContDiffOn ℝ ∞ (fun w ↦ Q.1 w.1 i a b) Ω :=
  ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.comp_contDiffOn
    (contDiffOn_pi.mp Q.2.1 i)).comp contDiffOn_fst hspace

private theorem contDiffOn_fullGradient
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
  (phaseGradient_smooth T Q).comp
    (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase

/-- The actual full-phase symbol is jointly smooth, from the primitive frame
and the retained phase gradient. This supplies the matrix field for the
orthogonal inverse in `app:ch_waves:eq:primary-algebraic-correction`. -/
theorem contDiffOn_fullPhaseSymbol
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞
      (fun w ↦ reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) Ω := by
  apply fullSymbolFromEntries.contDiff.comp_contDiffOn
  exact contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦
    contDiffOn_reducedSymbol_entry (contDiffOn_fullStress_entry T Q hspace)
      (contDiffOn_fullGradient T Q hphase) i j

/-- Joint smoothness of the SAME selected adjugate column, used by
`fullLeadingCovector` and scalar transport in `app:ch_waves:thm:leading`. -/
theorem contDiffOn_fullNullvector
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (nullvector T Q col) Ω := by
  exact (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp
    (contDiffOn_rightNullvector_reducedSymbol (contDiffOn_fullStress_entry T Q hspace)
      (contDiffOn_fullGradient T Q hphase) col))

/-- Joint smoothness of the SAME selected adjugate row in the solvability
condition for `app:ch_waves:eq:primary-algebraic-correction`. -/
theorem contDiffOn_fullConullvector
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (conullvector T Q row) Ω :=
  contDiffOn_leftNullvector_reducedSymbol (contDiffOn_fullStress_entry T Q hspace)
    (contDiffOn_fullGradient T Q hphase) row

/-- The concrete leading covector is jointly smooth once the first conclusion
of `FullModulation.scalarAmplitude_spec` is supplied
(`app:ch_waves:thm:wkb`). -/
theorem contDiffOn_fullLeadingCovector
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω :=
  hα.smul (contDiffOn_fullNullvector T Q col hspace hphase)

/-- The actual covariant reduced operator of the concrete leading covector
is jointly smooth. Immersion supplies the inverse induced metric, including
all Christoffel terms (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffOn_fullLeadingCovector_reducedOperator
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (himm : IsImmersionOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞ (fun w ↦ reducedOperator F Q.1
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1) Ω := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_reducedOperator_joint hΩ (hF.comp contDiffOn_fst hspace)
    (fun w hw ↦ himm w.1 (hspace w hw)) (contDiffOn_fullStress_entry T Q hspace)
    (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα) i

/-- Joint smoothness of the literal full-phase orthogonal inverse. The phase
producer supplies characteristicity; only the fixed minor is a primitive gap
input (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffOn_fullSymbolInverse
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hminor : ∀ w ∈ Ω,
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0) :
    ContDiffOn ℝ ∞ (fun w ↦ orthogonalSymbolInverse
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) col) Ω :=
  contDiffOn_orthogonalSymbolInverse (contDiffOn_fullPhaseSymbol T Q hspace hphase)
    row col (fun w hw ↦ phase_characteristic T Q (hphase w hw)) hminor

/-- The SAME `fullCorrectionCovector` is jointly smooth in `(x,z,ζ)` from
primitive geometry, the fixed minor, and the smooth actual scalar amplitude.
This is the regularity assertion needed in `app:ch_waves:thm:wkb`, with the
literal correction of `app:ch_waves:eq:primary-algebraic-correction`. -/
theorem contDiffOn_fullCorrectionCovector
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (himm : IsImmersionOn F U)
    (hminor : ∀ w ∈ Ω,
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω := by
  have hR := contDiffOn_fullSymbolInverse T Q row col hspace hphase hminor
  have hP := contDiffOn_fullLeadingCovector_reducedOperator
    T Q F row col Φ Y r hΩ hspace hphase hF himm hα
  have hreal : ContDiffOn ℝ ∞ (fun w ↦ WithLp.toLp 2
      (orthogonalSymbolInverse
        (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) col *ᵥ
        reducedOperator F Q.1
          (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1)) Ω := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffOn.sum fun j _ ↦
      ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp_contDiffOn hR).mul
        (contDiffOn_pi.mp hP j)
  exact ((euclideanComplexInclusion (ι := Fin n)).contDiff.comp_contDiffOn hreal).const_smul
    Complex.I

/-- On the open full domain, joint smoothness supplies exactly the physical
differentiability inputs to `fullCorrectionCovector_cancel_of_scalar_transport`.
The scalar regularity is supplied by `FullModulation.scalarAmplitude_spec`;
the nullvector regularity is derived from the actual phase and frame
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullLeadingCovector_transport_differentiable
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    DifferentiableAt ℝ
        (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1 ∧
      ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1 := by
  constructor
  · exact ((hα.contDiffAt (hΩ.mem_nhds hw)).comp w.1
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · intro j
    exact ((contDiffAt_piLp 2).mp
      (((contDiffOn_fullNullvector T Q col hspace hphase).contDiffAt
        (hΩ.mem_nhds hw)).comp w.1
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)

/-- Domainwise complex cancellation for the SAME correction. The scalar PDE
is precisely the sixth conclusion of `FullModulation.scalarAmplitude_spec`;
physical differentiability is proved here rather than required separately.
The parent supplies the actual frame symmetry and denominator/minor gaps on
the common open domain (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_cancel_on_of_scalar_transport
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hminor : ∀ w ∈ Ω,
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col ≠ 0)
    (hQsym : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hden : ∀ w ∈ Ω, adaptedDenominator T Q row col w ≠ 0)
    (hpde : ∀ w ∈ Ω,
      fderiv ℝ (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2)) w.1
        (transportDirection T Q row col w) + transportPotential T Q F row col w *
          scalarAmplitude T Q F row col Φ Y r w = 0) :
    ∀ w ∈ Ω,
      Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
        Complex.ofReal *ᵥ (fun j ↦ fullCorrectionCovector T Q F row col Φ Y r w j)) +
        (fun i ↦ (reducedOperator F Q.1
          (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0 := by
  intro w hw
  obtain ⟨hαx, hkx⟩ := fullLeadingCovector_transport_differentiable
    T Q F row col Φ Y r hΩ hspace hphase hα hw
  exact fullCorrectionCovector_cancel_of_scalar_transport T Q F row col Φ Y r
    (hphase w hw) (hminor w hw) (hQsym w hw) hαx hkx (hden w hw) (hpde w hw)

end JanetCartan.RawPrimary
