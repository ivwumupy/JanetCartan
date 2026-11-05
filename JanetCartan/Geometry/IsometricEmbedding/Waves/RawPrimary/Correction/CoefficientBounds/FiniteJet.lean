module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.PotentialFormula

/-!
# Primitive finite jet of the orthogonal correction

The consumer is the SAME `fullCorrectionCovector` in `RawPrimary.Construction`.
For `app:ch_waves:eq:primary-algebraic-correction`, only the immersion second
jet and the first joint jet of `(Q, phaseGradient, scalarAmplitude)` enter.
The induced Christoffel coefficients are retained literally.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary.CorrectionBounds
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Primitive values in `app:ch_waves:eq:primary-algebraic-correction`:
stress frame, phase gradient, and transported scalar. -/
abbrev Values (n : ℕ) := Input n × ℝ

/-- The leading covector as a polynomial in the primitive values
(`app:ch_waves:thm:wkb`). -/
def leadingValue (col : Fin n) (v : Values n) : Euclidean n := v.2 • right col v.1

/-- The primitive symbol, before imposing characteristicity
(`app:ch_waves:eq:primary-algebraic-correction`). -/
def symbolValue (v : Values n) : MetricTensor n := reducedSymbol v.1.1 v.1.2

/-- The correction uses one joint derivative and two immersion derivatives
(`app:ch_waves:eq:WKB-grading`). No correction or inverse is an input. -/
abbrev Jet (n N : ℕ) (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :=
  StressJet n N × (Values n × ((Euclidean n × Z) →L[ℝ] Values n))

/-- Polynomial smoothness of the actual leading formula
(`app:ch_waves:thm:wkb`). -/
theorem contDiff_leadingValue (col : Fin n) : ContDiff ℝ ∞ (leadingValue col) :=
  contDiff_snd.smul ((smooth_right col).comp contDiff_fst)

private def matrixOfEntries : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- Polynomial smoothness of the symbol in its primitive values
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiff_symbolValue : ContDiff ℝ ∞ (@symbolValue n) := by
  apply matrixOfEntries.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ∞ (fun v : Values n ↦ ∑ a, v.1.1 i j a * v.1.2 a)
  apply ContDiff.sum
  intro a _
  exact ((Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mp contDiff_fst.fst i)).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp contDiff_fst.snd)

/-- The physical derivative of the leading covector computed from primitive
jets (`app:ch_waves:eq:primary-algebraic-correction`). -/
def leadingJetDerivative (col : Fin n) (p : Jet n N Z) (a : Fin n) : Euclidean n :=
  fderiv ℝ (leadingValue col) p.2.1 (p.2.2 (EuclideanSpace.single a 1, 0))

/-- The full reduced operator on the leading covector, including its induced
connection, as a finite jet formula (`app:ch_waves:thm:wkb`). -/
def reducedLeadingJet (col : Fin n) (p : Jet n N Z) : Fin n → ℝ :=
  fun i ↦ ∑ a, ∑ b, p.2.1.1.1 i a b *
    (((leadingJetDerivative col p a) b + (leadingJetDerivative col p b) a) / 2 -
      ∑ j, secondJetChristoffel p.1 a b j * leadingValue col p.2.1 j)

/-- Literal `i R P b₀` from primitive jets
(`app:ch_waves:eq:primary-algebraic-correction`). -/
def correctionJetValue (col : Fin n) (p : Jet n N Z) : EuclideanSpace ℂ (Fin n) :=
  Complex.I • euclideanComplexInclusion (WithLp.toLp 2
    (orthogonalSymbolInverse (symbolValue p.2.1) col *ᵥ reducedLeadingJet col p))

/-- The reduced operator jet is smooth under the primitive metric gap alone;
no correction regularity is assumed (`app:ch_waves:eq:WKB-grading`). -/
theorem contDiffAt_reducedLeadingJet (col : Fin n) {p : Jet n N Z}
    (hmet : IsUnit (firstJetMetric p.1.1)) :
    ContDiffAt ℝ ∞ (reducedLeadingJet col) p := by
  have hd (a b : Fin n) : ContDiffAt ℝ ∞
      (fun q : Jet n N Z ↦ leadingJetDerivative col q a b) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.contDiffAt.comp p
      ((((contDiff_leadingValue col).fderiv_right (by simp)).contDiffAt.comp p
        contDiffAt_snd.fst).clm_apply (contDiffAt_snd.snd.clm_apply contDiffAt_const))
  have hk (j : Fin n) : ContDiffAt ℝ ∞
      (fun q : Jet n N Z ↦ leadingValue col q.2.1 j) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp p
      ((contDiff_leadingValue col).contDiffAt.comp p contDiffAt_snd.fst)
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.contDiffAt.comp p
    (contDiffAt_pi.mp contDiffAt_snd.fst.fst.fst i)).mul
    (((hd a b).add (hd b a) |>.div_const 2).sub (ContDiffAt.sum fun j _ ↦
      ((contDiffAt_secondJetChristoffel hmet a b j).comp p contDiffAt_fst).mul (hk j)))

/-- Smoothness of the complete correction follows from primitive geometric
gaps. This uses the proved Gram inverse, rather than an inverse estimate or
an assumed successful wave (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem contDiffAt_correctionJetValue (row col : Fin n) {p : Jet n N Z}
    (hmet : IsUnit (firstJetMetric p.1.1))
    (hchar : (symbolValue p.2.1).det = 0)
    (hminor : (symbolValue p.2.1).adjugate row col ≠ 0) :
    ContDiffAt ℝ ∞ (correctionJetValue col) p := by
  apply ContDiffAt.const_smul Complex.I
  apply (euclideanComplexInclusion (ι := Fin n)).contDiff.contDiffAt.comp p
  apply (contDiffAt_piLp 2).mpr
  intro i
  have hR := (contDiffAt_orthogonalSymbolInverse hchar hminor (m := ∞)).comp p
    (contDiff_symbolValue.contDiffAt.comp p contDiffAt_snd.fst)
  have hP := contDiffAt_reducedLeadingJet col hmet
  change ContDiffAt ℝ ∞ (fun q : Jet n N Z ↦
    ∑ j, orthogonalSymbolInverse (symbolValue q.2.1) col i j * reducedLeadingJet col q j) p
  apply ContDiffAt.sum
  intro j _
  exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt.comp p
    hR).mul (contDiffAt_pi.mp hP j)

/-- The actual primitive jet field for joint physical and spectator variables
(`app:ch_waves:eq:WKB-grading`). -/
def primitiveJet (F : Euclidean n → Euclidean N) (v : Euclidean n × Z → Values n)
    (w : Euclidean n × Z) : Jet n N Z := (stressJet F w.1, v w, fderiv ℝ v w)

/-- Identification with the original covariant reduced operator, with all
Christoffel terms. This is the connection to the concrete consumer
`fullCorrectionCovector` (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem reducedLeadingJet_primitiveJet (col : Fin n)
    {F : Euclidean n → Euclidean N} {v : Euclidean n × Z → Values n}
    {w : Euclidean n × Z} (hF : ContDiffAt ℝ ∞ F w.1)
    (hv : DifferentiableAt ℝ v w) :
    reducedLeadingJet col (primitiveJet F v w) =
      reducedOperator F (fun x ↦ (v (x, w.2)).1.1)
        (fun x ↦ leadingValue col (v (x, w.2))) w.1 := by
  have he : HasFDerivAt (fun x : Euclidean n ↦ (x, w.2))
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) w.1 :=
    (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
  have hd (a b : Fin n) :
      partialDeriv (fun x ↦ leadingValue col (v (x, w.2)) b) w.1 a =
        leadingJetDerivative col (primitiveJet F v w) a b := by
    have hh := (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp w.1
      (((contDiff_leadingValue col).differentiable (by simp)).differentiableAt.hasFDerivAt.comp
        w.1 (hv.hasFDerivAt.comp w.1 he))
    change HasFDerivAt (fun x ↦ leadingValue col (v (x, w.2)) b) _ w.1 at hh
    rw [partialDeriv, hh.fderiv]
    rfl
  funext i
  simp only [reducedLeadingJet, reducedOperator, tensorPairing, symmCovariantDeriv,
    hd, primitiveJet, secondJetChristoffel_eq_at hF]

end JanetCartan.RawPrimary.CorrectionBounds
