module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CanonicalSuperposition
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Coefficients
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Literal full-modulation raw formulas

Shared definitions for the final construction in `app:ch_waves:thm:individual`.
They retain `T.currentChart`, the full-modulation characteristic scalar, its
original fixed adjugate column and the original wide-band input. No phase,
amplitude, correction or successful operator is chosen through a new record.

The Gram completion below gives a total formula for the orthogonal restricted
inverse in `app:ch_waves:eq:primary-algebraic-correction`. Its inverse identities,
smoothness and uniform estimates are separate proof obligations. In particular,
defining the resulting raw field does NOT establish the source theorem.
-/

@[expose] public noncomputable section

open Set Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase NullTransport

/-- The orthogonal Gram completion for the source's restricted symbol inverse.
On the characteristic set with the selected nonzero adjugate column, its inverse
must be proved to exist (`app:ch_waves:eq:primary-algebraic-correction`). -/
def orthogonalSymbolCompletion {n : ℕ} (H : MetricTensor n) (col : Fin n) : MetricTensor n :=
  H.transpose * H + vecMulVec (rightNullvector H col) (rightNullvector H col)

/-- Explicit formula for `(H|kᗮ→lᗮ)⁻¹ Π_lᗮ`. Its identification with that
restricted inverse is an outstanding producer obligation, not an assumption
(`app:ch_waves:eq:primary-algebraic-correction`). -/
def orthogonalSymbolInverse {n : ℕ} (H : MetricTensor n) (col : Fin n) : MetricTensor n :=
  (orthogonalSymbolCompletion H col)⁻¹ * H.transpose

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))

/-- The literal leading covector, from the original full-modulation scalar
and fixed adjugate column (`app:ch_waves:thm:leading`). -/
def fullLeadingCovector (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Euclidean n :=
  scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w

/-- Characteristicity of the published current phase proves the actual
leading null relation (`app:ch_waves:thm:wkb`); no eikonal hypothesis is added. -/
theorem fullLeadingCovector_null (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T) :
    reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
      (fun j ↦ fullLeadingCovector T Q F row col Φ Y r w j) = 0 := by
  change reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
    (scalarAmplitude T Q F row col Φ Y r w • (fun j ↦ nullvector T Q col w j)) = 0
  rw [mulVec_smul, (nullvector_relations T Q row col hw).1, smul_zero]

/-- The full covector is linear in the original initial scalar, with the same
geometry, flow and footpoint (`app:ch_waves:eq:WKB-W`). -/
def fullLeadingCovectorLinearMap : (Euclidean (n - 1) × Euclidean 3 → ℝ) →ₗ[ℝ]
    (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean n) where
  toFun := fullLeadingCovector T Q F row col Φ Y
  map_add' r s := by
    funext w
    have he := congrFun ((scalarAmplitudeLinearMap T Q F row col Φ Y).map_add r s) w
    change scalarAmplitude T Q F row col Φ Y (r + s) w =
      scalarAmplitude T Q F row col Φ Y r w + scalarAmplitude T Q F row col Φ Y s w at he
    simp only [fullLeadingCovector, he, add_smul, Pi.add_apply]
  map_smul' c r := by
    funext w
    have he := congrFun ((scalarAmplitudeLinearMap T Q F row col Φ Y).map_smul c r) w
    change scalarAmplitude T Q F row col Φ Y (c • r) w =
      c * scalarAmplitude T Q F row col Φ Y r w at he
    simp only [fullLeadingCovector, he, mul_smul, Pi.smul_apply, RingHom.id_apply]

/-- The concrete correction `i R P_G b₀`, using the original Christoffel
terms and the orthogonal inverse formula. Its cancellation, regularity and
budgets remain to be proved (`app:ch_waves:eq:primary-algebraic-correction`). -/
def fullCorrectionCovector (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : EuclideanSpace ℂ (Fin n) :=
  Complex.I • euclideanComplexInclusion (WithLp.toLp 2
    ((orthogonalSymbolInverse
      (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) col) *ᵥ
      reducedOperator F Q.1 (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1))

/-- The actual formulas with the carrier label retained and the full covector
free. The supplied flow/footpoint must be instantiated from the full-modulation
constructor on a common buffer (`app:ch_waves:eq:WKB-W`). -/
def fullPrimaryAtom (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (p : Euclidean n × Euclidean (n - 1)) : EuclideanSpace ℂ (Fin N) :=
  canonicalAtom F τ (fun p ↦ phase T Q p.1 p.2)
    (fun p ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
    (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2))) p

/-- The concrete raw displacement formula on the original annular Hilbert
input. The detector/high-pass `d` acts only on that datum, before any spatial
initial cutoff (`app:ch_waves:thm:individual`). -/
def fullPrimaryWave {J : ℕ} (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (d : Euclidean (n - 1) → ℂ)
    (v : RawInputPartition.WideInput n J) : Euclidean n → EuclideanSpace ℂ (Fin N) :=
  wideSuperposition
    (fun p ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
      (p.1, T.reference.spatialPatch z + τ • p.2)) d v

/-- The concrete full-modulation formula is exactly the canonical
superposition whose derivative representation has been proved. Applying that
theorem still requires the local regularity of these actual coefficients
(`app:ch_waves:eq:individual-representation`). -/
theorem fullPrimaryWave_eq_canonicalWideWave {J : ℕ} (τ : ℝ)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (z : Euclidean 3)
    (d : Euclidean (n - 1) → ℂ) (v : RawInputPartition.WideInput n J) :
    fullPrimaryWave T Q F row col Φ Y τ r z d v =
      canonicalWideWave F τ (fun p ↦ phase T Q p.1 p.2)
        (fun p ↦ euclideanComplexInclusion
          (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
        (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2)))
        (T.reference.spatialPatch z) d v := rfl

/-- The separate zero atom uses exactly the original carrier and is never
multiplied by a high-pass or annular half derivative
(`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryAtom_zero_measure (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) (x : Euclidean n) :
    (∫ η, fullPrimaryAtom T Q F row col Φ Y τ r z
        (x, T.reference.spatialPatch z + τ • η) ∂Measure.dirac 0) =
      fullPrimaryAtom T Q F row col Φ Y τ r z (x, T.reference.spatialPatch z) := by
  simp

/-- The central phase is the SAME published current carrier, with no new
Hamilton chart (`app:ch_waves:eq:individual-representation`). -/
theorem fullPrimaryPhase_on_carrier (x : Euclidean n) (z : Euclidean 3) :
    phase T Q x (T.reference.spatialPatch z) = T.carrier Q x z := rfl

end JanetCartan.RawPrimary
