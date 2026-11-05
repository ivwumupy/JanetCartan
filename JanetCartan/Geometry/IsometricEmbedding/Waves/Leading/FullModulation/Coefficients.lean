module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.PositiveBound

/-!
# Literal null transport coefficients with independent full modulation

The parameter is `(z, ζ)` with `z : Euclidean 3` and an independent full
spatial covector `ζ`. The phase and coefficients depend on `ζ`; the prescribed
initial scalar depends on `(y,z)`. On the carrier graph `ζ = spatialPatch z`,
all coefficients agree exactly with the published actual transport formulas.

These definitions and algebraic identities are the shared inputs for the
full-parameter extension in `app:ch_waves:thm:leading`. Quantitative gaps,
coefficient estimates, and actual full-parameter flow construction remain
separate obligations; no successful-transport interface is postulated here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Fixed adjugate column for the full phase, retaining the independent carrier
label (`app:ch_waves:thm:leading`). -/
def nullvector (col : Fin n) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Euclidean n :=
  WithLp.toLp 2 (rightNullvector (reducedSymbol (Q.1 w.1)
    (phaseGradient T Q w.1 w.2.2)) col)

/-- Fixed adjugate row for the same full phase (`app:ch_waves:thm:leading`). -/
def conullvector (row : Fin n) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Fin n → ℝ :=
  leftNullvector (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)) row

/-- Denominator in the original adapted normal, without rotating the projected
stress frame (`app:ch_waves:thm:leading`). -/
def adaptedDenominator (row col : Fin n)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : ℝ :=
  adaptedTimeCoefficient (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)
    row col T.data.adapted.normal

/-- Normalized full-parameter transport direction
(`app:ch_waves:thm:leading`). -/
def transportDirection (row col : Fin n)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Euclidean n :=
  WithLp.toLp 2 (fun a ↦ transportField (Q.1 w.1) (conullvector T Q row w)
    (fun j ↦ nullvector T Q col w j) a / adaptedDenominator T Q row col w)

/-- Normalized potential, including the physical covariant derivative of the
full-covector null column (`app:ch_waves:thm:leading`). -/
def transportPotential (F : Euclidean n → Euclidean N) (row col : Fin n)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : ℝ :=
  (conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
    (fun x ↦ nullvector T Q col (x, w.2)) w.1) / adaptedDenominator T Q row col w

/-- The full column restricts to the already constructed carrier column
(`app:ch_waves:thm:leading`). -/
theorem nullvector_on_carrier (col : Fin n) (w : Euclidean n × Euclidean 3) :
    nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierNullvector T Q col w := rfl

/-- Exact left-column compatibility on the carrier graph
(`app:ch_waves:thm:leading`). -/
theorem conullvector_on_carrier (row : Fin n) (w : Euclidean n × Euclidean 3) :
    conullvector T Q row (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierConullvector T Q row w := rfl

/-- Exact adapted-denominator compatibility (`app:ch_waves:thm:leading`). -/
theorem adaptedDenominator_on_carrier (row col : Fin n) (w : Euclidean n × Euclidean 3) :
    adaptedDenominator T Q row col (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierAdaptedDenominator T Q row col w := rfl

/-- Exact normalized-direction compatibility (`app:ch_waves:thm:leading`). -/
theorem transportDirection_on_carrier (row col : Fin n) (w : Euclidean n × Euclidean 3) :
    transportDirection T Q row col (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierTransportDirection T Q row col w := rfl

/-- The full potential restricts to the original potential, including all
physical derivative terms (`app:ch_waves:thm:leading`). -/
theorem transportPotential_on_carrier (F : Euclidean n → Euclidean N)
    (row col : Fin n) (w : Euclidean n × Euclidean 3) :
    transportPotential T Q F row col (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierTransportPotential T Q F row col w := rfl

/-- Characteristicity gives the right and left null equations on the full
phase domain, before any transport solution is constructed
(`app:ch_waves:thm:leading`). -/
theorem nullvector_relations (row col : Fin n)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : (w.1, w.2.2) ∈ phaseDomain T) :
    reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
        (fun j ↦ nullvector T Q col w j) = 0 ∧
      conullvector T Q row w ᵥ* reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 := by
  have hc : (reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).det = 0 :=
    phase_characteristic T Q hw
  exact ⟨mulVec_rightNullvector hc col, leftNullvector_vecMul hc row⟩

/-- Normalization gives adapted time speed one. The gap producer must supply
the nonzero denominator for the actual full domain
(`app:ch_waves:thm:leading`). -/
theorem transportDirection_normal (row col : Fin n)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    (hd : adaptedDenominator T Q row col w ≠ 0) :
    ⟪T.data.adapted.normal, transportDirection T Q row col w⟫_ℝ = 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    transportDirection, div_mul_eq_mul_div, ← Finset.sum_div]
  convert div_self hd using 2
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The original scalar-reduction theorem applies with the full covector held
fixed. No transport equation is assumed (`app:ch_waves:thm:leading`). -/
theorem scalar_reduction_iff (F : Euclidean n → Euclidean N)
    (row col : Fin n) {α : Euclidean n → ℝ}
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm) (hα : DifferentiableAt ℝ α w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ nullvector T Q col (x, w.2) j) w.1)
    (hd : adaptedDenominator T Q row col w ≠ 0) :
    conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ α x • nullvector T Q col (x, w.2)) w.1 = 0 ↔
      fderiv ℝ α w.1 (transportDirection T Q row col w) +
        transportPotential T Q F row col w * α w.1 = 0 := by
  have hs : (∑ a, transportDirection T Q row col w a * partialDeriv α w.1 a) =
      fderiv ℝ α w.1 (transportDirection T Q row col w) := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
      congrArg (fderiv ℝ α w.1)
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (transportDirection T Q row col w))
  rw [scalar_reduction F Q.1 hQ hα hk, ← hs]
  simp only [transportDirection, transportPotential, PiLp.toLp_apply,
    div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  exact (div_eq_zero_iff.trans (or_iff_left hd)).symm

/-- The prescribed scalar has no dependence on the independent modulation
covector (`app:ch_waves:thm:leading`). -/
def initialScalar (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) : ℝ :=
  r (p.1, p.2.1)

/-- The literal full-parameter characteristic formula. The actual extension
must construct `Φ,Y` for the named coefficients and prove their properties;
this definition by itself asserts no transport solution
(`app:ch_waves:thm:leading`). -/
def scalarAmplitude (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : ℝ :=
  transportFromFootpoint
    (flowTransportCoefficient (fun q ↦ transportPotential T Q F row col
      ((coordinates (adaptedCoordinates T.data.adapted)).symm q)) Φ)
    0 (initialScalar r) Y (coordinates (adaptedCoordinates T.data.adapted) w)

/-- The characteristic formula is linear in the prescribed initial scalar,
while keeping all geometry and maps fixed (`app:ch_waves:thm:leading`). -/
def scalarAmplitudeLinearMap (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) :
    (Euclidean (n - 1) × Euclidean 3 → ℝ) →ₗ[ℝ]
      (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ) where
  toFun := scalarAmplitude T Q F row col Φ Y
  map_add' _r _s := funext fun _w ↦ scalarTransport_add _ _ _ _ _
  map_smul' _a _r := funext fun _w ↦ scalarTransport_smul _ _ _ _ _

/-- The transported density factors through the SAME footpoint and an
initial-data-independent positive exponential (`app:ch_waves:thm:leading`). -/
theorem scalarAmplitude_sq (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    scalarAmplitude T Q F row col Φ Y r w ^ 2 =
      scalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) w ^ 2 *
        initialScalar r (Y (coordinates (adaptedCoordinates T.data.adapted) w)) ^ 2 := by
  simp only [scalarAmplitude, transportFromFootpoint, characteristicTransport,
    scalarTransport, initialScalar, mul_one, mul_pow]

end JanetCartan.LeadingWave.FullModulation
