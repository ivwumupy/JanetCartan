module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedNormalReduction.SupportedSymbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.BoundedSourceMultiplier.LiteralSplit

/-!
# The principal symbol of the supported weighted normal

The principal symbol is the diagonal of the SAME zero-extended cycle amplitude
used in `WeightedNormalReduction`. Its graph realization converts cycles back
to physical covectors once. The source cutoff belongs to `diagonalSymbol`,
and is not included in this source-independent symbol.

These definitions alone do not assert that the chosen bounded graph realizes
the principal integral or that its physical commutator gains a derivative.
Those are construction obligations for `app:ch_regular_base:eq:actual-right-inverse`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization

open AmplitudeBound NormalComparison LowBounds UncutNormal WholeImageGeometry
open WeightedNormalReduction FullLowBounds BoundedSourceMultiplier

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "L²" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The source-independent diagonal in cycle frequency, for the principal
factor in `app:ch_regular_base:eq:actual-pdo-remainder`. -/
def principalCycleSymbol (a : FullAmplitude n r) (x ξ : E) : Mat := a x x ξ

/-- The same principal amplitude in physical covectors, for the graph family
used by `app:ch_regular_base:eq:actual-right-inverse`. -/
def principalPhysicalAmplitude (a : FullAmplitude n r) (x η : E) : Mat :=
  principalCycleSymbol a x ((2 * Real.pi)⁻¹ • η)

/-- The common bounded graph family for the principal PDO. Its literal
realization must be proved from finite symbol profiles; the family definition
by itself does not prove this. Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
def principalL2Operator (a : FullAmplitude n r) : L² →L[ℂ] L² :=
  fullGraphOperator (fun x η ↦ inner ℝ x η) (fun x _ η ↦ principalPhysicalAmplitude a x η)

/-- The exact physical commutator, before the retained input Fourier cutoff.
Its order is a separate analytic assertion. Source:
`app:ch_regular_base:eq:actual-right-inverse`, Step 4. -/
def principalPhysicalCommutator (a : FullAmplitude n r) (m : SchwartzMap E ℂ) :
    L² →L[ℂ] L² :=
  principalL2Operator a ∘L physicalMultiplier (m.toLp (⊤ : ENNReal)) -
    physicalMultiplier (m.toLp (⊤ : ENNReal)) ∘L principalL2Operator a

/-- The literal shifted-integral remainder for this commutator, including
all frequencies and cutoff shoulders. Source:
`app:ch_regular_base:eq:fixed-source-multiplication` with phase `x·η`. -/
def principalCommutatorAmplitude (a : FullAmplitude n r) (m : SchwartzMap E ℂ)
    (x η : E) : Mat :=
  sourceRemainder (fun x η ↦ inner ℝ x η) (principalPhysicalAmplitude a) m x η

/-- Physical-to-cycle conversion cancels exactly; no second normalization
factor is introduced in the principal term of `actual-pdo-remainder`. -/
@[simp] theorem principalPhysicalAmplitude_cycle (a : FullAmplitude n r) (x ξ : E) :
    principalPhysicalAmplitude a x ((2 * Real.pi) • ξ) = principalCycleSymbol a x ξ := by
  unfold principalPhysicalAmplitude
  rw [inv_smul_smul₀ (show 2 * Real.pi ≠ 0 by positivity)]

/-- The two-position diagonal retains its source cutoff, independently of
the principal symbol's output position. Source: `actual-pdo-remainder`. -/
theorem diagonalSymbol_eq_sourceCut_principalCycleSymbol
    (a : FullAmplitude n r) (β : E → ℝ) (x y ξ : E) :
    diagonalSymbol a β ξ (pairedPosition x y) = β y • principalCycleSymbol a x ξ :=
  diagonalSymbol_pairedPosition a β x y ξ

/-- The supported scalar diagonal, including the inverse-chart indicator.
It is used only after deriving its equality with the actual matrix diagonal.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
def supportedPrincipalScalar (X D : Set E) (S c : E → E → ℝ) (x ξ : E) : ℂ :=
  {v : E | x ∈ X ∧ (2 * Real.pi) • v ∈ averagedGradient S x x '' D}.indicator
    (fun v ↦ (c x (wholeImageInverse S D x x ((2 * Real.pi) • v)) : ℂ)^2) ξ

/-- The SAME zero-extended weighted diagonal equals the supported scalar
matrix. All phase and matrix gaps remain restricted to their original charts.
Consumer: principal plateau cancellation in `actual-right-inverse`. -/
theorem weighted_principalCycleSymbol_eq_supported
    {X D : Set E} {S : E → E → ℝ} (c : E → E → ℝ) (U : E → E → Mat)
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hs : tsupport (Function.uncurry c) ⊆ X ×ˢ D)
    {δ δU : ℝ} (hδ : 0 < δ) (hδU : 0 < δU)
    (hgap : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|)
    (hdet : ∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) (x ξ : E) :
    principalCycleSymbol
      (cycleCrossNormalAmplitude D S (maskedTransportAmplitude c U)
        (maskedWeightedAmplitude S c U) (wholeImageInverse S D) (averagedJacobian S)) x ξ =
      supportedPrincipalScalar X D S c x ξ • (1 : Mat) := by
  have h := weighted_diagonalSymbol_eq_supported_mask_square c U (fun _ ↦ 1)
    hX hD hcX hS hs hδ hδU hgap hdet x x ξ
  simp only [diagonalSymbol_pairedPosition, one_smul] at h
  rw [principalCycleSymbol, h]
  exact Set.indicator_smul_const_apply _ _ _ _

end JanetCartan.FourierIntegral.WeightedPrincipalLocalization
