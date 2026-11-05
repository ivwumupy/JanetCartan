module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Frequency
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.MaskContainment

/-!
# The canonical frozen symbols with their original masks

Instantiate the shared literal symbols with the zero-position restriction of
the SAME canonical conic inverse, its actual domain, the actual angular and
high masks, and the original compact Lebesgue spectator support. This fixes
the concrete expressions consumed by the remaining integrability and spectral
proofs in `app:ch_background:prop:bg-frame`; the definitions assert neither
successful finite-family construction nor a spectral gap.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

section Carrier
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y initial angular₀
  FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)

/-- The actual single-carrier frozen symbol with the canonical masks and
spectator support from `CanonicalConic.kernelSymbolInputs`
(`app:ch_background:eq:bg-real-symbol`). -/
def canonicalFrozenCarrierSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  frozenCarrierSymbol T Q F row col Φ Y initial angular₀ FixedCutoffs.highFrequency
    (adaptedSliceCoordinates T) u₀ Ω₀ (closedBall (spectatorCenter z₀) (a / 2)) k

/-- Nonnegativity of the instantiated canonical carrier expression
(`app:ch_background:prop:bg-frame`). This alone does not prove integrability. -/
theorem canonicalFrozenCarrierSymbol_posSemidef (k : Euclidean n) :
    (canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha k).PosSemidef :=
  frozenCarrierSymbol_posSemidef T Q F row col Φ Y initial angular₀ FixedCutoffs.highFrequency
    (adaptedSliceCoordinates T) u₀ Ω₀ (closedBall (spectatorCenter z₀) (a / 2)) k

omit T Q F row col Φ Y initial in
/-- The actual mask belongs to the retained frozen input cone wherever its
input covector is nonzero (`app:ch_background:defn:bg-row`). -/
theorem canonicalAngularMask_mem_frozenInputDomain (har : a ≤ r)
    {p : InputVariables n} (hη : p.2.2 ≠ 0)
    (hm : angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0) :
    p ∈ frozenInputDomain z₀ ηb r (6 * a) :=
  angularMask_mem_symbolInputDomain hηb hr ha har
    (by simpa using (show 0 ≤ 4 * a by positivity))
    (by simpa using (show 0 ≤ 4 * a by positivity)) hη hm

/-- Off the proved frozen cone the actual original input density is zero.
The zero-covector case follows from its literal `|η|` factor
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem canonicalFrozenInputDensity_zero_outside (har : a ≤ r) (p : InputVariables n)
    (hp : p ∉ frozenInputDomain z₀ ηb r (6 * a)) : inputDensity a₀ J₀ p = 0 := by
  by_cases hη : p.2.2 = 0
  · simp [inputDensity, inputWeight, hη]
  by_cases hm : angular₀ p.2.1 (‖p.2.2‖⁻¹ • p.2.2) = 0
  · simp [inputDensity, inputWeight, uncutFrozenCoefficients, hm]
  exact (hp (canonicalAngularMask_mem_frozenInputDomain z₀ hηb hr ha har hη hm)).elim

/-- The actual spectator mask gives the original compact support, without
changing the Lebesgue initial measure (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem canonicalFrozenExtendedDensity_zero_outside_spectator
    (p : Variables n × Euclidean 2) (hv : p.2 ∉ closedBall (spectatorCenter z₀) (a / 2)) :
    extendedDensity a₀ J₀ u₀ Ω₀ p = 0 := by
  by_cases hp : p ∈ Ω₀
  · rw [extendedDensity, indicator_of_mem hp]
    have hm : angular₀ ((u₀ p).1, p.2) (‖(u₀ p).2‖⁻¹ • (u₀ p).2) = 0 := by
      by_contra hm
      have hv' := (angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha
        (And.left (angularWidth_spec hηb hr)) hm).2.1
      exact hv (ball_subset_closedBall hv')
    simp only [inputDensity, inputWeight, uncutFrozenCoefficients, inverseCoordinates,
      hm, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_div, zero_smul]
  · exact indicator_of_notMem hp _

/-- Exact Fourier-consumer identity for the fully specified canonical
frozen carrier: actual masks, spectator set, measurement, inverse and
Jacobian, with reflection and `2π` unchanged
(`app:ch_background:eq:bg-real-symbol`, frozen step). -/
theorem canonicalFrozen_fullReflectedMatrixAmplitude
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcell : 4 * a < 1 / 2) (x y ξ : Euclidean n) :
    CarrierNormalRealization.fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial ha hcell angular₀
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha 1))
      J₀ u₀ Ω₀ (closedBall (spectatorCenter z₀) (a / 2)) ξ
      (AmplitudeBound.pairedPosition x y) =
      (FixedCutoffs.physical ha 1 x * FixedCutoffs.physical ha 1 y) •
        (fun i j ↦ (canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha
          ((2 * Real.pi) • ξ) i j : ℂ)) :=
  fullReflectedMatrixAmplitude_normalizedCarrierData_zero T Q F row col Φ Y initial angular₀
    FixedCutoffs.highFrequency (adaptedSliceCoordinates T) hP hηb hr har hcarrier hInv htrans
      ha hcell (closedBall (spectatorCenter z₀) (a / 2)) x y ξ

end Carrier

section Family
variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) (T j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T j).family.threshold)
    (F : Euclidean n → Euclidean N) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r a : ι → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)

/-- The original finite Hamilton family, with each literal frozen chart,
mask, and spectator set inserted into the shared matrix expression
(`app:ch_background:prop:bg-frame`, frozen step). -/
def canonicalFrozenMatrixSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  frozenMatrixSymbol T Q hQ hlow F row col Φ Y initial
    (fun j ↦ angularMask (z₀ j) (NormedSpace.normalize (ηb j)) (ha j)
      (angularWidth_spec (hηb j) (hr j)).1)
    FixedCutoffs.highFrequency (fun j ↦ adaptedSliceCoordinates (T j))
    (fun j ↦ frozenSymbolInverse (T j) ⟨Q, hQ, hlow j⟩ (z₀ j) (ηb j) (r j) (6 * a j))
    (fun j ↦ frozenSymbolDomain (T j) ⟨Q, hQ, hlow j⟩ (z₀ j) (ηb j) (r j) (6 * a j))
    (fun j ↦ closedBall (spectatorCenter (z₀ j)) (a j / 2)) k

/-- Exact finite assembly of the canonical frozen image and carrier symbols
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem canonicalFrozenMatrixSymbol_eq (k : Euclidean n) :
    canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y initial z₀ ηb r a hηb hr ha k =
      frozenImageSymbol (Q 0) k + ∑ j, canonicalFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
        (row j) (col j) (Φ j) (Y j) (initial j) (z₀ j) (hηb j) (hr j) (ha j) k := rfl

/-- Nonnegativity of the concrete finite expression at every Euclidean
frequency (`app:ch_background:prop:bg-frame`); a uniform gap remains to be proved. -/
theorem canonicalFrozenMatrixSymbol_posSemidef (k : Euclidean n) :
    (canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y initial z₀ ηb r a hηb hr ha k).PosSemidef := by
  rw [canonicalFrozenMatrixSymbol_eq]
  exact (frozenImageSymbol_posSemidef (Q 0) k).add
    (Matrix.posSemidef_sum _ (fun j _ ↦ canonicalFrozenCarrierSymbol_posSemidef (T j)
      ⟨Q, hQ, hlow j⟩ F (row j) (col j) (Φ j) (Y j) (initial j) (z₀ j) (hηb j) (hr j) (ha j) k))

end Family
end JanetCartan.ContinuumNormal.FrozenModel
