module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Gap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.MultiplierComparison.InitialData

/-!
# Comparison with the unit initial amplitude

The literal density in `app:ch_background:eq:bg-full-complex-amplitude`
scales by the FOURTH power of the initial amplitude at the retained label.
Consequently an initial amplitude at least `1/2` gives `1/16` of the unit
carrier energy. We retain both reflections, the original masks, inverse,
inverse domain, and the Lebesgue integral over the original spectator ball.
The image term is unchanged and nonnegative.

Integrability is derived from `canonicalFrozenCarrierSymbol_initial_regularity`.
Its primitive `hi` is the prescribed smooth initial datum in
`NullTransport.exists_projected_local_positive_amplitude` (in
`Waves/NullTransport/ActualAmplitude/LocalConstruction`). That construction
produces `hY` on its retained flow domain and
`MapsTo (fun q ↦ (q.1, Y q)) Dflow (I ×ˢ D)`; taking the second component
gives `hYrange`. The parent's common radii must place the initial section in
that same flow domain (`hseed`). This containment and the simultaneous finite
incidence construction remain parent obligations. These conditional
deductions do not establish unconditional spectral existence.

`frozenInitial_sqrt_admissible_of_cNorm` supplies both initial-data inputs for
the paper's `sqrt (1 + v)` perturbations directly from their sufficiently small
finite-order norm. In particular the factor above remains the literal fourth
power, even for these square-root initial data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

private def multiplierQuadraticTest {n : ℕ} (s : Euclidean n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M ↦ dotProduct (fun i ↦ s i) (M *ᵥ (fun i ↦ s i))
      map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c A; simp [Matrix.smul_mulVec, dotProduct_smul] }).toContinuousLinearMap

section Carrier
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "aᵢ" => uncutFrozenCoefficients T Q F row col Φ Y initial
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a / 2)

/-- The exact fourth-power multiplier survives the actual inverse substitution
and zero extension, including points outside the inverse domain. Consumer:
`canonicalFrozenCarrierSymbol_initial_quadratic_ge_unit`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenExtendedDensity_initial_factor (p : Variables n × Euclidean 2) :
    extendedDensity aᵢ J₀ u₀ Ω₀ p =
      initial (Y (0, (0, parameter ((u₀ p).1, p.2)))) ^ 4 •
        extendedDensity a₀ J₀ u₀ Ω₀ p := by
  by_cases hp : p ∈ Ω₀
  · simp only [extendedDensity, indicator_of_mem hp]
    exact frozenInputDensity_initial_factor T Q F row col Φ Y initial hηb hr ha J₀ _
  · simp only [extendedDensity, indicator_of_notMem hp, smul_zero]

private theorem frozenExtendedDensity_initial_test_ge_unit
    (hlower : ∀ z ∈ carrierSupport z₀ (r := a),
      (1 / 2 : ℝ) ≤ initial (Y (0, (0, parameter z))))
    (p : Variables n × Euclidean 2) (s : Euclidean n) :
    (1 / 16 : ℝ) * multiplierQuadraticTest s (extendedDensity a₀ J₀ u₀ Ω₀ p) ≤
      multiplierQuadraticTest s (extendedDensity aᵢ J₀ u₀ Ω₀ p) := by
  rw [frozenExtendedDensity_initial_factor T Q F row col Φ Y initial hηb hr ha,
    map_smul, smul_eq_mul]
  by_cases hp : p ∈ Ω₀
  · by_cases hm : angular₀ ((u₀ p).1, p.2) (‖(u₀ p).2‖⁻¹ • (u₀ p).2) = 0
    · simp [extendedDensity, hp, inputDensity, inputWeight, uncutFrozenCoefficients,
        inverseCoordinates, hm]
    have hz := angularMask_nonzero z₀ (NormedSpace.normalize ηb) ha
      (angularWidth_spec hηb hr).1 hm
    have hl := hlower ((u₀ p).1, p.2)
      ⟨ball_subset_closedBall hz.1, ball_subset_closedBall hz.2.1⟩
    have hpow : (1 / 16 : ℝ) ≤ initial (Y (0, (0, parameter ((u₀ p).1, p.2)))) ^ 4 := by
      convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hl 4 using 1; norm_num
    apply mul_le_mul_of_nonneg_right hpow
    simp only [extendedDensity, indicator_of_mem hp]
    change 0 ≤ dotProduct (fun i ↦ s i)
      (inputDensity a₀ J₀ (inverseCoordinates u₀ p) *ᵥ (fun i ↦ s i))
    simpa only [star_trivial] using
      (frozenInputDensity_posSemidef T Q F row col Φ Y (fun _ ↦ 1) angular₀
        FixedCutoffs.highFrequency (adaptedSliceCoordinates T) (inverseCoordinates u₀ p)).dotProduct_mulVec_nonneg
          (fun i ↦ s i)
  · simp only [extendedDensity, indicator_of_notMem hp, map_zero, mul_zero, le_refl]

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ) (hV : IsOpen V) (hLV : L ⊆ V)

include hP har hcarrier hf hInv htrans hcJ hV hLV

/-- The EXACT canonical reflected carrier form dominates `1/16` of its unit
initial-amplitude version. Both densities are genuinely integrable by the
primitive regularity theorems; positivity of a totalized integral is not used
to infer integrability. The lower bound is needed only at retained initial
labels on the actual mask support. Consumer: the finite-matrix comparison in
`app:ch_background:prop:bg-frame`. -/
theorem canonicalFrozenCarrierSymbol_initial_quadratic_ge_unit
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D)
    (hlower : ∀ z ∈ carrierSupport z₀ (r := a),
      (1 / 2 : ℝ) ≤ initial (Y (0, (0, parameter z))))
    (k s : Euclidean n) :
    (1 / 16 : ℝ) * dotProduct (fun i ↦ s i)
      (canonicalFrozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1) z₀ hηb hr ha k *ᵥ
        (fun i ↦ s i)) ≤
      dotProduct (fun i ↦ s i)
        (canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha k *ᵥ
          (fun i ↦ s i)) := by
  have hiInt := (canonicalFrozenCarrierSymbol_initial_regularity T Q F row col Φ Y initial
    hP hηb hr ha har hcarrier hf hInv htrans hcJ hV hLV hi hY hseed hYrange).1
  have huInt := frozenExtendedDensity_unit_integrable T Q F row col Φ Y hP hηb hr ha har
    hcarrier hf hInv htrans hcJ hV hLV
  have hamp (p : Variables n) :
      (1 / 16 : ℝ) * multiplierQuadraticTest s (amplitude a₀ J₀ u₀ Ω₀ S₀ p) ≤
        multiplierQuadraticTest s (amplitude aᵢ J₀ u₀ Ω₀ S₀ p) := by
    simp only [amplitude, ← (multiplierQuadraticTest s).integral_comp_comm (huInt p),
      ← (multiplierQuadraticTest s).integral_comp_comm (hiInt p), ← integral_const_mul]
    exact integral_mono (((multiplierQuadraticTest s).integrable_comp (huInt p)).const_mul _)
      ((multiplierQuadraticTest s).integrable_comp (hiInt p))
      (fun v ↦ frozenExtendedDensity_initial_test_ge_unit T Q F row col Φ Y initial hηb hr ha
        hlower (p, v) s)
  change (1 / 16 : ℝ) * multiplierQuadraticTest s
      ((2 * (2 * Real.pi) ^ n) •
        (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, k) + amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, -k))) ≤
    multiplierQuadraticTest s ((2 * (2 * Real.pi) ^ n) •
      (amplitude aᵢ J₀ u₀ Ω₀ S₀ (0, 0, k) + amplitude aᵢ J₀ u₀ Ω₀ S₀ (0, 0, -k)))
  simp only [map_smul, map_add, smul_eq_mul]
  calc
    _ = (2 * (2 * Real.pi) ^ n) *
        ((1 / 16 : ℝ) * multiplierQuadraticTest s (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, k)) +
         (1 / 16 : ℝ) * multiplierQuadraticTest s (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, -k))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hamp (0, 0, k)) (hamp (0, 0, -k)))
      (by positivity)

end Carrier

section Family
variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
    (G : ι → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))

variable (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) (T j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T j).family.threshold)
    (F : Euclidean n → Euclidean N) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r a : ι → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)
    {b cJ : ι → ℝ} {V L : ι → Set (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : ∀ j, (P j).IsValid c C)
    (har : ∀ j, 6 * a j ≤ 3 * r j)
    (hcarrier : ∀ j, closedBall (spectatorCenter (z₀ j)) (3 * r j) ×ˢ
      closedBall (z₀ j 0) (3 * r j) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * (P j).radius / 2))
    (hf : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩))
      (physicalParameterSet (z₀ j) (6 * a j) ×ˢ dataSet (z₀ j) (ηb j) (3 * r j)))
    (hInv : ∀ j, BufferedPhaseInverse (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩)
      (physicalParameterSet (z₀ j) (6 * a j)) (dataBox (z₀ j) (ηb j) (r j))
      (dataSet (z₀ j) (ηb j) (2 * r j)) (dataBox (z₀ j) (ηb j) (2 * r j))
      (V j) (L j) (b j) (cJ j) (G j))
    (htrans : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
      ∀ u ∈ supportedCone (z₀ j) (NormedSpace.normalize (ηb j)) (r j) (angularWidth (ηb j) (r j)),
        ‖(adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p u).2 - u.2‖ ≤
          (angularWidth (ηb j) (r j) / 4) * ‖u.2‖)
    (hcJ : ∀ j, 0 < cJ j) (hV : ∀ j, IsOpen (V j)) (hLV : ∀ j, L j ⊆ V j)

local notation "e₀" => canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y
  (fun _ _ ↦ 1) z₀ ηb r a hηb hr ha


variable (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
    {D : ι → Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : ι → Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}

local notation "eᵢ" => canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y
  initial z₀ ηb r a hηb hr ha

include hP har hcarrier hf hInv htrans hcJ hV hLV

/-- The literal finite matrix with permitted initial amplitudes dominates
`1/16` of the unit matrix. The image contribution is unchanged: its
nonnegativity supplies the remaining `15/16` of that term. The carrier
integrals retain their actual geometric and analytic inputs. Consumer:
`exists_canonicalFrozenMatrixSymbol_initial_gap_of_incidence`
(`app:ch_background:prop:bg-frame`). -/
theorem canonicalFrozenMatrixSymbol_initial_quadratic_ge_unit
    (hi : ∀ j, ContDiffOn ℝ ∞ (initial j) (D j))
    (hY : ∀ j, ContDiffOn ℝ ∞ (Y j) (Dflow j))
    (hseed : ∀ j, MapsTo
      (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ j 0) (r j) ×ˢ ball (spectatorCenter (z₀ j)) (6 * a j)) (Dflow j))
    (hYrange : ∀ j, MapsTo (Y j) (Dflow j) (D j))
    (hlower : ∀ j, ∀ z ∈ carrierSupport (z₀ j) (r := a j),
      (1 / 2 : ℝ) ≤ initial j (Y j (0, (0, parameter z))))
    (k s : Euclidean n) :
    (1 / 16 : ℝ) * dotProduct (fun i ↦ s i) (e₀ k *ᵥ (fun i ↦ s i)) ≤
      dotProduct (fun i ↦ s i) (eᵢ k *ᵥ (fun i ↦ s i)) := by
  have hI : 0 ≤ dotProduct (fun i ↦ s i) (frozenImageSymbol (Q 0) k *ᵥ (fun i ↦ s i)) := by
    simpa only [star_trivial] using (frozenImageSymbol_posSemidef (Q 0) k).dotProduct_mulVec_nonneg
      (fun i ↦ s i)
  simp only [canonicalFrozenMatrixSymbol_eq, add_mulVec, dotProduct_add,
    sum_mulVec, dotProduct_sum, mul_add, Finset.mul_sum]
  apply add_le_add (by linarith : (1 / 16 : ℝ) *
    dotProduct (fun i ↦ s i) (frozenImageSymbol (Q 0) k *ᵥ (fun i ↦ s i)) ≤ _)
  apply Finset.sum_le_sum
  intro j _
  exact canonicalFrozenCarrierSymbol_initial_quadratic_ge_unit (T j) ⟨Q, hQ, hlow j⟩ F
    (row j) (col j) (Φ j) (Y j) (initial j) (hηb j) (hr j) (ha j) (hP j) (har j)
    (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j) (hV j) (hLV j)
    (hi j) (hY j) (hseed j) (hYrange j) (hlower j) k s

variable (hgap : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
    ∀ u ∈ dataBox (z₀ j) (ηb j) (2 * r j),
      ‖((G j).symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)

include hgap

local notation "u₀" => fun j ↦ frozenSymbolInverse (T j) (Subtype.mk Q (And.intro hQ (hlow j))) (z₀ j) (ηb j) (r j) (6 * a j)
local notation "Ω₀" => fun j ↦ frozenSymbolDomain (T j) (Subtype.mk Q (And.intro hQ (hlow j))) (z₀ j) (ηb j) (r j) (6 * a j)
local notation "J₀" => fun j ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T j))
  (normalizedTransportPosition (T j) (Subtype.mk Q (And.intro hQ (hlow j))) 0)
local notation "a₀" => fun j ↦ uncutFrozenCoefficients (T j) (Subtype.mk Q (And.intro hQ (hlow j))) F (row j) (col j)
  (Φ j) (Y j) (fun _ ↦ 1)
  (angularMask (z₀ j) (NormedSpace.normalize (ηb j)) (ha j) (And.left (angularWidth_spec (hηb j) (hr j))))
  FixedCutoffs.highFrequency

/-- A single positive high-frequency constant works for EVERY permitted
initial multiplier, once the same unit-family incidence geometry is supplied.
The constant is the constructed unit constant divided by `16`; no positive
symbol, nonvanishing normal or coercivity premise is assumed. The root and
detection inputs have the producers documented in `Spectral/Gap`, and their
simultaneous instantiation remains with the spectral parent
(`app:ch_background:prop:bg-frame`). -/
theorem exists_canonicalFrozenMatrixSymbol_initial_gap_of_incidence
    (active : Euclidean n → Finset ι) (z : Euclidean n → ι → Euclidean 3)
    (hroot : ∀ k : Euclidean n, ‖k‖ = frozenFamilyHighFrequencyRadius T G → ∀ j ∈ active k,
      ((0, 0, k), spectatorCenter (z₀ j)) ∈ Ω₀ j ∧
      parameter (((u₀ j) ((0, 0, k), spectatorCenter (z₀ j))).1, spectatorCenter (z₀ j)) = z k j ∧
      0 < inputWeight (a₀ j) (J₀ j)
        (inverseCoordinates (u₀ j) ((0, 0, k), spectatorCenter (z₀ j))))
    (hdetect : ∀ k : Euclidean n, ‖k‖ = frozenFamilyHighFrequencyRadius T G → ∀ s : Euclidean n,
      ActualCarriers.imageChannel (pencil (Q 0) k) s = 0 →
      (∀ j ∈ active k, ⟪quadratic (Q 0) ((T j).carrierGradient ⟨Q, hQ, hlow j⟩ 0 (z k j)), s⟫_ℝ = 0) →
      s = 0) :
    ∃ δ > (0 : ℝ), ∀ initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ j, ContDiffOn ℝ ∞ (initial j) (D j)) →
      (∀ j, ContDiffOn ℝ ∞ (Y j) (Dflow j)) →
      (∀ j, MapsTo
        (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
        (ball (z₀ j 0) (r j) ×ˢ ball (spectatorCenter (z₀ j)) (6 * a j)) (Dflow j)) →
      (∀ j, MapsTo (Y j) (Dflow j) (D j)) →
      (∀ j, ∀ z ∈ carrierSupport (z₀ j) (r := a j),
        (1 / 2 : ℝ) ≤ initial j (Y j (0, (0, parameter z)))) →
      ∀ k : Euclidean n, frozenFamilyHighFrequencyRadius T G ≤ ‖k‖ →
      ∀ s : Euclidean n, δ * ‖s‖ ^ 2 ≤ dotProduct (fun i ↦ s i)
        (canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y initial
          z₀ ηb r a hηb hr ha k *ᵥ (fun i ↦ s i)) := by
  obtain ⟨δ, hδ, hunit⟩ := exists_canonicalFrozenMatrixSymbol_unit_gap_of_incidence
    T G Q hQ hlow F row col Φ Y z₀ ηb r a hηb hr ha hP har hcarrier hf hInv htrans
    hcJ hV hLV hgap active z hroot hdetect
  refine ⟨δ / 16, by positivity, ?_⟩
  intro initial hi hY hseed hYrange hlower k hk s
  have hcompare := canonicalFrozenMatrixSymbol_initial_quadratic_ge_unit
    T G Q hQ hlow F row col Φ Y z₀ ηb r a hηb hr ha hP har hcarrier hf hInv htrans
    hcJ hV hLV initial hi hY hseed hYrange hlower k s
  have hscaled := mul_le_mul_of_nonneg_left (hunit k hk s) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  calc
    _ = (1 / 16 : ℝ) * (δ * ‖s‖ ^ 2) := by ring
    _ ≤ _ := hscaled.trans hcompare

end Family

end JanetCartan.ContinuumNormal.FrozenModel
