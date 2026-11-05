module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CommonMeasurement.Energy

/-!
# The realized frozen carrier at a common measurement radius

The inputs are the SAME local geometry and `UnitRealization` produced jointly
by `exists_realized_frozen_incidence_patch`. For every positive `ρ` with
`6 * ρ < d.a`, restrict that operator by `FixedCutoffs.periodic` at `ρ`.
The full normal is the physical sandwich of the original bounded PDO; its
literal full-amplitude action and the exact Fourier energy are proved below.
No analytic-normal premise is added and no new derivative estimates are needed.

Consumers: `jc-frozen-model-spectral` and `jc-frozen-continuum-model`, for
`new:lem:scaling` and `app:ch_background:prop:bg-frame`. Finite-family
instantiation and the final gap assembly remain with those consumers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization CommonMeasurement
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    (d : FrozenIncidencePatchData T z₀ ηb)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (hcell : 4 * d.a < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) d.ha
  (And.left (angularWidth_spec d.hηb d.hr))
local notation "e₀" => normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
  d.ha hcell angular₀ FixedCutoffs.highFrequency 0
local notation "a₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical d.ha 1)
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb d.r (6 * d.a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb d.r (6 * d.a)
local notation "S₀" => closedBall (spectatorCenter z₀) (d.a / 2)
local notation "b₀" => canonicalFrozenCarrierSymbol T Q F d.row d.col Φ Y (fun _ ↦ 1)
  z₀ d.hηb d.hr d.ha
local notation "H" => EuclideanL2 n (EuclideanSpace ℂ (Fin n))

/-- Restrict the actual unit-initial frozen carrier to ANY common positive
measurement radius. The old and new operators share their literal test action,
uniqueness and adjoint on the original Lebesgue carrier space. The new global
normal is a constructed physical sandwich, with its exact full-amplitude action;
its Fourier energy uses the SAME `canonicalFrozenCarrierSymbol`.

All input certificates are the joint outputs of
`exists_realized_frozen_incidence_patch`; in particular the normal and energy
identities are extracted from `hreal`, not assumed anew. Both quadratures,
the reflected factor four, `k = 2πξ`, the original inverse/domain at `d.r` and
`6*d.a`, and the spectator ball at `d.a/2` are retained
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem FrozenIncidencePatchData.exists_common_measurement_realization
    {c C : ℝ} (hP : P.IsValid c C) (hgeom : d.Geometry Q)
    (hreal : d.UnitRealization Q F hcell) {ρ : ℝ} (hρ : 0 < ρ) (hρa : 6 * ρ < d.a) :
    ∃ (hρcell : 4 * ρ < 1 / 2) (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n) (A : H →L[ℂ] H),
    (∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (e₀).outputChart → V f x = 0) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val) → W = V) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e₀ w) 2 (carrierMeasure n) ∧
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₀ w) ∧
    (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
      realOutputCompression (transferOperator A) ∧
    let e := normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
      hρ hρcell angular₀ FixedCutoffs.highFrequency 0
    let a := coefficientsOfCarrier e (FixedCutoffs.physical hρ 1)
    let Vρ := restrictCarrier (FixedCutoffs.periodic hρ hρcell 1) V
    let M := freezingVectorPhysicalMultiplier (FixedCutoffs.physical hρ 1)
      (FixedCutoffs.physical hρ 1).continuous (FixedCutoffs.physical hρ 1).hasCompactSupport
    let Aρ := M ∘L A ∘L M
    ‖Vρ‖ ≤ ‖V‖ ∧
    (∀ v : carrierInitialTestSpace n,
      Vρ (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
    (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vρ f x = 0) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = Vρ) ∧
    (∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
      Vρ.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
    (realQuadratureChannel Vρ).comp (realQuadratureChannel Vρ).adjoint =
      realOutputCompression (transferOperator Aρ) ∧
    (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume),
      ContDiff ℝ ∞ f → HasCompactSupport f →
      Aρ (hf.toLp f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator
          (fun x y ξ ↦ fullReflectedMatrixAmplitude a J₀ u₀ Ω₀ S₀ ξ (pairedPosition x y))
          (fun y j ↦ f y j) x)) ∧
    (∀ ξ x y i j, fullReflectedMatrixAmplitude a J₀ u₀ Ω₀ S₀ ξ (pairedPosition x y) i j =
      (FixedCutoffs.physical hρ 1 x : ℂ) * (FixedCutoffs.physical hρ 1 y : ℂ) *
        (b₀ ((2 * Real.pi) • ξ) i j : ℂ)) ∧
    (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) →
      ∀ w : OutputL2 n, ‖(realQuadratureChannel W).adjoint w‖ ^ 2 =
        euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
          (FixedCutoffs.physical hρ 1 x • toEuclidean (𝕜 := ℝ) w x))) := by
  have hρcell : 4 * ρ < 1 / 2 := by linarith
  let e := normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
    hρ hρcell angular₀ FixedCutoffs.highFrequency 0
  let χ := FixedCutoffs.periodic (n := n) hρ hρcell 1
  obtain ⟨hn, hsupport, B, _, hb, hA, V, htest, hsupp, hunique, hadj, hnormal, henergy⟩ :=
    hreal Φ Y (2 * (n + 1)) le_rfl
  let A := vectorTwoPositionL2Operator hn (4 * d.a) (fullReflectedMatrixAmplitude a₀ J₀ u₀ Ω₀ S₀)
    hb (fullReflectedMatrixAmplitude_supportedInCenteredBox a₀ J₀ u₀ Ω₀ S₀ (4 * d.a) hsupport)
    B hA
  have hs : ∀ x, χ x ≠ 0 → x ∈ torusChart (closedBall 0 (4 * ρ)) :=
    fun _ hx ↦ fixed_measurement_mem_chart hρ hρcell hx
  have hK : torusChart (closedBall 0 (4 * ρ)) ⊆ (e₀).outputChart := by
    exact fun _ hx ↦ closedBall_subset_closedBall (by linarith : 4 * ρ ≤ 4 * d.a) hx
  have hp : ∀ x, χ x ≠ 0 → (e₀).measurementCutoff x = 1 := by
    intro x hx
    exact (mul_eq_left₀ hx).mp
      (physical_measurement_mul hρ d.ha (by linarith) (centeredTorusRepresentative x))
  have ht : ∀ v : carrierInitialTestSpace n,
      restrictCarrier χ V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val :=
    restrictCarrier_test_common_chart e₀ χ (closedBall 0 (4 * ρ)) hs hK
      (fun _ _ ↦ rfl) hp V htest
  have hu : ∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ v : carrierInitialTestSpace n,
        W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) →
      W = restrictCarrier χ V := fun W hW ↦ carrierExtensions_eq_of_initialTests e _ W ht hW
  have hnres := restricted_fullReflected_realization hn (4 * d.a) a₀ J₀ u₀ Ω₀ S₀ hb
    (fullReflectedMatrixAmplitude_supportedInCenteredBox a₀ J₀ u₀ Ω₀ S₀ (4 * d.a) hsupport)
    B hA χ (FixedCutoffs.physical hρ 1) (FixedCutoffs.physical hρ 1).contDiff
    (FixedCutoffs.physical hρ 1).hasCompactSupport (fun _ ↦ rfl) V hnormal
  rw [d.commonMeasurement_coefficients Q F Φ Y hcell hρ hρcell hρa] at hnres
  refine ⟨hρcell, V, A, htest, hsupp, hunique, hadj, hnormal, ?_, ht,
    carrierRealization_eq_zero_outside e _ ht, hu, ?_, hnres.1, hnres.2,
    d.commonMeasurement_amplitude_symbol Q F Φ Y hρ hρcell hP hgeom, ?_⟩
  · exact (restrictCarrier_norm_le χ V).trans
      ((mul_le_mul_of_nonneg_right (FixedCutoffs.periodic_norm_le_one hρ hρcell 1)
        (norm_nonneg V)).trans_eq (one_mul _))
  · exact restrictCarrier_adjoint_common_chart e₀ χ (closedBall 0 (4 * ρ)) hs hK
      (fun _ _ ↦ rfl) hp V hadj
  · intro W hW w
    rw [hu W hW]
    exact d.commonMeasurement_adjoint_energy Q F Φ Y hρ hρcell hρa V (henergy V htest) w

end JanetCartan.ContinuumNormal.FrozenModel
