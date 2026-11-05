module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Output
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart

/-!
# Literal Fourier energy on the retained masks

Apply the Fourier identity to the unit realization from the joint retained
constructor. Symbol continuity and boundedness are derived from its retained
outer inverse, not assumed. The common measurement changes only the physical
cutoff; the inner angular mask and outer inverse remain unchanged.
Consumer: the single finite retained family's frozen gap
(`app:ch_background:prop:bg-frame`, `new:lem:scaling`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization CommonMeasurement
open ContinuumNormalReduction TransportSymbol TransportKernel
open FrozenModel UnitRealization PeriodicLocalL2 AmplitudeBound

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
    (hcell' : 4 * a' < 1 / 2) (hrr : r' ≤ r) (haa : a' ≤ a)
    (hgeom : RetainedSpectralGeometry T Q z₀ ηb r a)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "e₀" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1)
  ha' hcell' angular₀ FixedCutoffs.highFrequency 0
local notation "b₀" => retainedFrozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1)
  z₀ r a hηb hr' ha'

include hP hr ha hrr haa hgeom

/-- The literal unit carrier constructed on the retained masks has the
Euclidean energy of its actual symbol. Its global normal, separation,
measurability and symbol bound are all discharged from the joint constructor's
outputs (`app:ch_background:prop:bg-frame`). No energy or coercivity premise is
introduced. Initial-test uniqueness gives the result for the SAME supplied `V`.
-/
theorem unitCarrierOutput_adjoint_energy {s : ℕ} (hs : 2 * (n + 1) ≤ s)
    (hunit : UnitCarrierOutput T Q F row col Φ Y z₀ ηb r a r' a' hr' ha' hcell' hηb s hs)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV : ∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    (w : OutputL2 n) :
    ‖(realQuadratureChannel V).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical ha' 1 x • toEuclidean (𝕜 := ℝ) w x)) := by
  obtain ⟨har, hcarrier, G, b, cJ, Vgeom, L, hcJ, hVgeom, hLV, hf, hInv, htrans, _⟩ := hgeom
  have hcont := retainedFrozenCarrierSymbol_unit_continuous T Q F row col Φ Y
    hP hηb hr ha hr' ha' hrr haa har hcarrier hf hInv htrans hcJ hVgeom hLV
  obtain ⟨Csymbol, _, hsymbol⟩ := retainedFrozenCarrierSymbol_unit_bounded T Q F row col Φ Y
    hP hηb hr hr' ha' haa har hcarrier hf hInv htrans hcJ
  obtain ⟨hn, hsupport, B, _, hb, hA, W, htest, _, _, _, hnormal, hsep⟩ := hunit
  exact carrierExtension_adjoint_norm_sq_eq_frozenCarrierEnergy T Q F row col Φ Y
    (fun _ ↦ 1) ha' hcell' angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
    (frozenSymbolInverse T Q z₀ ηb r (6 * a))
    (frozenSymbolDomain T Q z₀ ηb r (6 * a)) (closedBall (spectatorCenter z₀) (a' / 2))
    hn (4 * a') hsupport hb B (fun i j ξ is his ↦ hA i j ξ is (his.trans hs))
    (fun i j ↦ ((continuous_apply j).comp ((continuous_apply i).comp hcont)).measurable)
    Csymbol hsymbol hsep W hnormal htest V hV w

/-- Restriction to the common physical measurement preserves the literal
retained symbol, both quadratures and `2*pi*xi`. The plateau multiplication
also retains the half-open-cell indicator in the Euclidean extension
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-frame`). -/
theorem unitCarrierOutput_commonMeasurement_energy {s : ℕ} (hs : 2 * (n + 1) ≤ s)
    (hunit : UnitCarrierOutput T Q F row col Φ Y z₀ ηb r a r' a' hr' ha' hcell' hηb s hs)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV : ∀ v : carrierInitialTestSpace n,
      V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e₀ v.val)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2) (hμa : 6 * μ < a')
    (w : OutputL2 n) :
    ‖(realQuadratureChannel (restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) V)).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x)) := by
  change ‖(carrierChannel (restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) V)).adjoint w‖ ^ 2 = _
  rw [carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint]
  change ‖(realQuadratureChannel V).adjoint
    (cutoffMultiplier (FixedCutoffs.periodic hμ hμcell 1) w)‖ ^ 2 = _
  rw [unitCarrierOutput_adjoint_energy T Q F row col Φ Y hP hηb hr ha hr' ha' hcell'
    hrr haa hgeom hs hunit V hV]
  apply euclideanFrozenEnergy_congr_ae
  let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
  have hm := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae (cutoffMultiplier_coeFn χ w))
  filter_upwards [toEuclidean_coe (𝕜 := ℝ) (cutoffMultiplier χ w),
    toEuclidean_coe (𝕜 := ℝ) w, hm] with x ht hw hm
  congr 1
  rw [ht, hw]
  by_cases hx : x ∈ halfOpenCell n
  · simp only [indicator_of_mem hx, periodicLift, Function.comp_apply]
    rw [hm hx]
    change FixedCutoffs.physical ha' 1 x •
      (FixedCutoffs.physical hμ 1 (centeredTorusRepresentative (torusQuotient x)) •
        w (torusQuotient x)) = _
    rw [centeredTorusRepresentative_quotient hx, smul_smul, mul_comm,
      physical_measurement_mul hμ ha' (by linarith)]
  · simp [hx]

end JanetCartan.ContinuumNormal.RetainedFrozen
