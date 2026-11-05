module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedCellAdjoint.ForwardBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.ReflectedComparison

/-!
# Normal comparison for the literal retained-cell operators

The retained forward/adjoint output identifies its operator uniquely by the
original test integral. This identifies any already retained operator with
that output before applying the full reflected-amplitude difference estimate.
Both the local angular masks and the final common measurement are unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier CanonicalConic
open FullPhaseCharts.ActualComparison
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open ContinuumAdjoint.Canonical.RetainedCellAdjoint Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Apply a full reflected-amplitude bound to the SAME literal retained-cell
operators. Their identity follows from equality on the dense original test
space, rather than an identification of independent existential choices.
The exact constructor of `houtput` is
`RetainedRowGeometry.exists_uniform_retained_cell_carrierAdjoint_with_comparison`;
`FamilyInputs.exists_retained_conic_fullAmplitude_comparison` supplies `hfull`.
The measurement restriction uses the existing reflected comparison, so its
factor four is counted once. Consumer: the fixed-reference carrier contribution
in `ContinuumNormal.ActualConstruction.norm_physicalNormal_sub_le_image_and_full_amplitudes`.
Sources: `app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-frame` and `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem retainedCell_realNormal_sub_norm_le_fullAmplitude
    {n N : ℕ} {P : Patch n} {V : Set (Euclidean n)} {hV : IsOpen V}
    (T : PatchQuantitativeFamily P V hV)
    (Q : Bool → {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q V ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Bool → Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : Bool → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {K : Set (Euclidean n)} {Kinitial : Set (Euclidean (n - 1) × Euclidean 3)}
    (zRoot : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a r' a' : ℝ) (ha' : 0 < a') (hr' : 0 < r')
    (hcell : 4 * a' < 1 / 2) (hηb : ηb ≠ 0)
    (C Cpdo Cmask H : Bool → ℝ) (Cbound : Bool → ℕ → ℝ)
    (m : ℕ) (hreserve : 2 * (n + 1) ≤ m)
    (U : Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (χ : C(Torus n, ℝ)) (hχ : ‖χ‖ ≤ 1) (tol : ℝ) :
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let e := fun t ↦ data T (Q t) (F t) row col (φ t) (y t) initial ha' hcell angular
      FixedCutoffs.highFrequency
    let d := fun t ↦ coefficientsOfCarrier (e t) (FixedCutoffs.physical ha' 1)
    let J := fun t ↦ symbolJacobian T (Q t)
    let u := fun t ↦ symbolInverse T (Q t) zRoot ηb r (6 * a)
    let Ω := fun t ↦ symbolDomain T (Q t) zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    (∀ t, RetainedCellForwardAdjointOutput (K := K) (Kinitial := Kinitial)
      T (Q t) (F t) row col (φ t) (y t) initial zRoot ηb r a r' a' ha' hr' hηb
      (C t) (Cpdo t) (Cmask t) (H t) m hreserve (e t) (d t) (Cbound t)) →
    (∀ t v, U t (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (e t) v.val) →
    (∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude (d true) (J true) (u true) (Ω true) S ξ z i j -
        fullReflectedMatrixAmplitude (d false) (J false) (u false) (Ω false) S ξ z i j)
      m (4 * tol)) →
    ‖carrierChannel (CommonMeasurement.restrictCarrier χ (U true)) ∘L
        (carrierChannel (CommonMeasurement.restrictCarrier χ (U true))).adjoint -
      carrierChannel (CommonMeasurement.restrictCarrier χ (U false)) ∘L
        (carrierChannel (CommonMeasurement.restrictCarrier χ (U false))).adjoint‖ ≤
      (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (4 * tol)) := by
  intro angular e d J u Ω S houtput hU hfull
  have hn : 0 < n := by have := row.isLt; omega
  choose hsupport Lmask hLmask Mmask hMmask hmask hfinite htest hb hA W
    hW hWadj hWtest hWsupp hWunique hWliteral hWlimit hWnormal hWcommon hWraw using houtput
  have hident (t : Bool) : U t = W t := hWunique t (U t) (hU t)
  let b := fun t ↦ fullReflectedMatrixAmplitude (d t) (J t) (u t) (Ω t) S
  have hs t := fullReflectedMatrixAmplitude_supportedInCenteredBox
    (d t) (J t) (u t) (Ω t) S (4 * a') (hsupport t)
  have hB (t) (i j : Fin n) : HasAmplitudeDerivativeBound
      (fun ξ z ↦ b t ξ z i j) (2 * (n + 1)) (Cpdo t * H t) :=
    fun ξ is his ↦ hA t i j ξ is (his.trans hreserve)
  apply ActualConstruction.norm_restricted_carrierNormal_sub_le_full_amplitudes
    hn (4 * a') b hb hs (fun t ↦ Cpdo t * H t) hB U
    (fun t ↦ ?_) χ hχ m hreserve (4 * tol)
    (fun i j ↦ by simpa only [b, Pi.sub_apply, Matrix.sub_apply] using hfull i j)
  simpa only [hident t, carrierChannel, b, J, u, Ω, S] using hWnormal t

end JanetCartan.ContinuumNormal.CarrierVariation
