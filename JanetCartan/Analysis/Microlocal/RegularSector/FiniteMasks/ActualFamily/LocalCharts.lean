module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction

/-!
# Retained witnesses of the actual local characteristic construction

The finite selection must keep the exact root, section and source/time masks
returned by the uniform amplitude producer. `LocalChart` packages its output;
`exists_localChart` constructs every field from a regular frozen zero, including
the nonzero adjugate entry. No successful local chart is an input.

Consumer: the actual finite chart selection for
`app:ch_regular_base:thm:sector` and `prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic Characteristic.UniformAmplitudes ActualCarriers
open Characteristic.AmplitudeBounds Characteristic.RootFamily Characteristic.ConicAmplitude
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.EvolutionIntegral.SymbolBudgets hiding TwoTimePoint
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- The unmodified varying-field conclusion of
`exists_uniform_supported_conic_pencilAmplitudes`. It retains the same phase,
root, amplitudes and all three supported symbol bounds for the later
`UniformEvolution` instantiation (`energy-complete-residual`). -/
def UniformChartEvolution (Ω : Set E) (x : E) (RQ : ℝ)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (M : ℝ)
    (i r c : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ)
    (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ)
    (ε L a b ρ ρo src μ ν : ℝ) (phaseCost : ℕ → ℝ)
    (σ : Z → ℝ) (κ : ℝ → ℝ) : Prop :=
  let e := coordinateSplit i
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  ∀ angular : Euclidean d → ℝ, ContDiff ℝ ∞ angular →
    (∀ η ∈ tsupport angular, 0 < ℓ η) →
    ∀ ra > (0 : ℝ), ∀ rb : ℝ,
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
    ∀ Q : E → Fin (d + 1) → Mat,
      ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
      cNorm (closedBall x RQ) 10 Q ≤ M →
      let h := fieldRoot e Q H
      let U := fieldDomain e Ω ℓ z.2.2 ε
      ∃ Φ : Z × ℝ → Z, ∃ C : OpenPartialHomeomorph T T,
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t * h w) ∧
        closedBall z L ⊆ U ∧
        (∀ w ∈ closedBall z L, (rootPencil e Q h w).det = 0 ∧
          μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
          ν ≤ |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
        (C : T → T) = twoTimeProjection Φ ∧ C.source = ball (z.1, z) a ∧
        ContDiffOn ℝ ∞ C.symm C.target ∧ closedBall (z.1, z) b ⊆ C.target ∧
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
        (∀ q ∈ C.target,
          (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
          (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ U ∧
          (twoTimeState Φ (C.symm q)).1 = q.1) ∧
        (∀ w ∈ ball z a, (w.1, w) ∈ C.target ∧
          C.symm (w.1, w) = (w.1, w) ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
        (∀ q ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
        ball (z.1, z) ρo ⊆ C.target ∧
        MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)) ∧
        ∀ B : E → Mat, ContDiffOn ℝ ∞ B Ω → cNorm (closedBall x RQ) 9 B ≤ M →
          let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
            (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
          let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
          let W₀ := curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0))
          let W₁ := curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
          ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
            (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
            (∀ p ∈ tsupport (collared ℓ 0 angular (Fs 0)) ∪
              tsupport (collared ℓ 1 angular (Fs 1)), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) →
              collared ℓ 1 angular (Fs 2) p ≠ 0 → G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
            (∀ y : E, κ =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
              WKB.firstOrderApply
                (fun x a ↦ ((coefficient i Q x a).map Complex.ofReal).mulVecLin)
                (fun x ↦ ((zeroth i B x).map Complex.ofReal).mulVecLin)
                (fun x ↦ Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
                  (fun k ↦ (W₀ + W₁) (x 0) s (spatialPart x) η k j)) y =
                Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
                  (fun k ↦ twoTimePhysicalApply (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
                    (fun x ↦ (zeroth i B x).map Complex.ofReal) W₁
                      (y 0) s (spatialPart y) η k j)) ∧
            (∀ y : E, κ (y 0) = 1 → ∀ η,
              (coefficient i Q y 0).map Complex.ofReal * W₀ (y 0) (y 0) (spatialPart y) η =
                conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ y η •
                  projector i Q h r c y ((ℓ η)⁻¹ • η)) ∧
          (∀ q : T, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d + 1),
            (fun k ↦ collared ℓ 1 angular (Fs 2) q k j) =
              WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
                (fun y k ↦ collared ℓ 1 angular (Fs 1)
                  (physicalSlice e q.2.1 q.2.2.2 y) k j)
                (e.symm (q.1, q.2.2.1))) ∧
          ∀ j : Fin 3,
            let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
            let F := bufferedMatrix V κ f
            let o := if j = 0 then 0 else 1
            let W := collared ℓ o angular F
            ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ V ∧
            tsupport F ⊆ closedBall (z.1, z) (ρ / 2) ∧ ContDiff ℝ ∞ W ∧
            tsupport W ⊆ ConicPhase.domain ℓ V ∧
            (∀ q : T, q.2.1 ≤ z.1 - src → W q = 0) ∧
            (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → F =ᶠ[𝓝 q] f) ∧
            ∀ m,
              BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                (curryCharacteristicMatrix W) ∧
              twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z (ρ / 2) ra rb) m
                (curryCharacteristicMatrix W) ≤
                D m * (1 + cNorm (closedBall x RQ) (m + 10) Q +
                  cNorm (closedBall x RQ) (m + 9) B)

/-- Fixed local data constructed at one frozen regular zero. The fields
below are produced by `exists_localChart`, before the varying coefficients,
angular collar, derivative order and accuracy (`thm:sector`). -/
structure LocalChart (Ω : Set E) (x : E) (RQ : ℝ)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (M : ℝ) where
  index : Fin (d + 1)
  row : Fin (d + 1)
  col : Fin (d + 1)
  minor_ne_zero : (pencil A₀ ξ).adjugate row col ≠ 0
  radialSection : Euclidean d →L[ℝ] ℝ
  root : (Fin (d + 1) → Mat) × Euclidean d → ℝ
  coefficientRadius : ℝ
  rootRadius : ℝ
  sourceRadius : ℝ
  targetRadius : ℝ
  bufferRadius : ℝ
  outerRadius : ℝ
  maskRadius : ℝ
  minorGap : ℝ
  transportGap : ℝ
  phaseCost : ℕ → ℝ
  sourceMask : Z → ℝ
  timeMask : ℝ → ℝ
  coefficientRadius_pos : 0 < coefficientRadius
  rootRadius_pos : 0 < rootRadius
  sourceRadius_pos : 0 < sourceRadius
  targetRadius_pos : 0 < targetRadius
  bufferRadius_pos : 0 < bufferRadius
  bufferRadius_lt_outerRadius : bufferRadius < outerRadius
  maskRadius_pos : 0 < maskRadius
  maskRadius_lt_sourceRadius : maskRadius < sourceRadius
  minorGap_pos : 0 < minorGap
  transportGap_pos : 0 < transportGap
  phaseCost_pos : ∀ m, 0 < phaseCost m
  section_eq_one : radialSection (coordinateSplit index ξ).2 = 1
  sourceMask_smooth : ContDiff ℝ ∞ sourceMask
  timeMask_smooth : ContDiff ℝ ∞ timeMask
  sourceMask_range : ∀ w, sourceMask w ∈ Icc (0 : ℝ) 1
  timeMask_range : ∀ t, timeMask t ∈ Icc (0 : ℝ) 1
  sourceMask_compact : HasCompactSupport sourceMask
  timeMask_compact : HasCompactSupport timeMask
  sourceMask_support : tsupport sourceMask ⊆
    ball ((coordinateSplit index x).1,
      ((coordinateSplit index x).2, (coordinateSplit index ξ).2)) (maskRadius / 2)
  timeMask_support : tsupport timeMask ⊆ ball (coordinateSplit index x).1 (maskRadius / 2)
  sourceMask_plateau : closedBall ((coordinateSplit index x).1,
      ((coordinateSplit index x).2, (coordinateSplit index ξ).2)) (maskRadius / 4) ⊆
    interior {w | sourceMask w = 1}
  timeMask_plateau : closedBall (coordinateSplit index x).1 (maskRadius / 4) ⊆
    interior {t | timeMask t = 1}
  evolution : UniformChartEvolution Ω x RQ A₀ ξ M index row col radialSection root
    coefficientRadius rootRadius sourceRadius targetRadius bufferRadius outerRadius
    maskRadius minorGap transportGap phaseCost sourceMask timeMask

/-- Regularity of the literal determinant produces a nonzero adjugate entry;
no extra rank or minor hypothesis is imposed on the finite chart construction
(`app:ch_regular_base:prop:normalization`). -/
theorem exists_nonzero_adjugate_entry_of_regular
    (A₀ : Fin (d + 1) → Mat) (ξ : E)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0) :
    ∃ r c, (pencil A₀ ξ).adjugate r c ≠ 0 := by
  by_contra! hz
  have hzero : (pencil A₀ ξ).adjugate = 0 := by
    ext r c
    exact hz r c
  apply hreg
  ext η
  simp [fderiv_determinant_apply, hzero]

/-- Construct the actual local chart, retaining the uniform producer's entire
conclusion and its original masks. The time coordinate is selected by that
producer from determinant regularity. This is the local input to the finite
selection, not an assumed successful-family interface (`thm:sector`). -/
theorem exists_localChart
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E)
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    Nonempty (LocalChart Ω x RQ A₀ ξ M) := by
  obtain ⟨r, c, hm⟩ := exists_nonzero_adjugate_entry_of_regular A₀ ξ hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, μ, hμ, ν, hν, phaseCost, hphaseCost, hℓ,
    σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes hΩ x hRQ hKΩ
      A₀ ξ r c hξ hp hreg hm hM
  exact ⟨⟨i, r, c, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
    phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
    hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
    hevolution⟩⟩

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
