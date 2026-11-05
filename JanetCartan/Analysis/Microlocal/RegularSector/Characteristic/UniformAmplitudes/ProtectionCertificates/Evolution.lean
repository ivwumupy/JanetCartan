module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ProtectionCertificates.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.LocalCharts

/-!
# Joint protected evolution and supported amplitudes

This names the entire varying-field conclusion, including its same-flow
amplitudes, so local and finite selection can retain it without identifying
independent existential witnesses. Its producer is the conic constructor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open ActualCarriers AmplitudeBounds RootFamily ConicAmplitude ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
open EvolutionIntegral.SymbolBudgets hiding TwoTimePoint
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- The complete strengthened amplitude conclusion for the finite protection
export (`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`).
The original `UniformChartEvolution` is its projection on the SAME witnesses;
root and geometry bounds retain reserves zero and one, respectively. -/
def UniformProtectionEvolution (Ω : Set E) (x : E) (RQ : ℝ)
    (A₀ : Fin (d + 1) → Mat) (ξ : E) (M : ℝ)
    (i r c : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ)
    (H : (Fin (d + 1) → Mat) × Euclidean d → ℝ)
    (ε L a b ρ ρo src μ ν : ℝ) (phaseCost rootCost : ℕ → ℝ)
    (evolutionTime speedGap rootSize : ℝ) (σ : Z → ℝ) (κ : ℝ → ℝ) : Prop :=
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
        RootProtectionBounds Q e h U ℓ speedGap rootSize ∧
        ODE.IsSmoothFlowOn (rootHamiltonField h) z L (L / 2) evolutionTime Φ ∧
        C.source ⊆ twoTimeDomain z (L / 2) evolutionTime ∧
        ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z (L / 2) evolutionTime) ∧
        ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z (L / 2) evolutionTime) ∧
        ContDiffOn ℝ ∞ C C.source ∧
        (∀ q ∈ twoTimeDomain z (L / 2) evolutionTime,
          HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
            (rootHamiltonField h (twoTimeState Φ q)) q.1) ∧
        (∀ q ∈ twoTimeDomain z (L / 2) evolutionTime, ∀ u ∈ uIcc q.2.1 q.1,
          (u, q.2) ∈ twoTimeDomain z (L / 2) evolutionTime ∧
            twoTimeState Φ (u, q.2) ∈ closedBall z L ∧
            (twoTimeState Φ (u, q.2)).1 = u) ∧
        (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
          (u, (C.symm q).2) ∈ twoTimeDomain z (L / 2) evolutionTime ∧
            HasDerivAt (fun t ↦ twoTimeState Φ (t, (C.symm q).2))
              (rootHamiltonField h (twoTimeState Φ (u, (C.symm q).2))) u ∧
            twoTimeState Φ (u, (C.symm q).2) ∈ closedBall z L ∧
            (twoTimeState Φ (u, (C.symm q).2)).1 = u) ∧
        (∀ m, cNorm (closedBall z L) m h ≤
          rootCost m * (1 + cNorm (closedBall x RQ) m Q)) ∧
        (∀ (R₀ : ℕ) (M₀ : ℝ), cNorm (closedBall x RQ) R₀ Q ≤ M₀ →
          ∀ j ≤ R₀, cNorm (closedBall z L) j h ≤ rootCost R₀ * (1 + M₀)) ∧
        (∀ (cost : ℕ → ℝ) (R₀ : ℕ) (scale : ℝ), 1 ≤ scale →
          (∀ m, cNorm (closedBall x RQ) m Q ≤ cost m * scale ^ (m - R₀)) →
          ∀ m, cNorm (closedBall z L) m h ≤
            (rootCost m * (1 + cost m)) * scale ^ (m - R₀)) ∧
        (∀ m, cNorm (closedBall z (L / 4) ×ˢ
            Icc (-evolutionTime / 4) (evolutionTime / 4)) m Φ +
          (cNorm (closedBall (z.1, z) a) m (twoTimeState Φ) +
            cNorm (closedBall (z.1, z) a) m (twoTimeProjection Φ)) +
          (cNorm (closedBall (z.1, z) b) m C.symm +
            cNorm (closedBall (z.1, z) b) m (twoTimePhase C)) ≤
              phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
        (∀ w ∈ ball z a, Φ (w, 0) = w) ∧
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

/-- Forgetting protection retains the original amplitudes on the same witnesses
(`paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`). -/
theorem UniformProtectionEvolution.toUniformChartEvolution
    {Ω : Set E} {x : E} {RQ : ℝ}
    {A₀ : Fin (d + 1) → Mat} {ξ : E} {M : ℝ}
    {i r c : Fin (d + 1)} {ℓ : Euclidean d →L[ℝ] ℝ}
    {H : (Fin (d + 1) → Mat) × Euclidean d → ℝ}
    {ε L a b ρ ρo src μ ν : ℝ} {phaseCost rootCost : ℕ → ℝ}
    {evolutionTime speedGap rootSize : ℝ} {σ : Z → ℝ} {κ : ℝ → ℝ}
    (hevolution : UniformProtectionEvolution Ω x RQ A₀ ξ M i r c ℓ H
      ε L a b ρ ρo src μ ν phaseCost rootCost evolutionTime speedGap rootSize σ κ) :
    FiniteMasks.ActualFamily.UniformChartEvolution Ω x RQ A₀ ξ M i r c ℓ H
      ε L a b ρ ρo src μ ν phaseCost σ κ := by
  intro angular hang hapos ra hra rb
  obtain ⟨D, hD, hfields⟩ := hevolution angular hang hapos ra hra rb
  refine ⟨D, hD, ?_⟩
  intro Q hQ hQrange hQM
  obtain ⟨Φ, C, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdata⟩ :=
    hfields Q hQ hQrange hQM
  exact ⟨Φ, C, hdata⟩

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
