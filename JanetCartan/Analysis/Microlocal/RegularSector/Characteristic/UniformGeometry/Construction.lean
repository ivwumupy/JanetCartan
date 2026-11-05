module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.ConicBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.ConicIdentities

/-!
# Uniform coefficient-to-conic characteristic geometry

One frozen regular pencil, its selected adjugate entry, the original physical
coefficient domain and one C³ bound construct the SAME coefficient root,
Hamilton flow, inverse projection and conic phase. Every radius, cone, low
constant and high-order constant sequence precedes the varying coefficient.
The coefficient-to-root reserve is zero, and the flow/inverse/phase reserve
is one. All norms retain the original physical coordinates and Frobenius
matrix convention.

The conic phase uses the radial formula and checked deductions of `ConicPhase`.
Its section is the already fixed root section, so no angular choice depends on
`Q`. The temporal shear and inverse bounds use the original coefficient C³
bound through the local second phase jet, rather than compactness after `Q`.

Consumers: `Characteristic.AmplitudeBounds` and
`EvolutionIntegral.SymbolBudgets`, for `app:ch_regular_base:lem:characteristic-kernel`
and `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
Finite covering, signed amplitude construction and operator assembly are separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformGeometry
open ActualCarriers AmplitudeBounds RootFamily ConicPhase FourierIntegral
open EvolutionIntegral NormalComparison WholeImageGeometry
variable {d : ℕ}

/-- Construct uniform local characteristic geometry directly from the original
coefficient field. No root, flow, inverse, phase or conic bound is an input.
All derivative orders and both time orientations use the same branch and
chart. The conic normalized jets have fixed reserve one in the original `Q`,
and the conic mixed/inverse constants depend only on its fixed C³ budget
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_uniform_fieldRoot_conicGeometry
    {Ω : Set (Euclidean (d + 1))} (hΩ : IsOpen Ω)
    (x : Euclidean (d + 1)) {R : ℝ} (hR : 0 < R) (hKΩ : closedBall x R ⊆ Ω)
    (A₀ : Fin (d + 1) → MetricTensor (d + 1)) (ξ : Euclidean (d + 1))
    (r c : Fin (d + 1)) (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0)
    (hm : (pencil A₀ ξ).adjugate r c ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ i : Fin (d + 1),
      let e := coordinateSplit i
      let η₀ := (e ξ).2
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, η₀))
      ∃ (ℓ : Euclidean d →L[ℝ] ℝ)
        (U : Set ((Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d)) (V : Set ℝ)
        (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ),
        ∃ ε > (0 : ℝ), ∃ κ > 0, ∃ μ > 0, ∃ ν > 0, ∃ G > 0, ∃ δ > 0,
        ∃ ρ > 0, ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
        ∃ T > (0 : ℝ), ∃ σ > (0 : ℝ), ∃ β > (0 : ℝ), ∃ B : ℕ → ℝ,
        (∀ m, 0 < B m) ∧ 2 * σ ≤ (3 * ρ) / 4 ∧ 2 * σ ≤ T / 4 ∧
        2 * β < ‖z.2.2‖ ∧
        closedBall (z.1, z) (2 * σ) ⊆ twoTimeDomain z ((3 * ρ) / 2) T ∧
        ∃ γ > (0 : ℝ), γ ≤ β ∧ γ ≤ σ ∧
        z.2.2 ∈ angularCone ℓ z.2.2 (γ / 2) ∧
        IsOpen (angularCone ℓ z.2.2 γ) ∧ Convex ℝ (angularCone ℓ z.2.2 γ) ∧
        (0 : Euclidean d) ∉ angularCone ℓ z.2.2 γ ∧
        closure (angularCone ℓ z.2.2 (γ / 2)) \ {0} ⊆ angularCone ℓ z.2.2 γ ∧
        ∃ κcone > (0 : ℝ), ∃ Bmix > (0 : ℝ), ∃ L > (0 : ℝ),
        ∃ J : ℝ → ℝ → ℕ → ℝ, (∀ a b n, 0 < J a b n) ∧
        ∃ S : ℝ → ℝ → ℝ → ℕ → ℝ, (∀ t a b n, 0 < S t a b n) ∧
        fderiv ℝ (determinant A₀) ξ (e.symm (1, 0)) ≠ 0 ∧
        ℓ η₀ = 1 ∧ IsOpen U ∧ IsOpen V ∧ H (A₀, η₀) = (e ξ).1 ∧
        ContDiffOn ℝ ∞ H (CharacteristicRoot.conicDomain ℓ U) ∧
        closedBall (A₀, η₀) (3 * ε) ⊆ CharacteristicRoot.conicDomain ℓ U ∧
        cthickening δ ((fun p ↦ (p, H p)) '' closedBall (A₀, η₀) (3 * ε)) ⊆
          CharacteristicRoot.conicBand ℓ U V ∧
        IsOpen (fieldDomain e Ω ℓ η₀ ε) ∧
        (∀ y ∈ Ω, ((e y).1, ((e y).2, η₀)) ∈ fieldDomain e Ω ℓ η₀ ε) ∧
        (∀ w ∈ closedBall z (3 * ρ),
          w ∈ fieldDomain e Ω ℓ η₀ ε ∧
          rootPhysicalPosition e w ∈ closedBall x R ∧
          w.2.2 ∈ closedBall η₀ ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2) ∧
        ∀ Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1),
          ContDiffOn ℝ ∞ Q Ω → MapsTo Q Ω (closedBall A₀ ε) →
          cNorm (closedBall x R) 3 Q ≤ M →
          let h := fieldRoot e Q H
          let D := fieldDomain e Ω ℓ η₀ ε
          let K := closedBall z (3 * ρ)
          ContDiffOn ℝ ∞ h D ∧
          (∀ w ∈ D, ∀ a : ℝ, 0 < a → h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
          (∀ m, cNorm K m h ≤ A m * (1 + cNorm (closedBall x R) m Q)) ∧
          (∀ (R₀ : ℕ) (M : ℝ), cNorm (closedBall x R) R₀ Q ≤ M →
            ∀ j ≤ R₀, cNorm K j h ≤ A R₀ * (1 + M)) ∧
          (∀ (a : ℕ → ℝ) (R₀ : ℕ) (T : ℝ), 1 ≤ T →
            (∀ m, cNorm (closedBall x R) m Q ≤ a m * T ^ (m - R₀)) →
            ∀ m, cNorm K m h ≤ (A m * (1 + a m)) * T ^ (m - R₀)) ∧
          (∀ w ∈ K, (rootPencil e Q h w).det = 0 ∧
            (1 / 2 : ℝ) ^ d * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            (1 / 2 : ℝ) ^ (2 * d) * ν ≤
              |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
          (∀ w ∈ D,
            let p := (Q (e.symm (w.1, w.2.1)), w.2.2)
            let pNorm := normalizedFieldParameter e Q ℓ w
            let PNorm := coefficientRootPencil e H pNorm
            w.2.2 ≠ 0 ∧ (rootPencil e Q h w).det = 0 ∧
            (p, h w) ∈ CharacteristicRoot.conicBand ℓ U V ∧
            (∀ τ, (p, τ) ∈ CharacteristicRoot.conicBand ℓ U V →
              (determinant p.1 (e.symm (τ, p.2)) = 0 ↔ h w = τ)) ∧
            κ ≤ |determinantNormalization (e.symm (h w, w.2.2)) *
              fderiv ℝ (determinant p.1) (e.symm (h w, w.2.2)) (e.symm (1, 0))| ∧
            h w = ℓ w.2.2 * H pNorm ∧ |h w| ≤ ℓ w.2.2 * G ∧
            rootPencil e Q h w = ℓ w.2.2 • PNorm ∧
            μ ≤ |PNorm.adjugate r c| ∧
            ν ≤ |minorTransportCoefficient PNorm (rootTimeCoefficient e Q w) r c| ∧
            (ℓ w.2.2) ^ d * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
            (ℓ w.2.2) ^ (2 * d) * ν ≤
              |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) ∧
          ∃ Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d),
          ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
            ODE.IsSmoothFlowOn (rootHamiltonField h) z (3 * ρ) ((3 * ρ) / 2) T Φ ∧
            ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z ((3 * ρ) / 2) T) ∧
            ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z ((3 * ρ) / 2) T) ∧
            (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ ∧
            C.source = ball (z.1, z) σ ∧ C.source ⊆ twoTimeDomain z ((3 * ρ) / 2) T ∧
            ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target ∧
            closedBall (z.1, z) (2 * β) ⊆ C.target ∧
            (∀ q ∈ twoTimeDomain z ((3 * ρ) / 2) T,
              HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
                (rootHamiltonField h (twoTimeState Φ q)) q.1) ∧
            (∀ q ∈ twoTimeDomain z ((3 * ρ) / 2) T, ∀ v ∈ uIcc q.2.1 q.1,
              (v, q.2) ∈ twoTimeDomain z ((3 * ρ) / 2) T ∧
                twoTimeState Φ (v, q.2) ∈ closedBall z (3 * ρ) ∧
                (twoTimeState Φ (v, q.2)).1 = v) ∧
            (∀ q ∈ C.target,
              (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
                (C.symm q).2.2.2 = q.2.2.2 ∧
                (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1) ∧
            (∀ q ∈ C.target, ∀ v ∈ uIcc q.2.1 q.1,
              (v, (C.symm q).2) ∈ twoTimeDomain z ((3 * ρ) / 2) T ∧
                twoTimeState Φ (v, (C.symm q).2) ∈ closedBall z (3 * ρ) ∧
                (twoTimeState Φ (v, (C.symm q).2)).1 = v) ∧
            (∀ w ∈ ball z σ,
              (w.1, w) ∈ C.source ∧ (w.1, w) ∈ C.target ∧
                twoTimeState Φ (w.1, w) = w ∧ twoTimeProjection Φ (w.1, w) = (w.1, w) ∧
                C.symm (w.1, w) = (w.1, w) ∧
                twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
            ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
            (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
            (∀ q ∈ closedBall (z.1, z) σ,
              ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
                (fderiv ℝ (twoTimeProjection Φ) q) -
                  ContinuousLinearMap.id ℝ (TwoTimePoint (Euclidean d))‖ ≤ 1 / 2) ∧
            (∀ q ∈ C.target, ∀ q' ∈ C.target,
              ‖C.symm q - C.symm q'‖ ≤ (2 * (1 + 2 * (A 3 * (1 + M)))) * ‖q - q'‖) ∧
            (∀ q ∈ closedBall (z.1, z) (2 * β), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) ∧
            (∀ n, cNorm (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ +
              (cNorm (closedBall (z.1, z) σ) n (twoTimeState Φ) +
                cNorm (closedBall (z.1, z) σ) n (twoTimeProjection Φ)) +
              (cNorm (closedBall (z.1, z) (2 * β)) n C.symm +
                cNorm (closedBall (z.1, z) (2 * β)) n (twoTimePhase C)) ≤
                  B n * (1 + cNorm (closedBall x R) (n + 1) Q)) ∧
            ContDiffOn ℝ ∞ (phase ℓ C) (domain ℓ C.target) ∧
            (∀ (q : TwoTimePoint (Euclidean d)) (a : ℝ), 0 < a →
              phase ℓ C (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * phase ℓ C q) ∧
            (∀ q ∈ localPatch (bufferedBase z γ) (ball z.2.2 (2 * γ)) ∩
                domain ℓ (localPatch (bufferedBase z γ) (ball z.2.2 (2 * γ))),
              phase ℓ C =ᶠ[𝓝 q] twoTimePhase C) ∧
            (∀ x ∈ elapsedPhysicalBox z γ, ∀ η ∈ angularCone ℓ z.2.2 γ,
              phase ℓ C (x 0, (x 0, (spatialPart x, η))) = ⟪spatialPart x, η⟫_ℝ) ∧
            (∀ q ∈ domain ℓ C.target,
              gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1 =
                ℓ q.2.2.2 • (twoTimeState Φ (C.symm (normalize ℓ q))).2.2 ∧
              gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2 =
                (C.symm (normalize ℓ q)).2.2.1 ∧
              deriv (fun t ↦ phase ℓ C (t, q.2)) q.1 =
                h (q.1, (q.2.2.1,
                  gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) ∧
              -deriv (fun s ↦ phase ℓ C (q.1, (s, q.2.2))) q.2.1 =
                h (q.2.1, (gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η))))
                  q.2.2.2, q.2.2.2))) ∧
            (∀ a > (0 : ℝ), ∀ b : ℝ, ∀ n : ℕ, ∀ Rf > (0 : ℝ),
              cNorm (bufferedJetSet ℓ z γ a b) n
                (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase Rf
                  (curriedPhase ℓ C))) ≤ J a b n * (1 + cNorm (closedBall x R) (n + 1) Q)) ∧
            (∀ t ≥ (0 : ℝ), ∀ a > (0 : ℝ), ∀ b : ℝ, ∀ n : ℕ, ∀ Rf > (0 : ℝ),
              ∀ v ∈ Icc 0 γ, ∀ p ∈ elapsedPhysicalBox z γ ×ˢ
                WholeImageGeometry.normalizedSourceBand (fullAngularCone ℓ z.2.2 γ t) Rf a b,
              ∀ k ≤ n,
                ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase Rf
                  (elapsedPhase (curriedPhase ℓ C) v))) p‖ ≤
                    S t a b n * (1 + cNorm (closedBall x R) (n + 1) Q)) ∧
            (∃ F : TwoTimePoint (Euclidean d) → ℝ,
              Continuous F ∧ ContDiffOn ℝ ∞ F {q | q.2.2.2 ≠ 0} ∧
              (∀ (q : TwoTimePoint (Euclidean d)) (a : ℝ), 0 < a →
                F (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * F q) ∧
              ∀ q ∈ domain ℓ (closedBall (z.1, z) (2 * γ)), F =ᶠ[𝓝 q] phase ℓ C) ∧
            (∀ v ∈ Icc 0 γ, ∀ Y : Set (Euclidean (d + 1)),
              SupportedPhaseRegularity (elapsedPhase (curriedPhase ℓ C) v)
                ((elapsedPhysicalBox z γ ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 γ)) ∧
              SupportedPhaseHomogeneity (elapsedPhase (curriedPhase ℓ C) v)
                ((elapsedPhysicalBox z γ ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 γ)) ∧
              SupportedMixedInvertibility (elapsedPhase (curriedPhase ℓ C) v)
                ((elapsedPhysicalBox z γ ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 γ))) ∧
            ∀ v ∈ Icc 0 γ, ∀ y ∈ elapsedPhysicalBox z γ,
              (∀ η ∈ angularCone ℓ z.2.2 γ,
                ‖mixedPhaseMatrix (curriedPhase ℓ C (y 0) (y 0 - v)) (spatialPart y) η - 1‖ ≤ 1 / 2 ∧
                ‖fun j : Fin d ↦ partialDeriv
                  (elapsedTimeDerivative (curriedPhase ℓ C) v (y 0, spatialPart y)) η j‖ ≤ L) ∧
              (∀ ζ : Euclidean (d + 1), spatialPart ζ ∈ angularCone ℓ z.2.2 γ →
                IsUnit (mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) v) y ζ).det ∧
                κcone ≤ |(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) v) y ζ).det| ∧
                ‖(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) v) y ζ)⁻¹‖ ≤ Bmix) ∧
              ∀ y' ∈ elapsedPhysicalBox z γ,
                InjOn (averagedGradient (elapsedPhase (curriedPhase ℓ C) v) y y')
                  (spatialPart ⁻¹' angularCone ℓ z.2.2 γ) ∧
                ∀ ζ : Euclidean (d + 1), spatialPart ζ ∈ angularCone ℓ z.2.2 γ →
                  κcone ≤ |(averagedJacobian (elapsedPhase (curriedPhase ℓ C) v) y y' ζ).det| := by
  obtain ⟨i, ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    ρ, hρ, A, hA, T, hT, σ, hσ, β, hβ, B, hB, hσR, hσT, hβη, hdomain,
    hi, hℓ, hU, hV, hbase, hH, hsub, hband, hD, hcent, hstate, hfields⟩ :=
    exists_uniform_fieldRoot_twoTimeHamiltonPhase hΩ x hR hKΩ A₀ ξ r c hξ hp hreg hm hM
  let e := coordinateSplit i
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e ξ).2))
  let γ := min β σ
  have hγ : 0 < γ := lt_min hβ hσ
  have hγβ : γ ≤ β := min_le_left _ _
  have hγσ : γ ≤ σ := min_le_right _ _
  have hγsub : closedBall (z.1, z) (2 * γ) ⊆ closedBall (z.1, z) (2 * β) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨κm, hκm, Bmix, hBmix, L, hL, hmixedBounds⟩ :=
    exists_uniform_conic_mixed_bounds ℓ z hγ (B 2 * (1 + M))
  obtain ⟨κa, hκa, haveraged⟩ := exists_conic_elapsed_averaged_geometry d
  let J := fun a b n ↦ jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z γ a b) n * B n
  let S := fun t a b n ↦
    1 + SymbolBudgets.phaseTimeConstant
      (elapsedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b) b) n γ +
      jetBoundConstant ℓ (budgetCoordinates ''
        bufferedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b)) n * B n
  have hJ : ∀ a b n, 0 < J a b n := fun a b n ↦ mul_pos (jetBoundConstant_pos _ _ _) (hB n)
  have hS : ∀ t a b n, 0 < S t a b n := by
    intro t a b n
    have ht := SymbolBudgets.phaseTimeConstant_nonneg
      (elapsedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b) b) n hγ.le
    have hj := jetBoundConstant_pos ℓ (budgetCoordinates ''
      bufferedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b)) n
    have hb := hB n
    dsimp [S]
    positivity
  have hzcone : z.2.2 ∈ angularCone ℓ z.2.2 (γ / 2) := by
    simp only [angularCone, mem_ofPred_eq, show ℓ z.2.2 = 1 from hℓ, inv_one, one_smul]
    exact ⟨zero_lt_one, mem_ball_self (by positivity)⟩
  refine ⟨i, ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    ρ, hρ, A, hA, T, hT, σ, hσ, β, hβ, B, hB, hσR, hσT, hβη, hdomain,
    γ, hγ, hγβ, hγσ, hzcone, isOpen_angularCone ℓ z.2.2 γ,
    convex_angularCone ℓ z.2.2 γ, (fun h ↦ ne_zero_of_mem_angularCone h rfl),
    closure_angularCone_subset (by linarith), min κm κa, lt_min hκm hκa,
    Bmix, hBmix, L, hL, J, hJ, S, hS,
    hi, hℓ, hU, hV, hbase, hH, hsub, hband, hD, hcent, hstate, ?_⟩
  intro Q hQ hQrange hQM
  obtain ⟨hh, hhom, hbounds, hlow, hgraded, hgaps, hroot,
    Φ, C, hΦ, hs, hproj, hC, hsource, hsourceD, hCs, hCis, hbuffer,
    hderiv, hsegment, hcoords, hinverseSegment, hdiag, hphase, hdiff,
    hgap, hlip, hmixed, hbudget⟩ := hfields Q hQ hQrange hQM
  have hbuffer' := hγsub.trans hbuffer
  have hmixed' := fun q hq ↦ hmixed q (hγsub hq)
  have hphaseBound (n : ℕ) : cNorm (closedBall (z.1, z) (2 * γ)) n (twoTimePhase C) ≤
      B n * (1 + cNorm (closedBall x R) (n + 1) Q) := by
    apply (cNorm_mono_set_of_contDiffAt hγsub (isCompact_closedBall _ _)
      (fun q hq ↦ (hphase.contDiffAt (C.open_target.mem_nhds (hbuffer hq))).of_le
        (by simp))).trans
    have hb := hbudget n
    have h₁ := cNorm_nonneg (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ
    have h₂ := cNorm_nonneg (closedBall (z.1, z) σ) n (twoTimeState Φ)
    have h₃ := cNorm_nonneg (closedBall (z.1, z) σ) n (twoTimeProjection Φ)
    have h₄ := cNorm_nonneg (closedBall (z.1, z) (2 * β)) n C.symm
    linarith
  have hphaseLow : cNorm (closedBall (z.1, z) (2 * γ)) 2 (twoTimePhase C) ≤ B 2 * (1 + M) :=
    (hphaseBound 2).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQM) (hB 2).le)
  obtain ⟨htime, hmix⟩ := hmixedBounds (fieldRoot e Q H) Φ C hbuffer' hphase hdiff hmixed' hphaseLow
  have hdiag' : ∀ w ∈ ball z.1 σ ×ˢ ball z.2 σ,
      twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ := by
    intro w hw
    have hw' : w ∈ ball z σ := by
      simpa only [mem_ball, Prod.dist_eq, max_lt_iff, mem_prod] using hw
    exact (hdiag w hw').2.2.2.2.2
  have hRD : closedBall z (3 * ρ) ⊆ fieldDomain e Ω ℓ z.2.2 ε := fun w hw ↦ (hstate w hw).1
  have hscale : ∀ w ∈ fieldDomain e Ω ℓ z.2.2 ε, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ fieldDomain e Ω ℓ z.2.2 ε ∧
        fieldRoot e Q H (w.1, (w.2.1, a • w.2.2)) = a * fieldRoot e Q H w :=
    fun w hw a ha ↦ ⟨fieldDomain_smul e Ω ℓ z.2.2 ε hw ha, hhom w hw a ha⟩
  refine ⟨hh, hhom, hbounds, hlow, hgraded, hgaps, hroot,
    Φ, C, hΦ, hs, hproj, hC, hsource, hsourceD, hCs, hCis, hbuffer,
    hderiv, hsegment, hcoords, hinverseSegment, hdiag, hphase, hdiff,
    hgap, hlip, hmixed, hbudget, contDiffOn_phase ℓ hphase,
    (fun q _ ha ↦ extend_smul ℓ (twoTimePhase C) q ha),
    (fun q hq ↦ phase_eventuallyEq_on_overlap ℓ hdiff isOpen_ball isOpen_ball (convex_ball _ _)
      ((localPatch_bufferedBase_subset z γ).trans hbuffer') hq),
    (fun _ hx _ hη ↦ phase_diagonal_on_buffer ℓ C hγσ hdiag' hx hη), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨gradient_phase_position ℓ (hdiff _ hq.2),
      gradient_phase_covector ℓ (hdiff _ hq.2) hq.1.ne',
      rootFlow_conicPhase_eikonal ℓ (by positivity : 0 < 3 * ρ) hT hRD hΦ hC hsourceD hdiff hscale hq⟩
  · intro a ha b n Rf hRf
    have hb := cNorm_normalizedTwoTimePhase_phase_le ℓ C hphase
      (isCompact_bufferedJetSet ℓ z γ a b) (isCompact_closedBall _ _) hbuffer'
      (bufferedJetSet_normalizes ℓ hγ.le ha).1 (bufferedJetSet_normalizes ℓ hγ.le ha).2 hRf n
    change cNorm _ _ (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase Rf
      (curriedExtend ℓ (twoTimePhase C)))) ≤ _
    exact hb.trans ((mul_le_mul_of_nonneg_left (hphaseBound n)
      (jetBoundConstant_pos _ _ _).le).trans_eq (by dsimp [J]; ring))
  · intro t ht a ha b n Rf hRf v hv p hp k hk
    have hb := norm_iteratedFDeriv_buffered_elapsed_le ℓ hγ.le
      (div_pos ha (by positivity : 0 < 1 + t + ‖z.2.2‖ + γ)) C.open_target hbuffer' hphase hRf hv hk
      (normalizedSourceBand_mem_elapsedJetSet ℓ hγ.le ht ha hRf hp)
    change ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase Rf
      (elapsedPhase (curriedExtend ℓ (twoTimePhase C)) v))) p‖ ≤ _
    apply hb.trans
    have hq := cNorm_nonneg (closedBall x R) (n + 1) Q
    have ht' := SymbolBudgets.phaseTimeConstant_nonneg
      (elapsedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b) b) n hγ.le
    have hj := (jetBoundConstant_pos ℓ (budgetCoordinates ''
      bufferedJetSet ℓ z γ (a / (1 + t + ‖z.2.2‖ + γ)) ((1 + ‖ℓ‖) * b)) n).le
    have hh := mul_le_mul_of_nonneg_left (hphaseBound n) hj
    dsimp [S]
    nlinarith [mul_nonneg ht' hq]
  · exact exists_continuous_conicPhase_extension ℓ C (isCompact_closedBall _ _) hbuffer' hphase
  · intro v hv Y
    have hrh := elapsed_supported_regularity_homogeneity ℓ hγ hbuffer' hphase hv Y
    exact ⟨hrh.1, hrh.2, elapsed_supportedMixedInvertibility ℓ hγ hbuffer' hphase hdiff hmixed' hv Y⟩
  · intro v hv y hy
    refine ⟨fun η hη ↦ ⟨norm_mixedPhaseMatrix_phase_sub_one_le ℓ hγ hbuffer' hphase hdiff hmixed' hv hy hη,
      htime v hv y hy η hη⟩, ?_, ?_⟩
    · intro ζ hζ
      obtain ⟨hu, hd, hi⟩ := hmix v hv y hy ζ hζ
      exact ⟨hu, (min_le_left κm κa).trans hd, hi⟩
    · intro y' hy'
      have ha := haveraged ℓ (fieldRoot e Q H) Φ C z γ hγ hbuffer' hphase hdiff hmixed' v hv y hy y' hy'
      exact ⟨ha.1, fun ζ hζ ↦ (min_le_right κm κa).trans (ha.2 ζ hζ)⟩

end JanetCartan.RegularSector.Characteristic.UniformGeometry
