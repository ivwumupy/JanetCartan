module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily

/-!
# The same coefficient root, Hamilton flow and inverse chart

This is the actual coefficient-to-geometry connection for
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
The coordinate split, coefficient branch, domains, radii and all constants
precede the varying original coefficient field. The root has reserve zero;
the flow, inverse and local phase have reserve one. Their only low input is
one C³ bound of the original physical coefficient, in the Frobenius norm.

Consumers: the same-root inputs of `AmplitudeBounds` and the phase inputs
of `EvolutionIntegral.SymbolBudgets`. Conic continuation is assembled in
separate leaves of this module; no amplitude or sector theorem is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformGeometry
open ActualCarriers AmplitudeBounds RootFamily
variable {d : ℕ}

/-- Construct one root branch and its actual two-time Hamilton geometry from
primitive frozen pencil data and a fixed C³ coefficient budget. All choices
precede `Q`, and the same flow and chart serve every order, with reserve one.
The original normalized minor and transport gaps, their radial powers, root
band, full differential and both orientations of each time segment are retained
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_uniform_fieldRoot_twoTimeHamiltonPhase
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
            ∀ n, cNorm (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ +
              (cNorm (closedBall (z.1, z) σ) n (twoTimeState Φ) +
                cNorm (closedBall (z.1, z) σ) n (twoTimeProjection Φ)) +
              (cNorm (closedBall (z.1, z) (2 * β)) n C.symm +
                cNorm (closedBall (z.1, z) (2 * β)) n (twoTimePhase C)) ≤
                  B n * (1 + cNorm (closedBall x R) (n + 1) Q) := by
  obtain ⟨i, ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    ρ, hρ, A, hA, hi, hℓ, hU, hV, hbase, hH, hsub, hband, hD, hcent, hstate, hfields⟩ :=
    exists_coordinateSplit_uniform_fieldRoot hΩ x hR hKΩ A₀ ξ r c hξ hp hreg hm
  let e := coordinateSplit i
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e ξ).2))
  have hz : z.2.2 ≠ 0 := by
    intro hz
    have hh : ℓ z.2.2 = 1 := hℓ
    rw [hz, map_zero] at hh
    norm_num at hh
  have hRD : closedBall z (3 * ρ) ⊆ fieldDomain e Ω ℓ (e ξ).2 ε :=
    fun w hw ↦ (hstate w hw).1
  have hMr : 0 ≤ A 3 * (1 + M) := mul_nonneg (hA 3).le (by positivity)
  obtain ⟨T, hT, σ, hσ, β, hβ, B, hB, hσR, hσT, hβη, hdomain, hflows⟩ :=
    exists_common_twoTimeHamiltonPhase z hz (by positivity : 0 < 3 * ρ) hMr hD hRD
  refine ⟨i, ℓ, U, V, H, ε, hε, κ, hκ, μ, hμ, ν, hν, G, hG, δ, hδ,
    ρ, hρ, A, hA, T, hT, σ, hσ, β, hβ, (fun n ↦ B n * (1 + A (n + 1))),
    (fun n ↦ mul_pos (hB n) (by linarith [hA (n + 1)])),
    hσR, hσT, hβη, hdomain, hi, hℓ, hU, hV, hbase, hH, hsub, hband,
    hD, hcent, hstate, ?_⟩
  intro Q hQ hQrange hQM
  obtain ⟨hh, hhom, hbounds, hlow, hgraded, hgaps, hroot⟩ := hfields Q hQ hQrange
  have h3 := hlow 3 M hQM 3 le_rfl
  have hhom' : ∀ w ∈ fieldDomain e Ω ℓ (e ξ).2 ε, ∀ᶠ a : ℝ in 𝓝 1,
      fieldRoot e Q H (w.1, (w.2.1, a • w.2.2)) = a * fieldRoot e Q H w := by
    intro w hw
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    exact hhom w hw a ha
  obtain ⟨Φ, C, hΦ, hs, hproj, hC, hsource, hsourceD, hCs, hCis, hbuffer,
    hderiv, hsegment, hcoords, hinverseSegment, hdiag, hphase, hdiff,
    hgap, hlip, hmixed, hbudget⟩ := hflows (fieldRoot e Q H) hh h3 hhom'
  refine ⟨hh, hhom, hbounds, hlow, hgraded, hgaps, hroot,
    Φ, C, hΦ, hs, hproj, hC, hsource, hsourceD, hCs, hCis, hbuffer,
    hderiv, hsegment, hcoords, hinverseSegment, hdiag, hphase, hdiff,
    hgap, hlip, hmixed, ?_⟩
  intro n
  apply (hbudget n).trans
  have hq := cNorm_nonneg (closedBall x R) (n + 1) Q
  calc
    B n * (1 + cNorm (closedBall z (3 * ρ)) (n + 1) (fieldRoot e Q H)) ≤
        B n * (1 + A (n + 1) * (1 + cNorm (closedBall x R) (n + 1) Q)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (hbounds (n + 1))) (hB n).le
    _ ≤ (B n * (1 + A (n + 1))) * (1 + cNorm (closedBall x R) (n + 1) Q) := by
      nlinarith [mul_nonneg (hB n).le hq]

end JanetCartan.RegularSector.Characteristic.UniformGeometry
