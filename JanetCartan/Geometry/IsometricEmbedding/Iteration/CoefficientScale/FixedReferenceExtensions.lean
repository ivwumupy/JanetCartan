module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FixedReferenceExtensions.HamiltonProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Quotient
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Transport

/-!
# Joint extensions at the initialized reference scale

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, construct the
quotient boxes, cutoffs, transport refinements and covering domains before a
positive source cap and every history order. Every positive source scale below
that cap works for every initialized reference with the same literal map.
The geometric and reduced-array profiles, global Hamilton, eight quotient and
six transport extension profiles retain the original reserves and domains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.NormalRankStability
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers CurrentFullPhase FrozenMenu ProjectedStressFrame HamiltonPhase NullTransport
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates ProtectedFlow GeometricProfile JointExtensions

/-- All-small-source-scale form of the actual joint extension construction
(`main:prop:current-scale`, `app:eq:uniform-high-coeff`). Its consumer is the
`InitializedProfiles` final assembly, which intersects this cap with the
full-modulation cap before selecting its single reference.

The quotient cutoffs, buffers, inverse gaps and transport extension operators
are fixed before the cap and history orders. Forward agreement uses the original
buffered boxes; inverse agreement retains all of `LF` and `LT`. Transport
agreement balls cover a common physical neighborhood times every ORIGINAL
carrier cube. The Hamilton, quotient and transport reserves remain three, six
and five. The prescribed extra frame margin and geometric/reduced-array
profiles are retained. Constants and initial-frequency thresholds may depend
on the selected source scale, but precede initial frequency, stage, history
and accuracy. Only the original analytic chart must contain the carrier ball;
map equality transfers the result without enlarging the initialized working chart.
No actual coefficient profile or successful construction is assumed. -/
theorem exists_source_scale_cap_for_fixed_reference_joint_extensions {n : ℕ} (hn : 5 ≤ n) {I : Type*} [Fintype I]
    (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    (P : I → Patch n) {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r)
    (z : I → Euclidean 3) (k : I → Euclidean n)
    (hz : ∀ i, z i ∈ parameterInterior (P i).radius) (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i) ((P i).toFun w)) (z i)
      (EuclideanSpace.single 0 1) ≠ 0)
    {εextra : ℝ} (hεextra : 0 < εextra) :
    ∃ ρF ρT qrad s e cF bF cT bT : I → ℝ,
    ∃ VF LF : I → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : I → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (family i).family.radius / 8 ∧ 0 < e i ∧
        4 * qrad i ≤ ρF i ∧ 4 * qrad i ≤ ρT i ∧ 2 * e i ≤ ρF i ∧ 2 * e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ ψF χF : I → FullQuotientInput n → ℝ,
    ∃ ψT χT : I → TransverseQuotientInput n → ℝ,
      (∀ i,
        let η := (family i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
        ContDiff ℝ ∞ (ψF i) ∧ HasCompactSupport (ψF i) ∧
        tsupport (ψF i) ⊆ ball (fullForwardCenter (z i) η) (ρF i) ∧
        ContDiff ℝ ∞ (ψT i) ∧ HasCompactSupport (ψT i) ∧
        tsupport (ψT i) ⊆ ball (transverseForwardCenter (z i) η) (ρT i) ∧
        ContDiff ℝ ∞ (χF i) ∧ HasCompactSupport (χF i) ∧
        tsupport (χF i) ⊆ interior (fullParameterBox (z i) (s i / 2) (e i)) ×ˢ VF i ∧
        ContDiff ℝ ∞ (χT i) ∧ HasCompactSupport (χT i) ∧
        tsupport (χT i) ⊆ interior (transversePrimitiveBox (z i) (s i / 2) (e i)) ×ˢ VT i) ∧
    ∃ ε : ℝ, ∃ g : I → ℝ, 0 < ε ∧ (∀ i, 0 < g i) ∧
    ∃ centers : (i : I) → Finset (parameterCube (P i).radius),
    ∃ row col : (i : I) → centers i → Fin n,
    ∃ ρ L : (i : I) → centers i → ℝ,
    ∃ hρ : ∀ i q, 0 < ρ i q,
    ∃ Ω : (i : I) → centers i → Set (Euclidean n × Euclidean 3),
      (∀ i q, 0 < L i q ∧ IsOpen (Ω i q) ∧
        closedBall ((0 : Euclidean n), q.1.1) (ρ i q) ⊆ Ω i q ∧
        Ω i q ⊆ (ball (0 : Euclidean n) (family i).physicalRadius ∩
          interior (closedBall 0 r)) ×ˢ parameterInterior (3 * (P i).radius / 2)) ∧
      (∀ i, closedBall (0 : Euclidean n) ε ×ˢ parameterCube (P i).radius ⊆
        ⋃ q, closedBall ((0 : Euclidean n), q.1.1)
          (transportExtensionRadius ((0 : Euclidean n), q.1.1) (hρ i q))) ∧
    ∃ Dq Dt : I → ℕ → ℝ, (∀ i m, 0 < Dq i m) ∧ (∀ i m, 0 < Dt i m) ∧
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ cap →
    ∀ G : FlatReference n, G.map = sourceDilation G₀.map σ →
    ∀ rStar r₀ kMin : ℕ, 12 ≤ rStar → 6 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Bquotient Btransport Egeom Eext Bextended : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧ (∀ m, 0 ≤ Bquotient m) ∧ (∀ m, 0 ≤ Btransport m) ∧
      (∀ m, 0 ≤ Egeom m) ∧ (∀ m, 0 ≤ Eext m) ∧ (∀ m, 0 ≤ Bextended m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
        cNorm (closedBall 0 r) 12 F ≤ cNorm (closedBall 0 r) 12 G.map + 1 ∧
        cNorm (closedBall 0 r) 6 (projectedStress F - fun _ ↦ cubeStress n) < εextra ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 r) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        (∀ m, extendedGeometricCoefficientNorm p m F ≤
          Egeom m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients p (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 r) ∧
        tsupport (extendedReducedCoefficients p (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (r + p.width / 2) ∧
        HasDerivativeProfile univ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) r₀
          (currentCoefficientScale R₀ j) Eext ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (family i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
        ∀ i,
          let T := family i
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
          let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
          BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (fullParameterSet (z i) (s i) (2 * e i))
            (dataBox (z i) ηb (qrad i)) (dataSet (z i) ηb (2 * qrad i))
            (dataBox (z i) ηb (2 * qrad i)) (VF i) (LF i) (bF i) (cF i)
            (FrozenIncidence.referenceEquiv T (hP i) (hz i) (hinc i) (hd i)) ∧
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet (z i) (s i) (2 * e i))
            (closedBall ηb (qrad i)) (ball ηb (2 * qrad i)) (closedBall ηb (2 * qrad i))
            (VT i) (LT i) (bT i) (cT i) (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ContDiff ℝ ∞ (extendedHamiltonPhase T Q) ∧
          EqOn (extendedHamiltonPhase T Q) (phase (T.currentChart Q).coordinates)
            (closedBall (hamiltonExtensionCenter T) (hamiltonExtensionRadius T)) ∧
          tsupport (extendedHamiltonPhase T Q) ⊆ hamiltonExtensionSupport T ∧
          HasDerivativeProfile univ (extendedHamiltonPhase T Q) r₀
            (currentCoefficientScale R₀ j) Bextended ∧
          (∀ f ∈ ({fullForwardCoefficient T Q,
              fullForwardEpsilonCoefficient T Q} : Set (FullQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ ψF i x • f x) ∧
            EqOn (fun x ↦ ψF i x • f x) f
              (fullParameterBox (z i) (s i / 2) (e i) ×ˢ dataBox (z i) ηb (2 * qrad i)) ∧
            tsupport (fun x ↦ ψF i x • f x) ⊆ tsupport (ψF i)) ∧
          (∀ f ∈ ({transverseForwardCoefficient T Q,
              transverseForwardEpsilonCoefficient T Q} : Set (TransverseQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ ψT i x • f x) ∧
            EqOn (fun x ↦ ψT i x • f x) f
              (transversePrimitiveBox (z i) (s i / 2) (e i) ×ˢ closedBall ηb (2 * qrad i)) ∧
            tsupport (fun x ↦ ψT i x • f x) ⊆ tsupport (ψT i)) ∧
          (∀ f ∈ ({fullInverseCoefficient T Q (z i) ηb (qrad i),
              fullInverseEpsilonCoefficient T Q (z i) ηb (qrad i)} : Set (FullQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ χF i x • f x) ∧
            EqOn (fun x ↦ χF i x • f x) f
              (fullParameterBox (z i) (s i / 4) (e i / 2) ×ˢ LF i) ∧
            tsupport (fun x ↦ χF i x • f x) ⊆ tsupport (χF i)) ∧
          (∀ f ∈ ({transverseInverseCoefficient T Q ηb (qrad i),
              transverseInverseEpsilonCoefficient T Q ηb (qrad i)} : Set (TransverseQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ χT i x • f x) ∧
            EqOn (fun x ↦ χT i x • f x) f
              (transversePrimitiveBox (z i) (s i / 4) (e i / 2) ×ˢ LT i) ∧
            tsupport (fun x ↦ χT i x • f x) ⊆ tsupport (χT i)) ∧
          (∀ m, extendedQuotientCoefficientNorm T Q (z i) ηb (qrad i)
              (ψF i) (ψT i) (χF i) (χT i) m ≤
            Dq i m * currentQuotientCoefficientNorm T Q (z i) ηb
              (ρF i) (ρT i) (qrad i) (s i) (e i) (VF i) (VT i) m) ∧
          (∀ m, extendedQuotientCoefficientNorm T Q (z i) ηb (qrad i)
              (ψF i) (ψT i) (χF i) (χT i) m ≤
            Bquotient m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
          ∀ q : centers i,
            ContDiffOn ℝ ∞ (carrierNullvector T Q (col i q)) (Ω i q) ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q (row i q)) (Ω i q) ∧
            ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q (row i q) (col i q)) (Ω i q) ∧
            ContDiffOn ℝ ∞ (fun w ↦ (carrierAdaptedDenominator T Q (row i q) (col i q) w)⁻¹)
              (Ω i q) ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q (row i q) (col i q)) (Ω i q) ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F (row i q) (col i q)) (Ω i q) ∧
            (∀ w ∈ Ω i q,
              carrierNullvector T Q (col i q) w ≠ 0 ∧ carrierConullvector T Q (row i q) w ≠ 0 ∧
              g i ≤ |carrierAdaptedDenominator T Q (row i q) (col i q) w| ∧
              |(carrierAdaptedDenominator T Q (row i q) (col i q) w)⁻¹| ≤ (g i)⁻¹) ∧
            cNorm (closedBall ((0 : Euclidean n), q.1.1) (ρ i q)) 1
              (carrierTransportDirection T Q (row i q) (col i q)) ≤ L i q ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (carrierNullvector T Q (col i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (carrierConullvector T Q (row i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (carrierAdaptedDenominator T Q (row i q) (col i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (fun w ↦ (carrierAdaptedDenominator T Q (row i q) (col i q) w)⁻¹) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (carrierTransportDirection T Q (row i q) (col i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρ i q)
              (carrierTransportPotential T Q F (row i q) (col i q)) ∧
            ∀ m,
              extendedTransportCoefficientNorm T Q F (row i q) (col i q)
                  ((0 : Euclidean n), q.1.1) (hρ i q) m ≤
                Dt i m * currentTransportCoefficientNorm T Q F (row i q) (col i q)
                  (closedBall ((0 : Euclidean n), q.1.1) (ρ i q)) m ∧
              extendedTransportCoefficientNorm T Q F (row i q) (col i q)
                  ((0 : Euclidean n), q.1.1) (hρ i q) m ≤
                Btransport m * currentCoefficientScale R₀ j ^ (m - r₀) := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  choose ρF hρF ρT hρT qrad hqrad s hs e he δq hδq cF hcF bF hbF VF LF
    cT hcT bT hbT VT LT hsq hphysical hrF hrT heF heT hrF' hrT' heF' heT'
    hVF hVFc hLFc hLFV hVT hVTc hLTc hLTV
    ψF χF ψT χT hψF hcψF hsψF hψT hcψT hsψT hχF hcχF hsχF hχT hcχT hsχT
    Dq Hq hDq hHq hquot using
    fun i ↦ exists_actual_quotient_extensions (family i) (hP i) (hz i) (hk i) (hinc i) (hd i)
  choose δt ε g hδt hε hg centers row col ρ Ldir hρ Ω hΩ hcover Dt hDt htransport using
    fun i ↦ exists_transport_extensions_before_geometry (N := embeddingDimension n)
      (by omega : 2 ≤ n) (hP i) (family i) hK hKU (hball i)
  obtain ⟨εcommon, d, _, hεcommon, _, hdcommon, _, hcommon⟩ := exists_common_phase_buffers
    ε (fun i ↦ min (δq i) (δt i)) (fun _ ↦ (1 : ℝ))
    hε (fun i ↦ lt_min (hδq i) (hδt i))
  obtain ⟨cap, hcap, hcap₁, hprofiles⟩ :=
    exists_source_scale_cap_for_fixed_reference_hamilton_profiles G₀ hr hrR hR p
      hpcenter hpradius P family hball (lt_min hdcommon hεextra)
  refine ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, ?_,
    ψF, χF, ψT, χT, ?_, εcommon, g, hεcommon, hg,
    centers, row, col, ρ, Ldir, hρ, Ω, ?_, ?_, Dq, Dt, hDq, hDt,
    cap, hcap, hcap₁, ?_⟩
  · intro i
    exact ⟨hρF i, hρT i, hqrad i, hs i, hsq i, hphysical i, he i,
      hrF' i, hrT' i, heF' i, heT' i, hcF i, hbF i, hcT i, hbT i,
      hVF i, hVFc i, hLFc i, hLFV i, hVT i, hVTc i, hLTc i, hLTV i⟩
  · intro i
    exact ⟨hψF i, hcψF i, hsψF i, hψT i, hcψT i, hsψT i,
      hχF i, hcχF i, hsχF i, hχT i, hcχT i, hsχT i⟩
  · intro i q
    exact ⟨(hΩ i q).1, (hΩ i q).2.1, (hΩ i q).2.2.1, (hΩ i q).2.2.2.1⟩
  · intro i
    apply Subset.trans (prod_mono (closedBall_subset_closedBall ?_) Subset.rfl) (hcover i)
    linarith [(hcommon i).1]
  intro σ hσ hσcap G hmap rStar r₀ kMin hStar hreserve horder
  obtain ⟨S, hS, C₀, hC₀, κ, hκ, A, E, Bphase, Egeom, Eext, Bextended,
    hA, hE, hBp, hEg, hEe, hBe, hhist⟩ :=
    hprofiles σ hσ hσcap G hmap rStar r₀ kMin hStar (by omega) horder
  choose Hp hHp hphase using fun i ↦ (family i).exists_projected_phase_sharp_bound
    (N := embeddingDimension n) hK hKU (hball i) C₀
      (by norm_num : (0 : ℝ) < 1 / 4) hκ
  choose Ht hHt htrans using fun i ↦ htransport i C₀ (1 / 4) κ
    (by norm_num) hκ
  let D : I → ℕ → ℝ := fun i m ↦ Hq i m * (1 + Hp i (m + 3))
  have hD (i) (m) : 0 ≤ D i m := by
    have := hHq i m
    have := hHp i (m + 3)
    dsimp [D]
    positivity
  let Bquotient := fun m ↦ (1 + ∑ i, D i m) * (1 + A (m + 6))
  let Btransport := fun m ↦ (1 + ∑ i, Ht i m) * (1 + A (m + 5))
  have hBq (m) : 0 ≤ Bquotient m :=
    mul_nonneg (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hD i m); linarith)
      (by linarith [hA (m + 6)])
  have hBt (m) : 0 ≤ Btransport m :=
    mul_nonneg (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ (hHt i m).le); linarith)
      (by linarith [hA (m + 5)])
  refine ⟨S, hS, C₀, hC₀, κ, hκ,
    A, E, Bphase, Bquotient, Btransport, Egeom, Eext, Bextended,
    hA, hE, hBp, hBq, hBt, hEg, hEe, hBe, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hscale := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith [hS.trans hR₀]) j
  let F := finiteHistoryMap G.map u
  obtain ⟨hF, hi, hrank, h4, h12, hclose, hmet, hnormal, hp, hgeom, hegeom,
    hesmooth, heeq, hesupport, heprofile, hlow, hcoeff⟩ := hhist R₀ hR₀ j u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank)
  have hcloseq (i) : cNorm (closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < δq i := by
    apply (cNorm_mono_set_of_contDiffAt (hball i) hK _).trans_lt
      (hclose.trans_le ((min_le_left _ _).trans
        ((hcommon i).2.1.trans (min_le_left _ _))))
    intro x hx
    exact ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
      contDiffAt_const).of_le (by simp)
  have hcloset (i) : cNorm (closedBall (0 : Euclidean n) r) 6
      (projectedStress F - fun _ ↦ cubeStress n) < δt i :=
    hclose.trans_le ((min_le_left _ _).trans ((hcommon i).2.1.trans (min_le_right _ _)))
  refine ⟨hF, hi, hrank, h4, h12, hclose.trans_le (min_le_right _ _), hmet, hnormal,
    hp, hgeom, hegeom, hesmooth, heeq, hesupport, heprofile, hlow, ?_⟩
  intro i
  dsimp only
  let T := family i
  let Q := (⟨projectedStress F, hframe, hlow i⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball 0 R) ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  obtain ⟨hfInv, htInv, hforwardF, hforwardT, hinverseF, hinverseT, hcompare, hqbound⟩ :=
    hquot i Q (hcloseq i)
  obtain ⟨hphaseProfile, hhamSmooth, hhamEq, hhamSupport, hhamProfile⟩ := hcoeff i
  obtain ⟨_, htransportCoeffs⟩ := htrans i F hF hi hrank h4
    (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx)) (hcloset i)
  refine ⟨hfInv, htInv, hphaseProfile, hhamSmooth, hhamEq, hhamSupport, hhamProfile,
    hforwardF, hforwardT, hinverseF, hinverseT, hcompare, ?_, ?_⟩
  · intro m
    have hphaseBound := hphase i F hF hi hrank h4
      (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx)) (hlow i) (m + 3)
    have hraw : extendedQuotientCoefficientNorm T Q (z i)
        (T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)) (qrad i)
        (ψF i) (ψT i) (χF i) (χT i) m ≤
        D i m * (1 + cNorm (closedBall 0 r) (m + 6) F) := by
      apply (hqbound m).trans
      dsimp only [D]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hHq i m).le
      simp only [show m + 3 + 3 = m + 6 by omega] at hphaseBound
      nlinarith [cNorm_nonneg (closedBall 0 r) (m + 6) F]
    have hh := JointBudget.fixed_profile_transfer_bound hscale (hA (m + 6))
      (hD i m) hreserve (hp (m + 6)) hraw
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
    apply mul_le_mul_of_nonneg_right _ (by linarith [hA (m + 6)])
    have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ D i m)
      (fun i _ ↦ hD i m) (Finset.mem_univ i)
    linarith
  · intro q
    obtain ⟨hkq, hlq, hden, hrecip, hdir, hpot, hnull, hdirBound,
      hek, hel, heden, herecip, hedir, hepot, hbounds⟩ := htransportCoeffs q
    refine ⟨hkq, hlq, hden, hrecip, hdir, hpot, ?_, hdirBound,
      hek, hel, heden, herecip, hedir, hepot, ?_⟩
    · intro w hw
      have hh := hnull w hw
      exact ⟨hh.1, hh.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.2⟩
    intro m
    refine ⟨(hbounds m).1, ?_⟩
    have hh := JointBudget.fixed_profile_transfer_bound hscale (hA (m + 5)) (hHt i m).le
      (show 5 + r₀ ≤ rStar by omega) (hp (m + 5)) (hbounds m).2
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
    apply mul_le_mul_of_nonneg_right _ (by linarith [hA (m + 5)])
    have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ Ht i m)
      (fun i _ ↦ (hHt i m).le) (Finset.mem_univ i)
    linarith

end JanetCartan.CurrentCoefficientProfiles
