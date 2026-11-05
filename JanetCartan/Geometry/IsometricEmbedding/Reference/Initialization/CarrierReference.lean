module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.GeometricReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers

/-!
# The actual reference with its fixed carrier gaps

The geometric construction in `main:prop:seed`. The analytic reference is
constructed first. The finite Hamilton family and its thresholds are fixed,
then one source scale places the actual projected stresses in that neighborhood.
The carrier phases, incidence roots and detector all use this same reference.
The smaller reference domain lies inside the carrier buffer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan
open GeometricProfile ProtectedFlow
open ProjectedStressFrame ActualCarriers FrozenMenu ActualCarriers.CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs

/-- Construct the analytic source, its fixed dilation, the actual Hamilton
carrier menu and positive geometric gaps (`main:prop:seed`,
`app:ch_seed:prop:seed-actual-menu`). Every analytic premise of the low carrier
construction is discharged. The reference and its C8 neighborhood precede
every target and requested accuracy. The normal gap is on the actual normal
spaces. Signed frequencies retain the short-chord factor, and the detector
uses the same incidence roots as the returned root family. The source and
finite carrier charts are fixed before the requested finite full-coefficient
margins and cutoff parameters; these precede the one source scale. The local
full-array ball contains the actual working chart since `3 * r < b`. The
fixed affine extension satisfies the prescribed global margins against the
zero lower-order background (`app:ch_regular:eq:coefficient-extension`).
The carrier state domains lie in `ball 0 b`, and each physical
radius exceeds `3 * r`, before any extension parameters, finite margins
or source-scale cap are requested. These are the buffers consumed by
`ProtectedFlow.exists_primitive_signed_no_return`
(`app:ch_regular:thm:no-return`); `frameBall_subset_of_stateDomain`
converts state-domain containment to closed frame-ball containment. -/
theorem exists_reference_with_carrier_buffers_and_full_margins {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        (∀ i, 3 * r < (T i).reference.radius) ∧
      ∀ (p : BallExtension.Parameters (Euclidean n))
        (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ),
        (∀ j ∈ orders, 0 < margin j) →
        (∀ j ∈ orders, 0 < extendedMargin j) →
        ∀ cap : ℝ, 0 < cap →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.domain.coreRadius = r / 2 ∧ G.domain.chartRadius = r ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean n) b) j
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
      ∃ δ C₀ κ εframe : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧ 0 < εframe ∧
        (∀ (V : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
          IsOpen V → closedBall 0 R ⊆ V → ContDiffOn ℝ ∞ F V →
          cNorm (closedBall 0 R) 8 (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
          (∀ x ∈ ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
          (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
          ∀ i, cNorm (closedBall 0 b) 6
            (fun x ↦ projectedStress F x i - cubeStress n i) < εframe) ∧
        IsImmersionOn G.map (ball 0 R) ∧ HasFullNormalRankOn G.map (ball 0 R) ∧
        cNorm (closedBall 0 b) 4 G.map ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ G.map x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace G.map x,
          κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖) ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R),
      ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T i).family.threshold,
        (∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
            (normalizedHomogeneousSymbol isOpen_ball (projectedStress G.map) hQ) (ε / 2),
          I.flow = (T i).family.flow ⟨projectedStress G.map, hQ, hlow i⟩ ∧
          HEq I.chart ((T i).currentChart ⟨projectedStress G.map, hQ, hlow i⟩) ∧
          IsAssembledCarrierPhase (T i).reference I (projectedStress G.map)
            ((T i).carrier ⟨projectedStress G.map, hQ, hlow i⟩) r K (ε / 2) ∧
          (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
            ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            ∀ w ∈ parameterCube (D.patches i.1 i.2).radius, ∀ L ∈ cubeBadSubspaces n,
              (c / 2) * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto
                ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z -
                  (T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x w)‖)) ∧
        (∃ arank > (0 : ℝ), ∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
          ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            arank ≤ ‖(pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).adjugate‖ ∧
            (pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).rank = n - 1) ∧
        (∃ label : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
          (∀ i, 1 ≤ label i) ∧ Function.Injective label ∧
          ∃ γ a A asing csing ds M : ℝ,
            0 < γ ∧ 0 < a ∧ 0 < A ∧ 0 < asing ∧ 0 < csing ∧ 0 < ds ∧ 0 < M ∧
            IsCompact (angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
            Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
            (closure (directionSet
              (fun x : closedBall (0 : Euclidean n) r ↦
                currentGroup T id label (projectedStress G.map) hQ hlow x)
              (groupCube D id)) ⊆ angularSet n γ) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) r,
              ∀ q : Pair ((j : Fin D.chartCount) × Fin (D.patchCount j))
                  (Euclidean 3) (groupCube D id),
                (∀ L ∈ cubeBadSubspaces n,
                  a * q.beat ≤ ‖projectAway L
                    (q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x))‖) ∧
                q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x) ≠ 0 ∧
                (∀ lam : ℝ, 0 ≤ lam →
                  a * (lam * q.beat) ≤ ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ∧
                  ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ≤
                    A * (lam * q.beat))) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v ∈ angularSet n γ,
              asing ≤ ‖(pencil (projectedStress G.map x) v).adjugate‖ ∧
              n - 1 ≤ (pencil (projectedStress G.map x) v).rank ∧
              ‖pencil (projectedStress G.map x) v‖ ≤ M ∧
              csing ≤ (pencil (projectedStress G.map x) v).toEuclideanLin.singularValues
                (⟨n - 2, by omega⟩ : Fin n) ∧
              (determinant (projectedStress G.map x) v = 0 →
                ds ≤ ‖fderiv ℝ (determinant (projectedStress G.map x)) v‖))) ∧
        ∃ Rroot : IncidenceRefinement D, Rroot.IsValid ∧
          ∃ cr Br εroot cdet : ℝ, 0 < cr ∧ 0 < Br ∧ 0 < εroot ∧ 0 < cdet ∧
          ∃ g : (j : Fin Rroot.chartCount) → Fin (D.patchCount (Rroot.sourceChart j)) →
              Euclidean n × Euclidean n → ℝ,
            IsConstructedIncidenceRootFamily D Rroot r cr Br εroot (projectedStress G.map)
              (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress G.map, hQ, hlow ⟨j, a⟩⟩) g ∧
            ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
              ∀ k ∈ closedBall (Rroot.center j) (Rroot.radius j), ∀ s : Euclidean n,
                cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress G.map x) k) s‖ ^ 2 +
                  ∑ a, ⟪quadratic (projectedStress G.map x)
                    ((T ⟨Rroot.sourceChart j, a⟩).carrierGradient
                      ⟨projectedStress G.map, hQ, hlow ⟨Rroot.sourceChart j, a⟩⟩ x
                      (incidenceParameter (D.roots (Rroot.sourceChart j) a (Rroot.center j))
                        (g j a (x, k)))), s⟫_ℝ ^ 2 := by
  classical
  obtain ⟨G₀, hG₀⟩ := exists_analytic_flatReference hn
  let b := G₀.domain.coreRadius / 2
  let R := G₀.domain.coreRadius
  have hb : 0 < b := half_pos G₀.domain.coreRadius_pos
  have hbR : b < R := by dsimp [b, R]; linarith [G₀.domain.coreRadius_pos]
  have hR : R < G₀.domain.chartRadius := G₀.domain.coreRadius_lt_chartRadius
  have hBU : closedBall (0 : Euclidean n) b ⊆ ball 0 R := closedBall_subset_ball hbR
  obtain ⟨D, c, C, hD, T, hphysical, r, K, ε, hr, hrmin, hK, hε, hε1, hKε,
    hradius, hcompact, _, hmenu⟩ := exists_actual_carrier_menu hn isOpen_ball hb hBU
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  obtain ⟨label, hlabel, hinj, δlabel, γ, a, A, hδlabel, hγ, ha, hA,
    hcompactγ, hsymγ, hgapγ, hdisjγ, hlowLabel, ⟨hclosure, hpairs⟩,
    δsing, asing, csing, ds, M, hδsing, hasing, hcsing, hds, hM, hsing,
    Rroot, hRroot, η, cr, Br, εroot, cdet, δroot, hη, hcr, hBr, hεroot,
    hcdet, hδroot, hbuffer, arank, harank, εframe, hεframe,
    hlabelCap, hsingCap, hproduce, _⟩ := hmenu J id
  have hrb : 3 * r < b := hrmin.trans_le (min_le_left _ _)
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hphysical, hradius, ?_⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  obtain ⟨ρ, hρ, hρcap, hρ1, Gwide, hwideDomain, hwideMap, hfull, hextSmooth,
    hextended, _, δ, C₀, κ, hδ, hC₀, hκ, hnear⟩ :=
    exists_scaled_reference_geometric_neighborhood_with_full_margins G₀ hb hbR hR hεframe
      p orders margin extendedMargin hmargin hextendedMargin hcap
  have hrchart : r < Gwide.domain.chartRadius := by
    rw [hwideDomain]
    linarith
  let domain : LocalDomain :=
    ⟨r / 2, r, half_pos hr, by linarith, hrchart.trans (by
      rw [hwideDomain]; exact G₀.domain.chartRadius_lt_half)⟩
  let G : FlatReference n := { Gwide with
    domain := domain
    fullNormalRank := fun x hx ↦ Gwide.fullNormalRank x
      (ball_subset_ball hrchart.le hx) }
  have hnearG := hnear univ G.map isOpen_univ (subset_univ _)
    G.contDiff.contDiffOn (by simpa only [show G.map = Gwide.map from rfl, sub_self,
      cNorm_zero] using hδ)
  obtain ⟨hi, hrank, hlowF, hmet, hnormal, hsmooth, hclose⟩ := hnearG
  have hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R) := contDiffOn_pi.mpr hsmooth
  obtain ⟨hlow, hphase, hcarrierRank, hlowInc, g, hg, hdetect⟩ :=
    hproduce (projectedStress G.map) hQ hclose
  let Qlabel : FrameNeighborhood (ball (0 : Euclidean n) R) (closedBall 0 b) δlabel :=
    ⟨projectedStress G.map, hQ, fun i ↦ (hclose i).trans_le hlabelCap⟩
  refine ⟨ρ, hρ, hρcap, hρ1, G, hwideMap, rfl, rfl, hfull, hextSmooth, hextended,
    δ, C₀, κ, εframe, hδ, hC₀, hκ, hεframe, hnear,
    hi, hrank, hlowF, hmet, hnormal, hQ, hlow, hphase,
    ⟨arank, harank, hcarrierRank⟩, ?_, Rroot, hRroot, cr, Br, εroot, cdet,
    hcr, hBr, hεroot, hcdet, g, hg, hdetect⟩
  refine ⟨label, hlabel, hinj, γ, a, A, asing, csing, ds, M,
    hγ, ha, hA, hasing, hcsing, hds, hM, hcompactγ, hsymγ, hgapγ, hdisjγ, ?_, ?_, ?_⟩
  · apply subset_trans (closure_mono ?_) hclosure
    rintro v ⟨x, q, rfl⟩
    exact ⟨(Qlabel, x), q, rfl⟩
  · intro x hx q
    exact hpairs (Qlabel, ⟨x, hx⟩) q
  · exact hsing (embeddingDimension n) G.map (ball 0 R) (closedBall 0 b)
      isOpen_ball hcompact hBU G.contDiff.contDiffOn hi hrank
      (fun i ↦ (hclose i).trans_le hsingCap)

/-- The full-margin reference constructor with its original interface
(`main:prop:seed`, `app:ch_regular:eq:coefficient-extension`). The stronger
`exists_reference_with_carrier_buffers_and_full_margins` also retains the
carrier state-domain containment and physical-radius buffers. -/
theorem exists_reference_with_carrier_gaps_and_full_margins {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
      ∀ (p : BallExtension.Parameters (Euclidean n))
        (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ),
        (∀ j ∈ orders, 0 < margin j) →
        (∀ j ∈ orders, 0 < extendedMargin j) →
        ∀ cap : ℝ, 0 < cap →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.domain.coreRadius = r / 2 ∧ G.domain.chartRadius = r ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean n) b) j
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
      ∃ δ C₀ κ εframe : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧ 0 < εframe ∧
        (∀ (V : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
          IsOpen V → closedBall 0 R ⊆ V → ContDiffOn ℝ ∞ F V →
          cNorm (closedBall 0 R) 8 (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
          (∀ x ∈ ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
          (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
          ∀ i, cNorm (closedBall 0 b) 6
            (fun x ↦ projectedStress F x i - cubeStress n i) < εframe) ∧
        IsImmersionOn G.map (ball 0 R) ∧ HasFullNormalRankOn G.map (ball 0 R) ∧
        cNorm (closedBall 0 b) 4 G.map ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ G.map x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace G.map x,
          κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖) ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R),
      ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T i).family.threshold,
        (∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
            (normalizedHomogeneousSymbol isOpen_ball (projectedStress G.map) hQ) (ε / 2),
          I.flow = (T i).family.flow ⟨projectedStress G.map, hQ, hlow i⟩ ∧
          HEq I.chart ((T i).currentChart ⟨projectedStress G.map, hQ, hlow i⟩) ∧
          IsAssembledCarrierPhase (T i).reference I (projectedStress G.map)
            ((T i).carrier ⟨projectedStress G.map, hQ, hlow i⟩) r K (ε / 2) ∧
          (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
            ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            ∀ w ∈ parameterCube (D.patches i.1 i.2).radius, ∀ L ∈ cubeBadSubspaces n,
              (c / 2) * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto
                ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z -
                  (T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x w)‖)) ∧
        (∃ arank > (0 : ℝ), ∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
          ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            arank ≤ ‖(pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).adjugate‖ ∧
            (pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).rank = n - 1) ∧
        (∃ label : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
          (∀ i, 1 ≤ label i) ∧ Function.Injective label ∧
          ∃ γ a A asing csing ds M : ℝ,
            0 < γ ∧ 0 < a ∧ 0 < A ∧ 0 < asing ∧ 0 < csing ∧ 0 < ds ∧ 0 < M ∧
            IsCompact (angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
            Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
            (closure (directionSet
              (fun x : closedBall (0 : Euclidean n) r ↦
                currentGroup T id label (projectedStress G.map) hQ hlow x)
              (groupCube D id)) ⊆ angularSet n γ) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) r,
              ∀ q : Pair ((j : Fin D.chartCount) × Fin (D.patchCount j))
                  (Euclidean 3) (groupCube D id),
                (∀ L ∈ cubeBadSubspaces n,
                  a * q.beat ≤ ‖projectAway L
                    (q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x))‖) ∧
                q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x) ≠ 0 ∧
                (∀ lam : ℝ, 0 ≤ lam →
                  a * (lam * q.beat) ≤ ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ∧
                  ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ≤
                    A * (lam * q.beat))) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v ∈ angularSet n γ,
              asing ≤ ‖(pencil (projectedStress G.map x) v).adjugate‖ ∧
              n - 1 ≤ (pencil (projectedStress G.map x) v).rank ∧
              ‖pencil (projectedStress G.map x) v‖ ≤ M ∧
              csing ≤ (pencil (projectedStress G.map x) v).toEuclideanLin.singularValues
                (⟨n - 2, by omega⟩ : Fin n) ∧
              (determinant (projectedStress G.map x) v = 0 →
                ds ≤ ‖fderiv ℝ (determinant (projectedStress G.map x)) v‖))) ∧
        ∃ Rroot : IncidenceRefinement D, Rroot.IsValid ∧
          ∃ cr Br εroot cdet : ℝ, 0 < cr ∧ 0 < Br ∧ 0 < εroot ∧ 0 < cdet ∧
          ∃ g : (j : Fin Rroot.chartCount) → Fin (D.patchCount (Rroot.sourceChart j)) →
              Euclidean n × Euclidean n → ℝ,
            IsConstructedIncidenceRootFamily D Rroot r cr Br εroot (projectedStress G.map)
              (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress G.map, hQ, hlow ⟨j, a⟩⟩) g ∧
            ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
              ∀ k ∈ closedBall (Rroot.center j) (Rroot.radius j), ∀ s : Euclidean n,
                cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress G.map x) k) s‖ ^ 2 +
                  ∑ a, ⟪quadratic (projectedStress G.map x)
                    ((T ⟨Rroot.sourceChart j, a⟩).carrierGradient
                      ⟨projectedStress G.map, hQ, hlow ⟨Rroot.sourceChart j, a⟩⟩ x
                      (incidenceParameter (D.roots (Rroot.sourceChart j) a (Rroot.center j))
                        (g j a (x, k)))), s⟫_ℝ ^ 2 := by
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, _hphysical, _hradius, hchoose⟩ :=
    exists_reference_with_carrier_buffers_and_full_margins hn
  exact ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hchoose⟩

/-- Construct the analytic source, its fixed dilation, the actual Hamilton
carrier menu and positive geometric gaps (`main:prop:seed`,
`app:ch_seed:prop:seed-actual-menu`). Every analytic premise of the low carrier
construction is discharged. The reference and its C8 neighborhood precede
every target and requested accuracy. The normal gap is on the actual normal
spaces. Signed frequencies retain the short-chord factor, and the detector
uses the same incidence roots as the returned root family. -/
theorem exists_reference_with_carrier_gaps {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.domain.coreRadius = r / 2 ∧ G.domain.chartRadius = r ∧
      ∃ δ C₀ κ εframe : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧ 0 < εframe ∧
        (∀ (V : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
          IsOpen V → closedBall 0 R ⊆ V → ContDiffOn ℝ ∞ F V →
          cNorm (closedBall 0 R) 8 (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
          (∀ x ∈ ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
          (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
          ∀ i, cNorm (closedBall 0 b) 6
            (fun x ↦ projectedStress F x i - cubeStress n i) < εframe) ∧
        IsImmersionOn G.map (ball 0 R) ∧ HasFullNormalRankOn G.map (ball 0 R) ∧
        cNorm (closedBall 0 b) 4 G.map ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ G.map x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace G.map x,
          κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖) ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R),
      ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T i).family.threshold,
        (∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
            (normalizedHomogeneousSymbol isOpen_ball (projectedStress G.map) hQ) (ε / 2),
          I.flow = (T i).family.flow ⟨projectedStress G.map, hQ, hlow i⟩ ∧
          HEq I.chart ((T i).currentChart ⟨projectedStress G.map, hQ, hlow i⟩) ∧
          IsAssembledCarrierPhase (T i).reference I (projectedStress G.map)
            ((T i).carrier ⟨projectedStress G.map, hQ, hlow i⟩) r K (ε / 2) ∧
          (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
            ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            ∀ w ∈ parameterCube (D.patches i.1 i.2).radius, ∀ L ∈ cubeBadSubspaces n,
              (c / 2) * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto
                ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z -
                  (T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x w)‖)) ∧
        (∃ arank > (0 : ℝ), ∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
          ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            arank ≤ ‖(pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).adjugate‖ ∧
            (pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).rank = n - 1) ∧
        (∃ label : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
          (∀ i, 1 ≤ label i) ∧ Function.Injective label ∧
          ∃ γ a A asing csing ds M : ℝ,
            0 < γ ∧ 0 < a ∧ 0 < A ∧ 0 < asing ∧ 0 < csing ∧ 0 < ds ∧ 0 < M ∧
            IsCompact (angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
            Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
            (closure (directionSet
              (fun x : closedBall (0 : Euclidean n) r ↦
                currentGroup T id label (projectedStress G.map) hQ hlow x)
              (groupCube D id)) ⊆ angularSet n γ) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) r,
              ∀ q : Pair ((j : Fin D.chartCount) × Fin (D.patchCount j))
                  (Euclidean 3) (groupCube D id),
                (∀ L ∈ cubeBadSubspaces n,
                  a * q.beat ≤ ‖projectAway L
                    (q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x))‖) ∧
                q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x) ≠ 0 ∧
                (∀ lam : ℝ, 0 ≤ lam →
                  a * (lam * q.beat) ≤ ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ∧
                  ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ≤
                    A * (lam * q.beat))) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v ∈ angularSet n γ,
              asing ≤ ‖(pencil (projectedStress G.map x) v).adjugate‖ ∧
              n - 1 ≤ (pencil (projectedStress G.map x) v).rank ∧
              ‖pencil (projectedStress G.map x) v‖ ≤ M ∧
              csing ≤ (pencil (projectedStress G.map x) v).toEuclideanLin.singularValues
                (⟨n - 2, by omega⟩ : Fin n) ∧
              (determinant (projectedStress G.map x) v = 0 →
                ds ≤ ‖fderiv ℝ (determinant (projectedStress G.map x)) v‖))) ∧
        ∃ Rroot : IncidenceRefinement D, Rroot.IsValid ∧
          ∃ cr Br εroot cdet : ℝ, 0 < cr ∧ 0 < Br ∧ 0 < εroot ∧ 0 < cdet ∧
          ∃ g : (j : Fin Rroot.chartCount) → Fin (D.patchCount (Rroot.sourceChart j)) →
              Euclidean n × Euclidean n → ℝ,
            IsConstructedIncidenceRootFamily D Rroot r cr Br εroot (projectedStress G.map)
              (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress G.map, hQ, hlow ⟨j, a⟩⟩) g ∧
            ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
              ∀ k ∈ closedBall (Rroot.center j) (Rroot.radius j), ∀ s : Euclidean n,
                cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress G.map x) k) s‖ ^ 2 +
                  ∑ a, ⟪quadratic (projectedStress G.map x)
                    ((T ⟨Rroot.sourceChart j, a⟩).carrierGradient
                      ⟨projectedStress G.map, hQ, hlow ⟨Rroot.sourceChart j, a⟩⟩ x
                      (incidenceParameter (D.roots (Rroot.sourceChart j) a (Rroot.center j))
                        (g j a (x, k)))), s⟫_ℝ ^ 2 := by
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hchoose⟩ :=
    exists_reference_with_carrier_gaps_and_full_margins hn
  let p : BallExtension.Parameters (Euclidean n) :=
    ⟨0, b, hb, b / 4, by positivity, by linarith⟩
  obtain ⟨ρ, hρ, _, hρ1, G, hmap, hcore, hchart, _, _, _, hgeometry⟩ :=
    hchoose p ∅ (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 (by norm_num)
  exact ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, ρ, hρ, hρ1, G, hmap, hcore, hchart, hgeometry⟩

end JanetCartan
