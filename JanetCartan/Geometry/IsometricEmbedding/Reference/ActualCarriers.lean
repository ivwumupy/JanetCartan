module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.GapStability
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Detection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ZeroEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.AngularConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhysicalReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentCharts
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierRank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SharpPhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SingularGap
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedPhases
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedSignedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.QuantitativeMenu
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FiniteRank

/-!
# Constructions for the actual carrier menu

Checked components of `app:ch_seed:prop:seed-actual-menu`. The decorated frozen
menu is constructed inside any prescribed positive physical ball. Primitive
smooth-frame C⁶ closeness produces current Hamilton charts on the retained
reference targets and actual smooth zero-energy characteristic carriers, with
the same section and positive sign. The actual projected stresses inherit
uniform angular adjugate, rank, matrix and simple-zero gaps directly from the
paper's componentwise C⁶ frame neighborhood.

`exists_constructed_carrier_phases` now constructs the finite carrier phases
from primitive smooth-frame closeness, on common physical buffers, with the
same quantitative Hamilton charts, section identity, characteristic equation,
gradient comparison, upper parameter Lipschitz bound and positive projected
chord lower bound. `CarrierProperties` exposes those literal carriers for all
consumers. `CarrierRank` proves their uniform adjugate gap and rank exactly
`n-1`. `SharpPhaseBounds` instantiates the projected-frame estimate to prove
the sharp immersion-order `m+3` bound on those same full phases. The numbered
angular singular-value theorem is also available.

`exists_actual_carrier_menu` below performs the finite assembly.  It keeps the
signed-family angular closure and true-frequency bounds, the singular-value and
adjugate producer on the same angular set, and the continued incidence roots
and full detector inequality for the same carrier family under one positive
frame neighborhood. Its quantitative clause applies the projected incidence
budgets and reserve-six root estimate to the very same detector roots on a
fixed finite cover. `HasConstructedCarrierTameBounds` retains sharp phase
reserve three, carrier-gradient reserve four, and the literal finite maximum
with reserve six. The common threshold restrictions for signed and angular
singular statements are explicit conclusions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers
open FrozenMenu CurrentFullPhase ConstructedSignedGeometry SignedPairs ProjectedStressFrame

/-- The finite actual carrier menu, with all low-order constants chosen on one
fixed neighborhood.  This is the assembly of Steps 1--3 of
`app:ch_seed:prop:seed-actual-menu`: the same quantitative chart family is
used for the phase, signed-pair, continued-incidence and detector clauses.
The quantitative clause uses the literal projected stresses and the original
Setup hypotheses, including the separate metric/normal gaps and C⁴ bound.
It constructs the detector roots and proves the reserve-six maximum for those
same witnesses. The positive frame threshold precedes every derivative order
and immersion; its restrictions to the signed and singular neighborhoods are
explicit. The sharp phase and carrier-gradient reserves remain available. -/
theorem exists_actual_carrier_menu {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : closedBall (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        ∃ r K εmax : ℝ, 0 < r ∧ 3 * r < min b 1 ∧ 1 ≤ K ∧
          0 < εmax ∧ εmax ≤ 1 ∧ K * εmax ≤ c / 2 ∧
          (∀ i, 3 * r < (T i).reference.radius) ∧
          IsCompact (closedBall (0 : Euclidean n) b) ∧
          (closedBall (0 : Euclidean n) b) ⊆ U ∧
          ∀ (G : Type*) [Finite G]
            (assign : G → (j : Fin D.chartCount) × Fin (D.patchCount j)),
            ∃ Rlabel : G → ℝ, (∀ g, 1 ≤ Rlabel g) ∧
              Function.Injective Rlabel ∧
              ∃ δlabel γ a A : ℝ, 0 < δlabel ∧ 0 < γ ∧ 0 < a ∧ 0 < A ∧
                IsCompact (angularSet n γ) ∧
                (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
                (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n,
                  γ ≤ dist v w) ∧
                Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
                ∃ hlowLabel : ∀ (Q : FrameNeighborhood U
                    (closedBall (0 : Euclidean n) b) δlabel) i,
                    cNorm (closedBall (0 : Euclidean n)
                      (T i).data.localReference.stateRadius) 6
                        (Q.1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
                  (closure (directionSet
                      (fun p : FrameNeighborhood U (closedBall 0 b) δlabel ×
                        closedBall (0 : Euclidean n) r ↦
                        currentGroup T assign Rlabel p.1.1 p.1.2.1
                          (hlowLabel p.1) p.2)
                      (groupCube D assign)) ⊆ angularSet n γ ∧
                    ∀ (p : FrameNeighborhood U (closedBall 0 b) δlabel ×
                        closedBall (0 : Euclidean n) r)
                      (q : Pair G (Euclidean 3) (groupCube D assign)),
                      (∀ L ∈ cubeBadSubspaces n,
                        a * q.beat ≤ ‖projectAway L
                          (q.vector (currentGroup T assign Rlabel p.1.1
                            p.1.2.1 (hlowLabel p.1) p.2))‖) ∧
                      q.vector (currentGroup T assign Rlabel p.1.1 p.1.2.1
                        (hlowLabel p.1) p.2) ≠ 0 ∧
                      (∀ lam : ℝ, 0 ≤ lam →
                        a * (lam * q.beat) ≤ ‖lam •
                          q.vector (currentGroup T assign Rlabel p.1.1 p.1.2.1
                            (hlowLabel p.1) p.2)‖ ∧
                        ‖lam • q.vector (currentGroup T assign Rlabel p.1.1
                          p.1.2.1 (hlowLabel p.1) p.2)‖ ≤ A * (lam * q.beat))) ∧
                ∃ δsing asing csing ds M : ℝ,
                  0 < δsing ∧ 0 < asing ∧ 0 < csing ∧ 0 < ds ∧ 0 < M ∧
                  (∀ (N : ℕ) (F : Euclidean n → Euclidean N)
                    (V K₀ : Set (Euclidean n)), IsOpen V → IsCompact K₀ →
                    K₀ ⊆ V → ContDiffOn ℝ ∞ F V → IsImmersionOn F V →
                    HasFullNormalRankOn F V →
                    (∀ i, cNorm K₀ 6
                      (fun x ↦ projectedStress F x i - cubeStress n i) < δsing) →
                    ∀ x ∈ K₀, ∀ v ∈ angularSet n γ,
                      asing ≤ ‖(pencil (projectedStress F x) v).adjugate‖ ∧
                      n - 1 ≤ (pencil (projectedStress F x) v).rank ∧
                      ‖pencil (projectedStress F x) v‖ ≤ M ∧
                      csing ≤ (pencil (projectedStress F x) v).toEuclideanLin.singularValues
                        (⟨n - 2, by omega⟩ : Fin n) ∧
                      (determinant (projectedStress F x) v = 0 →
                        ds ≤ ‖fderiv ℝ (determinant (projectedStress F x)) v‖)) ∧
                ∃ Rroot : IncidenceRefinement D, Rroot.IsValid ∧
                  ∃ η cr Br εroot cdet δroot : ℝ,
                    0 < η ∧ 0 < cr ∧ 0 < Br ∧ 0 < εroot ∧ 0 < cdet ∧
                    0 < δroot ∧
                    (∀ j a', ∀ t ∈ Icc (-Rroot.halfWidth j a')
                      (Rroot.halfWidth j a'), ∀ i : Fin 3,
                      |incidenceParameter (D.roots (Rroot.sourceChart j) a'
                        (Rroot.center j)) t i| + η <
                        (D.patches (Rroot.sourceChart j) a').radius) ∧
                    ∃ arank : ℝ, 0 < arank ∧
                    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δlabel ∧ δ ≤ δsing ∧
                      (∀ (Q : Euclidean n → Fin n → MetricTensor n)
                        (hQ : ContDiffOn ℝ ∞ Q U),
                        (∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
                          (fun x ↦ Q x j - cubeStress n j) < δ) →
                        ∃ hlowPhase : ∀ i, cNorm (closedBall (0 : Euclidean n)
                            (T i).data.localReference.stateRadius) 6
                              (Q - fun _ ↦ cubeStress n) <
                            (T i).family.threshold,
                          (∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
                              (normalizedHomogeneousSymbol hU Q hQ) (εmax / 2),
                            I.flow = (T i).family.flow
                              ⟨Q, hQ, hlowPhase i⟩ ∧
                            HEq I.chart ((T i).currentChart
                              ⟨Q, hQ, hlowPhase i⟩) ∧
                            IsAssembledCarrierPhase (T i).reference I Q
                              ((T i).carrier ⟨Q, hQ, hlowPhase i⟩) r K (εmax / 2) ∧
                            (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
                              ∀ z ∈ parameterCube
                                (D.patches i.1 i.2).radius,
                              ∀ w ∈ parameterCube
                                (D.patches i.1 i.2).radius,
                              ∀ L ∈ cubeBadSubspaces n,
                                (c / 2) * ‖z - w‖ ≤
                                  ‖Lᗮ.orthogonalProjectionOnto
                                    ((T i).carrierGradient
                                      ⟨Q, hQ, hlowPhase i⟩ x z -
                                      (T i).carrierGradient
                                        ⟨Q, hQ, hlowPhase i⟩ x w)‖)) ∧
                          (∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
                            ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
                              arank ≤ ‖(pencil (Q x)
                                ((T i).carrierGradient ⟨Q, hQ, hlowPhase i⟩ x z)).adjugate‖ ∧
                              (pencil (Q x) ((T i).carrierGradient
                                ⟨Q, hQ, hlowPhase i⟩ x z)).rank = n - 1) ∧
                          ∃ hlowInc : ∀ i, cNorm (closedBall (0 : Euclidean n)
                            (T i).data.localReference.stateRadius) 6
                              (Q - fun _ ↦ cubeStress n) <
                            (T i).family.threshold,
                          ∃ g : (j : Fin Rroot.chartCount) →
                              Fin (D.patchCount (Rroot.sourceChart j)) →
                              Euclidean n × Euclidean n → ℝ,
                            IsConstructedIncidenceRootFamily D Rroot r cr Br
                              εroot Q
                              (fun j a' ↦ (T ⟨j, a'⟩).carrier
                                ⟨Q, hQ, hlowInc ⟨j, a'⟩⟩) g ∧
                            ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
                              ∀ k ∈ closedBall (Rroot.center j)
                                (Rroot.radius j), ∀ s : Euclidean n,
                              cdet * ‖s‖ ^ 2 ≤
                                ‖imageChannel (pencil (Q x) k) s‖ ^ 2 +
                                ∑ a', ⟪quadratic (Q x)
                                  ((T ⟨Rroot.sourceChart j, a'⟩).carrierGradient
                                    ⟨Q, hQ, hlowInc ⟨Rroot.sourceChart j, a'⟩⟩ x
                                    (incidenceParameter
                                      (D.roots (Rroot.sourceChart j) a'
                                        (Rroot.center j))
                                      (g j a' (x, k)))), s⟫_ℝ ^ 2) ∧
                      ∀ (N : ℕ) (C₀ κmet κ : ℝ), 0 < κmet → 0 < κ →
                        ∃ δt > (0 : ℝ), δt ≤ δ ∧ ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
                        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
                          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
                          cNorm (closedBall (0 : Euclidean n) b) 4 F ≤ C₀ →
                          (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v,
                            κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
                          (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ w ∈ normalSpace F x,
                            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
                          (∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
                            (fun x ↦ projectedStress F x j - cubeStress n j) < δt) →
                          let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
                          ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
                            (T i).data.localReference.stateRadius) 6
                              (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
                          ∃ g : (j : Fin Rroot.chartCount) →
                            Fin (D.patchCount (Rroot.sourceChart j)) → Euclidean n × Euclidean n → ℝ,
                            IsConstructedIncidenceRootFamily D Rroot r cr Br εroot (projectedStress F)
                              (fun j a' ↦ (T ⟨j, a'⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a'⟩⟩) g ∧
                            (∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
                              ∀ k ∈ closedBall (Rroot.center j) (Rroot.radius j), ∀ s : Euclidean n,
                              cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress F x) k) s‖ ^ 2 +
                                ∑ a', ⟪quadratic (projectedStress F x)
                                  ((T ⟨Rroot.sourceChart j, a'⟩).carrierGradient
                                    ⟨projectedStress F, hQ, hlow ⟨Rroot.sourceChart j, a'⟩⟩ x
                                    (incidenceParameter (D.roots (Rroot.sourceChart j) a'
                                      (Rroot.center j)) (g j a' (x, k)))), s⟫_ℝ ^ 2) ∧
                            HasConstructedCarrierTameBounds T Rroot r
                              (closedBall (0 : Euclidean n) b) A F hQ hlow g := by
  classical
  obtain ⟨D, c, C, hD, T, hphysical, r, K, εmax, hr, hrmin, hK,
      hε, hε1, hKε, hrefRadius, hphaseThreshold⟩ :=
    exists_constructed_carrier_phases hn hU hb hBU
  have hcompact : IsCompact (closedBall (0 : Euclidean n) b) :=
    isCompact_closedBall _ _
  have hball : ∀ i, closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius ⊆ closedBall 0 b := by
    intro i x hx
    apply ball_subset_closedBall
    apply hphysical i (x, (T i).data.center)
    apply (T i).data.localReference.stateBall_subset
    rw [(T i).data.adapted.baseState_eq]
    simpa only [mem_closedBall, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg)] using hx
  have hphysRadius : ∀ i, 3 * r < (T i).physicalRadius := by
    intro i
    have hh := hrefRadius i
    change 3 * r < (T i).physicalRadius at hh
    exact hh
  have hphysRadius' : ∀ i, r < (T i).physicalRadius := by
    intro i
    linarith [hphysRadius i, hr]
  have hrb : 3 * r < b := lt_of_lt_of_le hrmin (min_le_left _ _)
  have hhalf : 0 < εmax / 2 := by positivity
  have hhalf_le : εmax / 2 ≤ εmax := by linarith
  obtain ⟨δphase, hδphase, hphase⟩ :=
    hphaseThreshold (εmax / 2) hhalf hhalf_le
  refine ⟨D, c, C, hD, T, hphysical, r, K, εmax, hr, hrmin, hK,
    hε, hε1, hKε, hrefRadius, hcompact, hBU, ?_⟩
  intro G _ assign
  obtain ⟨Rlabel, hRlabel, hinj, δlabel, γ, a, A, hδlabel, hγ, ha, hA,
      hcompactγ, hsymγ, hgapγ, hdisjγ, hSigned⟩ :=
    exists_constructed_signed_geometry hn hD T G assign hcompact hBU hball
      hr hphysRadius'
  obtain ⟨hlowLabel, hclosure, hpairs⟩ := hSigned
  obtain ⟨δsing, asing, csing, ds, M, hδsing, hasing, hcsing, hds, hM,
      hsing⟩ := exists_projectedStress_angular_singular_neighborhood hn hγ
  obtain ⟨Rroot, hRroot, η, cr, Br, εroot, cdet, δroot, hη, hcr, hBr,
      hεroot, hcdet, hδroot, hbuffer, hroot⟩ :=
    exists_constructed_incidence_detection hD T hBU hball hr hphysRadius hrb
  obtain ⟨δrank, arank, hδrank, harank, hcarrierRank⟩ :=
    exists_constructed_carrier_rank_bound (by omega : 2 ≤ n) hD T hr hphysRadius
      hcompact hBU hball
  let δ : ℝ := min εmax (min δphase (min δlabel (min δsing (min δroot δrank))))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le_phase : δ ≤ δphase := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_label : δ ≤ δlabel := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_sing : δ ≤ δsing := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_le_root : δ ≤ δroot := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδ_le_rank : δ ≤ δrank := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  refine ⟨Rlabel, hRlabel, hinj, δlabel, γ, a, A, hδlabel, hγ, ha, hA,
    hcompactγ, hsymγ, hgapγ, hdisjγ, hlowLabel, ⟨hclosure, hpairs⟩,
    δsing, asing, csing, ds, M, hδsing, hasing, hcsing, hds, hM, hsing,
    Rroot, hRroot, η, cr, Br, εroot, cdet, δroot, hη, hcr, hBr, hεroot,
    hcdet, hδroot, hbuffer, arank, harank, δ, hδ, hδ_le_label, hδ_le_sing, ?_, ?_⟩
  · intro Q hQ hclose
    have hclosePhase : ∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
        (fun x ↦ Q x j - cubeStress n j) < δphase :=
      fun j ↦ lt_of_lt_of_le (hclose j) hδ_le_phase
    obtain ⟨hlowPhase, hphaseQ⟩ := hphase Q hQ hclosePhase
    have hcloseRoot : ∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
        (fun x ↦ Q x j - cubeStress n j) < δroot :=
      fun j ↦ lt_of_lt_of_le (hclose j) hδ_le_root
    obtain ⟨hlowInc, g, hg, hdet⟩ := hroot Q hQ hcloseRoot
    refine ⟨hlowPhase, hphaseQ, ?_, hlowInc, g, hg, hdet⟩
    exact hcarrierRank Q hQ (fun j ↦ (hclose j).trans_le hδ_le_rank) hlowPhase
  · intro N C₀ κmet κ hκmet hκ
    obtain ⟨dt, hdt, At, hAt, htame⟩ := exists_constructed_carrier_tame_bounds (N := N)
      hD T hRroot hr hphysRadius hcompact hBU hball C₀ hκmet hκ hcr
    refine ⟨min δ dt, lt_min hδ hdt, min_le_left _ _, At, hAt, ?_⟩
    intro F hF hi hrank hlowF hmet hnormal hclose
    dsimp only
    let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
    obtain ⟨hlow, g, hg, hdet⟩ := hroot (projectedStress F) hQ
      (fun j ↦ (hclose j).trans_le ((min_le_left _ _).trans hδ_le_root))
    refine ⟨hlow, g, hg, hdet, ?_⟩
    exact htame F hF hi hrank hlowF hmet hnormal
      (fun j ↦ (hclose j).trans_le (min_le_right _ _)) hlow g Br εroot hg

end JanetCartan.ActualCarriers
