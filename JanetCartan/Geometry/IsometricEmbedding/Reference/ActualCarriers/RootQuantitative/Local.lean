module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds

/-!
# Local quantitative estimates for the selected incidence roots

The consumer is the finite buffered-cylinder assembly of
`app:ch_seed:eq:seed-phase-tame`. The primitive budgets are instantiated for
the literal projected frame and the already selected carrier chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ProjectedStressFrame
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The entire physical carrier ball lies in the frame ball, as follows from
its actual Hamilton chart and the retained state bound. This supplies the
physical containment needed for the root jets (`app:ch_seed:eq:seed-phase-tame`). -/
theorem physicalBall_subset_frameBall {c C : ℝ} (hP : P.IsValid c C) :
    ball (0 : Euclidean n) T.physicalRadius ⊆
      closedBall (0 : Euclidean n) T.data.localReference.stateRadius := by
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨fun _ ↦ cubeStress n, contDiffOn_const, by
      simpa using T.family.threshold_pos⟩
  intro x hx
  have hz : (0 : Euclidean 3) ∈ parameterInterior (2 * P.radius) := by
    intro i
    simpa using (show 0 < 2 * P.radius by linarith [hP.1])
  have ht := T.reference.target_contains x hx 0 hz
  have hs := (T.currentChart Q).source_admissible _
    ((T.currentChart Q).maps_to_source _ ht)
  have hb := T.family.state_mem Q _ hs
  rw [(T.currentChart Q).right_inverse _ ht] at hb
  rw [mem_closedBall, Prod.dist_eq] at hb
  exact (le_max_left _ _).trans hb

/-- Apply the reserve-six implicit-root theorem to the actual projected
incidence coefficients on a fixed ball. The only root inputs are its proved
low construction properties; no root or incidence high estimate is assumed
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_projected_local_root_bound {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (a : (Euclidean n × Euclidean n) × ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : Euclidean 3)
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)}
    (hKx : IsCompact Kx) (hKz : IsCompact Kz)
    (hKxO : Kx ⊆ ball (0 : Euclidean n) T.physicalRadius)
    (hKzO : Kz ⊆ parameterInterior (2 * P.radius))
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ cr : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (hcr : 0 < cr) :
    ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ (s V : Set (Euclidean n × Euclidean n)), IsOpen V → s ⊆ V →
        ∀ (g : Euclidean n × Euclidean n → ℝ), ContDiffOn ℝ ∞ g V →
        (∀ p ∈ V, currentIncidence (projectedStress F) (T.carrier Q) z (p, g p) = 0) →
        (∀ p ∈ s, (p, g p) ∈ closedBall a ρ) →
        (∀ p ∈ s, cr ≤ |CharacteristicRoot.scalarDerivative
          (currentIncidence (projectedStress F) (T.carrier Q) z) (p, g p)|) →
        ∀ m, cNorm s m g ≤ A m * (1 + cNorm K (m + 6) F) := by
  obtain ⟨δ, L, hδT, TQ, Tξ, Tk, A, B, D, hδ, hL, hTQ, hTξ, hTk,
    hA, hB, hD, hW, hballW, hb⟩ := T.exists_projected_incidence_budgets (N := N)
      hP a ρ z hKx hKz hKxO hKzO (hKxO.trans (T.physicalBall_subset_frameBall hP))
      hx hz hK hKU hball C₀ hκmet hκ
  choose E hE he using fun m ↦ exists_cNorm_incidence_root_le_reserve_six
    a hρ hTQ hTξ hTk hL hcr (hA (max m 2)).le (hB (max m 2)).le
      (hD (max m 2)).le m hW hballW
  refine ⟨δ, hδ, E, hE, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow hclose
  dsimp only
  intro s V hV hsV g hg heq hgraph hgap m
  obtain ⟨hQ, hξ, hk, hQT, hξT, hkT, hlowp, hhigh⟩ :=
    hb F hF hi hrank hlowF hmet hnormal hclose
  exact he m _ _ _ hQ hξ hk hQT hξT hkT hlowp s V hV hsV g hg
    heq hgraph hgap F K (hhigh (max m 2)).1
      (hhigh (max m 2)).2.1 (hhigh (max m 2)).2.2

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
