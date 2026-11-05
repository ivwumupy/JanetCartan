module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.IncidenceHighBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.IncidenceLowBounds

/-!
# Primitive incidence budgets from the original immersion

This instantiates both the low and high estimates for the same projected frame
and the same canonical carrier gradient. It supplies every primitive field
budget of `exists_cNorm_incidence_root_le_reserve_six`, leaving only the actual
root, its transverse gap and the root-jet application to the parent assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ProjectedStressFrame
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- All primitive incidence inputs, on one fixed joint ball, from the original
immersion smoothness, separate metric/normal gaps, `C⁴` bound and primitive frame
`C⁶` neighborhood. Constants, compact ranges and threshold precede the immersion
and all high orders. No carrier estimate, dynamic range, root or root estimate
is assumed (`app:ch_seed:eq:seed-frame-tame`, `app:ch_seed:eq:seed-phase-tame`,
`app:ch_seed:prop:seed-actual-menu`, Steps 2–3). -/
theorem exists_projected_incidence_budgets {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (a : (Euclidean n × Euclidean n) × ℝ) (ρ : ℝ) (z : Euclidean 3)
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)}
    (hKx : IsCompact Kx) (hKz : IsCompact Kz)
    (hKxO : Kx ⊆ ball (0 : Euclidean n) T.physicalRadius)
    (hKzO : Kz ⊆ parameterInterior (2 * P.radius))
    (hKxframe : Kx ⊆ closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ (δ L : ℝ) (hδT : δ ≤ T.family.threshold)
      (TQ : Set (Fin n → MetricTensor n)) (Tξ Tk : Set (Euclidean n)) (A B D : ℕ → ℝ),
      0 < δ ∧ 0 ≤ L ∧ IsCompact TQ ∧ IsCompact Tξ ∧ IsCompact Tk ∧
      (∀ m, 0 < A m) ∧ (∀ m, 0 < B m) ∧ (∀ m, 0 < D m) ∧
      IsOpen (T.incidenceDomain z) ∧ closedBall a ρ ⊆ T.incidenceDomain z ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hclose : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < δ,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hclose.trans_le hδT⟩
        let Qp := fun p : (Euclidean n × Euclidean n) × ℝ ↦ projectedStress F p.1.1
        let ξp := fun p : (Euclidean n × Euclidean n) × ℝ ↦
          T.carrierGradient Q p.1.1 (incidenceParameter z p.2)
        let kp := fun p : (Euclidean n × Euclidean n) × ℝ ↦ p.1.2
        ContDiffOn ℝ ∞ Qp (T.incidenceDomain z) ∧
        ContDiffOn ℝ ∞ ξp (T.incidenceDomain z) ∧
        ContDiffOn ℝ ∞ kp (T.incidenceDomain z) ∧
        MapsTo Qp (closedBall a ρ) TQ ∧ MapsTo ξp (closedBall a ρ) Tξ ∧
        MapsTo kp (closedBall a ρ) Tk ∧
        cNorm (closedBall a ρ) 1 Qp + cNorm (closedBall a ρ) 1 ξp +
          cNorm (closedBall a ρ) 1 kp ≤ L ∧
        ∀ m,
          cNorm (closedBall a ρ) m Qp ≤ A m * (1 + cNorm K (m + 2) F) ∧
          cNorm (closedBall a ρ) m ξp ≤ B m * (1 + cNorm K (m + 4) F) ∧
          cNorm (closedBall a ρ) m kp ≤ D m := by
  obtain ⟨δ, L, TQ, Tξ, Tk, hδ, hδT, hL, hTQ, hTξ, hTk, hW, hlow⟩ :=
    T.exists_incidence_low_budgets hP a ρ z hKx hKz hKxO hKzO hKxframe
      (hball.trans hKU) hx hz
  obtain ⟨A, B, D, hA, hB, hD, hhigh⟩ := T.exists_projected_incidence_high_budgets
    (N := N) hP a ρ z hKx hKz hKxO hKzO hKxframe hx hz hK hKU hball C₀ hκmet hκ
  refine ⟨δ, L, hδT, TQ, Tξ, Tk, A, B, D, hδ, hL, hTQ, hTξ, hTk,
    hA, hB, hD, T.isOpen_incidenceDomain z, hW, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hclose.trans_le hδT⟩
  have hs := T.incidence_fields_smooth hP z Q
  obtain ⟨hQrange, hξrange, hkrange, hnorm⟩ := hlow Q hclose
  exact ⟨hs.1, hs.2.1, hs.2.2, hQrange, hξrange, hkrange, hnorm,
    hhigh F hF hi hrank hlowF hmet hnormal (hclose.trans_le hδT)⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
