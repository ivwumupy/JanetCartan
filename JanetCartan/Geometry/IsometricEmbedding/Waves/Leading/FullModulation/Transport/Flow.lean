module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.FlowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Characteristics

/-!
# Uniform constants for the constructed adapted flow

Retain the quantifier order of `exists_actual_characteristics_cNorm_bound`
when assembling the actual charts. The constants here precede the frame and
hence all high immersion norms (`app:ch_waves:eq:joint-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase

/-- The actual buffered flow and inverse with a single sequence of one-high
constants fixed before the varying frame. This is the uniform form consumed by
`FullModulation.exists_positive_amplitude` (`app:ch_waves:eq:joint-tame`). -/
theorem exists_uniform_actual_flow_chart {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {M : ℝ} (hM : 0 ≤ M)
    {p₀ : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))} {R : ℝ} (hR : 0 < R)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K) :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧ ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (row col : Fin n),
      ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω →
      cNorm K 1 (transportDirection T Q row col) ≤ M →
    let τ := existenceTime R (liftedLowBound T M) / 4
    let I := Ioo (-τ) τ
    ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
    ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) → Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
      0 < τ ∧ IsOpen D ∧
      I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
      D = (fun q ↦ (q.1, Φ q)) '' (I ×ˢ ball p₀ (R / 8)) ∧
      ContDiffOn ℝ ∞ Φ (I ×ˢ ball p₀ (R / 8)) ∧
      ContDiffOn ℝ ∞ Y (I ×ˢ ball p₀ (R / 4)) ∧
      D ⊆ (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω ∧
      MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ ball p₀ (R / 8)) D ∧
      MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ ball p₀ (R / 8)) ∧
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) ∧
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ I, (Φ (t, p)).2 = p.2) ∧
      (∀ q ∈ D, (Y q).2 = q.2.2) ∧
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ I,
        HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted (transportDirection T Q row col
            ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
              (t, Φ (t, p))))).2, 0) t) ∧
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
      ∀ k,
        cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k Φ +
          cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k Y ≤
          A k * (1 + cNorm K k (transportDirection T Q row col)) := by
  classical
  choose A hA hbound using fun k ↦ exists_actual_characteristics_cNorm_bound T p₀
    hR hM hΩ hK hKΩ hbuffer k
  refine ⟨A, hA, ?_⟩
  intro Q row col hd hlow
  let C := FlowAmplitude.coordinates (Z := (Euclidean 3 × Euclidean (n - 1))) (adaptedCoordinates T.data.adapted)
  let L := liftedLowBound T M
  let ε := existenceTime R L
  have hL : 0 ≤ L := liftedLowBound_nonneg T hM
  have hε : 0 < ε := existenceTime_pos hR hL
  have hbounds (q) (hq : q ∈ closedBall ((0 : ℝ), p₀) R) :=
    liftedDirection_low_bounds T Q row col hΩ hd hK hKΩ hM hlow (hbuffer hq)
  obtain ⟨Ψ, hΨ, hi, hode, hr, _, Φ, hΦeq, _, _, _, hcarrier, hrange, hvelocity⟩ :=
    exists_lifted_characteristics T Q row col hΩ hd hR hL
      (fun q hq ↦ hKΩ (hbuffer hq)) (fun q hq ↦ (hbounds q hq).1)
      (fun q hq ↦ (hbounds q hq).2)
  have hlift := contDiffOn_liftedDirection T Q row col hd
  have hlip : LipschitzOnWith ⟨L, hL⟩ (liftedDirection T Q row col)
      (closedBall (0, p₀) R) :=
    (convex_closedBall (0, p₀) R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq ↦ (hlift.contDiffAt
        ((hΩ.preimage C.symm.continuous).mem_nhds (hKΩ (hbuffer hq)))).differentiableAt
          (by simp)) (fun q hq ↦ by exact_mod_cast (hbounds q hq).2)
  obtain ⟨D, hD, hsmall, hbig, heq, hΦ, hY, hΦD, hYU, hinit, hYΦ, hΦY⟩ :=
    buffered_footpoint_chart hR hL (fun _ ↦ rfl) hlip (fun q hq ↦ (hbounds q hq).1)
      hΨ hi hode (fun q hq t ht ↦ hr q hq t (Ioo_subset_Icc_self ht))
  have hp {p} (hp : p ∈ ball p₀ (R / 8)) : p ∈ ball p₀ (R / 2) :=
    ball_subset_ball (by linarith) hp
  have ht {t : ℝ} (ht : t ∈ Ioo (-(ε / 4)) (ε / 4)) : t ∈ Ioo (-ε) ε := by
    constructor <;> linarith [ht.1, ht.2]
  have heΦ : Φ = forwardFromLift Ψ := hΦeq
  rw [heΦ] at hcarrier hrange hvelocity
  refine ⟨D, forwardFromLift Ψ, footpointFromLift Ψ, by change 0 < ε / 4; positivity,
    hD, hsmall, hbig, heq, hΦ, hY, ?_, hΦD, hYU, hinit, hYΦ, hΦY,
    (fun p h t k ↦ hcarrier p (hp h) t (ht k)), ?_,
    (fun p h t k ↦ hvelocity p (hp h) t (ht k)), ?_, ?_, ?_⟩
  · intro q hq
    rw [heq] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact hrange ⟨ht hs.1, hp hs.2⟩
  · intro q hq
    have h := hcarrier (footpointFromLift Ψ q) (hp (hYU hq).2) q.1 (ht (hYU hq).1)
    rw [hΦY q hq] at h
    exact h.symm
  · apply hΨ.snd.comp
      ((contDiffOn_const.prodMk contDiffOn_snd).prodMk contDiffOn_fst)
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    constructor
    · have hp' : p ∈ ball p₀ (R / 2) := ball_subset_ball (by linarith) hp
      simpa using hp'
    · change -(2 * (ε / 4)) < t ∧ t < 2 * (ε / 4) at ht
      constructor <;> linarith [ht.1, ht.2]
  · apply hΨ.snd.comp (contDiffOn_id.prodMk contDiffOn_fst.neg)
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    change -(2 * (ε / 4)) < t ∧ t < 2 * (ε / 4) at ht
    change (t, p) ∈ ball (0, p₀) (R / 2) ∧ -t ∈ Ioo (-ε) ε
    constructor
    · rw [mem_ball, Prod.dist_eq, max_lt_iff]
      have hεR := (existenceTime_le hR hL).1
      change ε ≤ R / 4 at hεR
      refine ⟨?_, (mem_ball.mp hp).trans (by linarith)⟩
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    · constructor <;> linarith [ht.1, ht.2]
  · exact fun k ↦ hbound k Q row col hd hlow Ψ hΨ
      (fun q hq ↦ hi q (ball_subset_closedBall hq))
      (fun q hq t ht ↦ hode q (ball_subset_closedBall hq) t ht)
      (fun q hq t ht ↦ hr q (closedBall_subset_closedBall (by linarith) hq)
        t (Ioo_subset_Icc_self ht))

end JanetCartan.LeadingWave.FullModulation
