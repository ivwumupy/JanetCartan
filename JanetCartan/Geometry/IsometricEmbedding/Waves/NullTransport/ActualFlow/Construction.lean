module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Footpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.LowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.BufferedFootpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.ActualEstimates

/-!
# Actual adapted null-characteristic flow and local footpoint chart

For `app:ch_waves:thm:leading`, construct both maps for the literal
`carrierTransportDirection T Q row col`. The adapted normal and section are
those of the SAME `PatchQuantitativeFamily`; the carrier labels are unchanged.

The analytic input is a low `C¹` bound for that named direction on a compact
working set inside the coefficient patch. Its producer is
`jc-null-coefficient-tame`. Smoothness is produced by
`exists_projected_null_coefficients`, including for the literal projected stress
frame with its constructed low-neighborhood witness.

The forward and inverse times and state buffers are explicit in that bound.
The backwards-flow chart covers a prescribed smaller product box. Finite
parameter coverage is assembled by `ActualFlow.FiniteCharts`. Both constructed
maps satisfy joint one-high estimates in the named direction's high norm.
No transport solution is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.ActualFlow
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Construct a smooth local flow and inverse footpoint map for the actual
normalized direction, from its low bound and a fixed geometric buffer. All
domain and inverse identities consumed by `PositiveTransport.FlowSolution`
are outputs. The zero section is the retained adapted section, and both maps
keep the carrier parameters unchanged (`app:ch_waves:thm:leading`).

The final radius is qualitative. This theorem does not yet assert uniform
inverse buffers or the manuscript's joint tame estimates. The parent must
instantiate the low bound with the actual coefficient estimate. -/
theorem exists_actual_local_flow_chart (row col : Fin n)
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {M : ℝ} (hM : 0 ≤ M)
    (hlow : cNorm K 1 (carrierTransportDirection T Q row col) ≤ M)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R : ℝ} (hR : 0 < R)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K) :
    ∃ δ > (0 : ℝ), ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        IsOpen D ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-δ) δ ×ˢ ball p₀ δ) ∧
        ContDiffOn ℝ ∞ Y D ∧
        D ⊆ (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-δ) δ ×ˢ ball p₀ δ) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-δ) δ ×ˢ ball p₀ δ) ∧
        (∀ p ∈ ball p₀ δ, Φ (0, p) = p) ∧
        (∀ p ∈ ball p₀ δ, ∀ t ∈ Ioo (-δ) δ, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ ball p₀ δ, ∀ t ∈ Ioo (-δ) δ, (Φ (t, p)).2 = p.2) ∧
        (∀ q ∈ D, (Y q).2 = q.2.2) ∧
        (∀ p ∈ ball p₀ δ, ∀ t ∈ Ioo (-δ) δ,
          HasDerivAt (fun s ↦ Φ (s, p))
            ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
              ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
                (t, Φ (t, p))))).2, 0) t) := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let L := liftedLowBound T M
  let ε := existenceTime R L
  have hL : 0 ≤ L := liftedLowBound_nonneg T hM
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε :=
    ⟨neg_neg_of_pos (existenceTime_pos hR hL), existenceTime_pos hR hL⟩
  have hbounds (q) (hq : q ∈ closedBall ((0 : ℝ), p₀) R) :=
    liftedDirection_low_bounds T Q row col hΩ hd hK hKΩ hM hlow (hbuffer hq)
  obtain ⟨_, _, _, _, _, _, Φ, _, hΦ, hi, _, hcarrier, hrange, hode⟩ :=
    exists_lifted_characteristics T Q row col hΩ hd hR hL
      (fun q hq ↦ hKΩ (hbuffer hq)) (fun q hq ↦ (hbounds q hq).1)
      (fun q hq ↦ (hbounds q hq).2)
  have hp₀ : p₀ ∈ ball p₀ (R / 2) := mem_ball_self (half_pos hR)
  obtain ⟨δ, hδ, D, Y, hsub, hD, heq, hY, hΦD, hYU, hYΦ, hΦY⟩ :=
    exists_local_footpoint_chart isOpen_Ioo isOpen_ball h0 hp₀ hΦ hi (hode p₀ hp₀ 0 h0)
  have hδ0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hp {p} (hp : p ∈ ball p₀ δ) : p ∈ ball p₀ (R / 2) :=
    (hsub (show ((0 : ℝ), p) ∈ Ioo (-δ) δ ×ˢ ball p₀ δ from ⟨hδ0, hp⟩)).2
  have ht {t} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-ε) ε :=
    (hsub (show (t, p₀) ∈ Ioo (-δ) δ ×ˢ ball p₀ δ from ⟨ht, mem_ball_self hδ⟩)).1
  refine ⟨δ, hδ, D, Φ, Y, hD, hΦ.mono hsub, hY, ?_, hΦD, hYU,
    (fun p h ↦ hi p (hp h)), hYΦ, hΦY, (fun p h t k ↦ hcarrier p (hp h) t (ht k)),
    ?_, (fun p h t k ↦ hode p (hp h) t (ht k))⟩
  · intro q hq
    rw [heq] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact hrange (hsub hs)
  · intro q hq
    have h := hcarrier (Y q) (hp (hYU hq).2) q.1 (ht (hYU hq).1)
    rw [hΦY q hq] at h
    exact h.symm

/-- Construct the actual null-characteristic flow and inverse on fixed buffers.
The inverse is the backwards trajectory, and the flow tube contains the
prescribed smaller product box. Every time and radius is determined by the
named direction's low `C¹` bound and the geometric state buffer; no continuity
shrink depending on higher derivatives is used (`app:ch_waves:thm:leading`).

The low-bound producer is `jc-null-coefficient-tame`. The parent must still
instantiate its compact coefficient-domain buffers and refine the parameter
cover. The joint bound is in the named direction's high norm; its constants
are constructed by `exists_actual_characteristics_cNorm_bound` before the
projected stress field. -/
theorem exists_actual_buffered_flow_chart (row col : Fin n)
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {M : ℝ} (hM : 0 ≤ M)
    (hlow : cNorm K 1 (carrierTransportDirection T Q row col) ≤ M)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R : ℝ} (hR : 0 < R)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K) :
    let τ := existenceTime R (liftedLowBound T M) / 4
    let I := Ioo (-τ) τ
    ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
    ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
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
          ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
            ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
              (t, Φ (t, p))))).2, 0) t) ∧
      ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧ ∀ k,
        cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k Φ +
          cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k Y ≤
          A k * (1 + cNorm K k (carrierTransportDirection T Q row col)) := by
  classical
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
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
    (fun p h t k ↦ hvelocity p (hp h) t (ht k)), ?_⟩
  · intro q hq
    rw [heq] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact hrange ⟨ht hs.1, hp hs.2⟩
  · intro q hq
    have h := hcarrier (footpointFromLift Ψ q) (hp (hYU hq).2) q.1 (ht (hYU hq).1)
    rw [hΦY q hq] at h
    exact h.symm
  · choose A hA hbound using fun k ↦ exists_actual_characteristics_cNorm_bound T p₀
      hR hM hΩ hK hKΩ hbuffer k
    refine ⟨A, hA, fun k ↦ hbound k Q row col hd hlow Ψ hΨ
      (fun q hq ↦ hi q (ball_subset_closedBall hq))
      (fun q hq t ht ↦ hode q (ball_subset_closedBall hq) t ht)
      (fun q hq t ht ↦ hr q (closedBall_subset_closedBall (by linarith) hq)
        t (Ioo_subset_Icc_self ht))⟩

end JanetCartan.NullTransport.ActualFlow
