module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.HighBounds
set_option backward.isDefEq.respectTransparency false
/-!
# Uniform joint estimates for the literal null characteristics

The constants in `app:ch_waves:eq:joint-tame` are selected before the projected
stress field. Fixed coefficient-domain buffers and its low direction bound
control both the forward flow and the backwards footpoint map.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.NullTransport.ActualFlow
open ActualCarriers FrozenMenu CurrentFullPhase
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)

/-- Joint one-high estimates in the named physical direction, with constants
chosen before the projected stress field. `exists_actual_buffered_flow_chart`
supplies the SAME constructed flow, discharging every ODE premise. The
coefficient tame task produces only the named low/high direction bounds
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_actual_characteristics_cNorm_bound
    (p₀ : Euclidean (n - 1) × Euclidean 3) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω)
    (hm : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (row col : Fin n),
      ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω →
      cNorm K 1 (carrierTransportDirection T Q row col) ≤ M →
      ∀ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
        ℝ × (Euclidean (n - 1) × Euclidean 3),
      let ε := existenceTime R (liftedLowBound T M)
      ContDiffOn ℝ ∞ Ψ (ball (0, p₀) (R / 2) ×ˢ Ioo (-ε) ε) →
      (∀ q ∈ ball (0, p₀) (R / 2), Ψ (q, 0) = q) →
      (∀ q ∈ ball (0, p₀) (R / 2), ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s ↦ Ψ (q, s)) (liftedDirection T Q row col (Ψ (q, t))) t) →
      (∀ q ∈ closedBall (0, p₀) (R / 4), ∀ t ∈ Ioo (-ε) ε,
        Ψ (q, t) ∈ closedBall (0, p₀) R) →
      cNorm (Icc (-(ε / 4)) (ε / 4) ×ˢ closedBall p₀ (R / 8)) k (forwardFromLift Ψ) +
        cNorm (Icc (-(ε / 4)) (ε / 4) ×ˢ closedBall p₀ (R / 8)) k (footpointFromLift Ψ) ≤
        C * (1 + cNorm K k (carrierTransportDirection T Q row col)) := by
  let A := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let L := liftedLowBound T M
  let ε := existenceTime R L
  obtain ⟨B, hB, hb⟩ := exists_liftedDirection_cNorm_bound T p₀ R 1
  obtain ⟨H, hH, hh⟩ := exists_liftedDirection_cNorm_bound T p₀ R k
  have hL : 0 ≤ L := liftedLowBound_nonneg T hM
  have hε : 0 < ε := existenceTime_pos hR hL
  have hεR : ε ≤ R := (existenceTime_le hR hL).1.trans (by linarith)
  obtain ⟨C, hC, hc⟩ := exists_buffered_flow_cNorm_bound p₀ hR hε
    (show 0 ≤ B * (1 + M) by positivity) hεR (hΩ.preimage A.symm.continuous)
    (fun q hq ↦ hKΩ (hm hq)) k
  refine ⟨C * (1 + H), by positivity, ?_⟩
  intro Q row col hd hlow Ψ
  dsimp only
  intro hΨ hi hode hrange
  have h₁ := hb Q row col Ω K hΩ hd hK hKΩ hm
  have h₂ := hh Q row col Ω K hΩ hd hK hKΩ hm
  have hf := hc (liftedDirection T Q row col) Ψ
    (contDiffOn_liftedDirection T Q row col hd) hΨ
    (h₁.trans (mul_le_mul_of_nonneg_left (add_le_add_right hlow 1) hB.le))
    hi hode hrange
  apply hf.trans
  have hv := cNorm_nonneg K k (carrierTransportDirection T Q row col)
  have hhigh : 1 + cNorm (closedBall (0, p₀) R) k (liftedDirection T Q row col) ≤
      (1 + H) * (1 + cNorm K k (carrierTransportDirection T Q row col)) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hhigh hC.le).trans_eq (by ring)
end JanetCartan.NullTransport.ActualFlow
