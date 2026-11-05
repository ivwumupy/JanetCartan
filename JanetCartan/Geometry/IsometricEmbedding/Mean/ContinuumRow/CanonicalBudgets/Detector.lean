module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Inputs

/-!
# Primitive detector estimates for the canonical continuum row

The detector in `coefficientsOfCarrier_data` is the polynomial quadratic
contraction of the SAME projected stress and carrier gradient. Its low range
and high norms are derived from the existing primitive input estimates.
Consumer: `CoefficientNormCharts.Controls.reduced` in the global carrier
constructor; source: `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport.CoefficientBounds ActualCarriers.ConstructedCarrierJets

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Low and one-high detector bounds in the original carrier coordinates.
Both the Euclidean detector and the coefficient array with the finite-product
norm are estimated. The low range is obtained from primitive frame closeness,
and no detector or carrier-gradient estimate is assumed.
Source: `app:ch_background:eq:bg-mixed-input`, `bg-full-complex-amplitude`. -/
theorem exists_projected_quadratic_bounds {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ δ M : ℝ, ∃ A : ℕ → ℝ, 0 < δ ∧ 0 < M ∧ (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let q := fun w : Euclidean n × Euclidean 3 ↦
          quadratic (projectedStress F w.1) (T.carrierGradient Q w.1 w.2)
        (cNorm (closedBall a ρ) 1 q +
          cNorm (closedBall a ρ) 1 (fun w ↦ (q w).ofLp) ≤ M) ∧
        ∀ m, cNorm (closedBall a ρ) m q +
          cNorm (closedBall a ρ) m (fun w ↦ (q w).ofLp) ≤
            A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨δ, L, hδ, hL, hlo⟩ :=
    exists_actualInput_low_bound T hP a ρ hx (hball.trans hKU) hc
  obtain ⟨B, hB, hb⟩ :=
    exists_projected_actualInput_bound T hP a ρ hx hc hK hKU hball C₀ hκmet hκ
  let g : Input n → Euclidean n := fun p ↦ quadratic p.1 p.2
  let g' : Input n → Fin n → ℝ := fun p ↦ (quadratic p.1 p.2).ofLp
  have hg : ContDiff ℝ ∞ g := contDiff_quadratic
  have hg' : ContDiff ℝ ∞ g' := PiLp.contDiff_ofLp.comp hg
  choose C hC hcomp using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ
      (isCompact_closedBall (0 : Input n) L) (r := m) (k := m) le_rfl
      (g := g) (fun _ _ ↦ hg.contDiffAt.of_le (by simp))
  choose C' hC' hcomp' using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a hρ
      (isCompact_closedBall (0 : Input n) L) (r := m) (k := m) le_rfl
      (g := g') (fun _ _ ↦ hg'.contDiffAt.of_le (by simp))
  refine ⟨δ, (C 1 + C' 1) * (1 + L), fun m ↦ (C m + C' m) * (1 + B m),
    hδ, by have := hC 1; have := hC' 1; positivity,
    fun m ↦ by have := hC m; have := hC' m; have := hB m; positivity, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hKU (hball (hx hw)), (hc hw).1⟩, (hc hw).2⟩
  have hs := smooth_actualInput T hP Q
  have hlowInput := hlo Q hclose
  have hmap : MapsTo (actualInput T Q) (closedBall a ρ) (closedBall (0 : Input n) L) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hn := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hs.contDiffAt ((isOpen_inputDomain T).mem_nhds (hdom hy))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
    have hv : ‖actualInput T Q w‖ ≤ cNorm (closedBall a ρ) 1 (actualInput T Q) := by
      simpa only [norm_iteratedFDeriv_zero] using hn
    exact hv.trans hlowInput
  have hq (m) := add_le_add
    (hcomp m (inputDomain T) (isOpen_inputDomain T) hdom (actualInput T Q) hs hmap)
    (hcomp' m (inputDomain T) (isOpen_inputDomain T) hdom (actualInput T Q) hs hmap)
  constructor
  · exact (hq 1).trans (by
      have := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlowInput)
        (add_pos (hC 1) (hC' 1)).le
      nlinarith)
  · intro m
    apply (hq m).trans
    have hh := hb F hF hi hrank hFM hmet hnormal hlow m
    have hf0 := cNorm_nonneg K (m + 4) F
    have hh' : 1 + cNorm (closedBall a ρ) m (actualInput T Q) ≤
        (1 + B m) * (1 + cNorm K (m + 4) F) := by nlinarith
    have := mul_le_mul_of_nonneg_left hh' (add_pos (hC m) (hC' m)).le
    nlinarith

/-- Smoothness of the literal detector on the canonical physical/carrier
domain. This is the regularity field needed by the primitive norm charts
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem quadratic_canonical_smooth {c C : ℝ} (hP : P.IsValid c C)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)))
      ((U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
        (parameter ⁻¹' parameterInterior (2 * P.radius))) := by
  have hψ : ContDiff ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) :=
    contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hf := (smooth_actualInput T hP Q).comp hψ.contDiffOn
    (s := (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius))) (fun _ hp ↦ hp)
  exact contDiff_quadratic.comp_contDiffOn hf

/-- The actual detector and the exact reduced coefficient array have uniform
low bounds and loss-four one-high estimates in the original `(s,v)` variables.
The only additional input is containment of their fixed compact domain in the
coefficient construction ball. Constants precede the immersion.
Consumer: `coefficientsOfCarrier_data` and `CoefficientNormCharts.Controls.reduced`;
source: `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_projected_canonical_quadratic_bounds {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLa : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      L (closedBall a ρ))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ δ M : ℝ, ∃ A : ℕ → ℝ, 0 < δ ∧ 0 < M ∧ (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let q := fun p : Euclidean n × CarrierParameter ↦
          quadratic (projectedStress F p.1) (T.carrierGradient Q p.1 (parameter p.2))
        (cNorm L 1 q + cNorm L 1 (fun p ↦ (q p).ofLp) ≤ M) ∧
        ∀ m, cNorm L m q + cNorm L m (fun p ↦ (q p).ofLp) ≤
          A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨δ, M, A, hδ, hM, hA, hb⟩ :=
    exists_projected_quadratic_bounds T hP a hρ hx hc hK hKU hball C₀ hκmet hκ
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL (isCompact_closedBall a ρ) (fun _ _ ↦ hψ.contDiffAt) hLa
  obtain ⟨D', hD', hd'⟩ := exists_cNorm_fixed_pullback_le (G := Fin n → ℝ)
    hL (isCompact_closedBall a ρ) (fun _ _ ↦ hψ.contDiffAt) hLa
  refine ⟨δ, (D 1 + D' 1) * M, fun m ↦ (D m + D' m) * A m,
    hδ, mul_pos (add_pos (hD 1) (hD' 1)) hM,
    fun m ↦ mul_pos (add_pos (hD m) (hD' m)) (hA m), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let q := fun w : Euclidean n × Euclidean 3 ↦
    quadratic (projectedStress F w.1) (T.carrierGradient Q w.1 w.2)
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hKU (hball (hx hw)), (hc hw).1⟩, (hc hw).2⟩
  have hs : ContDiffOn ℝ ∞ q (inputDomain T) :=
    contDiff_quadratic.comp_contDiffOn (smooth_actualInput T hP Q)
  have hs' : ContDiffOn ℝ ∞ (fun w ↦ (q w).ofLp) (inputDomain T) :=
    PiLp.contDiff_ofLp.comp_contDiffOn hs
  have hbound (m) : cNorm L m (q ∘ ψ) + cNorm L m ((fun w ↦ (q w).ofLp) ∘ ψ) ≤
      (D m + D' m) * (cNorm (closedBall a ρ) m q +
        cNorm (closedBall a ρ) m (fun w ↦ (q w).ofLp)) := by
    have h₁ := hd q (fun w hw ↦ hs.contDiffAt ((isOpen_inputDomain T).mem_nhds (hdom hw))) m
    have h₂ := hd' (fun w ↦ (q w).ofLp)
      (fun w hw ↦ hs'.contDiffAt ((isOpen_inputDomain T).mem_nhds (hdom hw))) m
    have h₃ := mul_nonneg (hD m).le (cNorm_nonneg (closedBall a ρ) m (fun w ↦ (q w).ofLp))
    have h₄ := mul_nonneg (hD' m).le (cNorm_nonneg (closedBall a ρ) m q)
    nlinarith
  obtain ⟨hlowq, hhighq⟩ := hb F hF hi hrank hFM hmet hnormal hclose hlow
  constructor
  · exact (hbound 1).trans (mul_le_mul_of_nonneg_left hlowq (add_pos (hD 1) (hD' 1)).le)
  · intro m
    exact (hbound m).trans ((mul_le_mul_of_nonneg_left (hhighq m)
      (add_pos (hD m) (hD' m)).le).trans_eq (by ring))

end JanetCartan.ContinuumRow.CanonicalCarrier
