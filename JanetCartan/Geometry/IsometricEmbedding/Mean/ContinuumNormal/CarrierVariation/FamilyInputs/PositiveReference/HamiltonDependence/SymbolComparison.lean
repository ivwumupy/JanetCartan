module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.StressPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds.Continuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Normalized Hamilton symbols at a positive reference

Consumer: the root/ODE/inverse comparison in
`FamilyInputs.PositiveReference.HamiltonDependence`, for
`app:lem:common-hamilton-phase` and `app:ch_osc:prop:osc-normal`, Step 4'.
The reference frame is allowed to vary in the physical variable. The actual
normalized determinant is compared, with no symbol-continuity premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ActualCarriers NormalizedSymbolBounds ConstructedCarrierJets
open HamiltonPhase.CompositionContinuity ProjectedStressFrame

/-- The literal normalized determinant depends continuously in every finite
norm on a nonconstant reference frame (`app:lem:common-hamilton-phase`). The
fixed state compact avoids the zero covector and projects into the fixed
physical compact. These are the actual Hamilton constructor's domains. -/
theorem exists_normalizedSymbol_sub_tolerance {n : ℕ}
    {K U : Set (Euclidean n)} {L : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hKU : K ⊆ U)
    (hLK : MapsTo Prod.fst L K) (hzero : ∀ z ∈ L, z.2 ≠ 0)
    {Q₀ : Euclidean n → Fin n → MetricTensor n} (hQ₀ : ContDiffOn ℝ ∞ Q₀ U)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiffOn ℝ ∞ Q U → cNorm K m (Q - Q₀) < δ →
      cNorm L m (normalizedSymbol Q - normalizedSymbol Q₀) < ε := by
  let M := cNorm K m Q₀
  let B := closedBall (0 : Fin n → MetricTensor n) (M + 1) ×ˢ (Prod.snd '' L)
  let f := fun p : (Fin n → MetricTensor n) × Euclidean n ↦
    determinant p.1 p.2 * ‖p.2‖ ^ (1 - (n : ℤ))
  let g₀ := fun z : Euclidean n × Euclidean n ↦ (Q₀ z.1, z.2)
  have hQ₀at : ∀ x ∈ K, ContDiffAt ℝ ∞ Q₀ x :=
    fun x hx ↦ hQ₀.contDiffAt (hU.mem_nhds (hKU hx))
  have hB : IsCompact B :=
    (isCompact_closedBall _ _).prod (hL.image continuous_snd)
  have hf : ∀ p ∈ B, ContDiffAt ℝ m f p := by
    intro p hp
    obtain ⟨z, hz, he⟩ := hp.2
    exact (contDiffAt_determinant_norm_zpow (he ▸ hzero z hz)).of_le (by simp)
  have hg₀ : ∀ z ∈ L, ContDiffAt ℝ m g₀ z := fun z hz ↦
    (((hQ₀at _ (hLK hz)).comp z contDiffAt_fst).prodMk contDiffAt_snd).of_le
      (by simp)
  have hbound₀ : ∀ x ∈ K, ‖Q₀ x‖ ≤ M := by
    intro x hx
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun x hx ↦ (hQ₀at x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hx (Nat.zero_le m)
  have hrange₀ : MapsTo g₀ L B := by
    intro z hz
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using
      (hbound₀ _ (hLK hz)).trans (by linarith : M ≤ M + 1), mem_image_of_mem _ hz⟩
  obtain ⟨d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt hL hB hf hg₀ hrange₀ hε
  obtain ⟨D, hD, hpull⟩ := exists_cNorm_fixed_pullback_le_jet_bound
    (G := (Fin n → MetricTensor n) × Euclidean n) hL
    (fun _ _ ↦ (contDiff_fst : ContDiff ℝ ∞
      (Prod.fst : Euclidean n × Euclidean n → Euclidean n)).contDiffAt) m
  refine ⟨min 1 (d / D), lt_min zero_lt_one (div_pos hd hD), ?_⟩
  intro Q hQ hsmall
  let g := fun z : Euclidean n × Euclidean n ↦ (Q z.1, z.2)
  have hQat : ∀ x ∈ K, ContDiffAt ℝ ∞ Q x :=
    fun x hx ↦ hQ.contDiffAt (hU.mem_nhds (hKU hx))
  have hg : ∀ z ∈ L, ContDiffAt ℝ m g z := fun z hz ↦
    (((hQat _ (hLK hz)).comp z contDiffAt_fst).prodMk contDiffAt_snd).of_le
      (by simp)
  have hrange : MapsTo g L B := by
    intro z hz
    refine ⟨?_, mem_image_of_mem _ hz⟩
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun x hx ↦ ((hQat x hx).sub (hQ₀at x hx)).of_le
        (by simp : (m : ℕ∞ω) ≤ ∞)) (hLK hz) (Nat.zero_le m)
    simp only [norm_iteratedFDeriv_zero] at hb
    change ‖Q z.1 - Q₀ z.1‖ ≤ cNorm K m (Q - Q₀) at hb
    have htri := norm_add_le (Q z.1 - Q₀ z.1) (Q₀ z.1)
    rw [sub_add_cancel] at htri
    have hs := hsmall.trans_le (min_le_left _ _)
    have hb₀ := hbound₀ _ (hLK hz)
    simpa only [mem_closedBall, dist_zero_right] using
      (show ‖Q z.1‖ ≤ M + 1 by linarith)
  let I : (Fin n → MetricTensor n) →L[ℝ]
      (Fin n → MetricTensor n) × Euclidean n := ContinuousLinearMap.inl ℝ _ _
  have hI : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [I]
  have hdiffat : ∀ x ∈ K, ContDiffAt ℝ ∞ (Q - Q₀) x :=
    fun x hx ↦ (hQat x hx).sub (hQ₀at x hx)
  have hp := hpull (I ∘ (Q - Q₀)) (cNorm K m (Q - Q₀)) (cNorm_nonneg ..)
    (fun z hz ↦ (I.contDiff.contDiffAt.comp _ (hdiffat _ (hLK hz))).of_le (by simp))
    (by
      intro j hj z hz
      calc
        _ ≤ ‖I‖ * ‖iteratedFDeriv ℝ j (Q - Q₀) z.1‖ :=
          I.norm_iteratedFDeriv_comp_left (hdiffat _ (hLK hz)) (by simp)
        _ ≤ 1 * ‖iteratedFDeriv ℝ j (Q - Q₀) z.1‖ :=
          mul_le_mul_of_nonneg_right hI (norm_nonneg _)
        _ ≤ _ := by
          rw [one_mul]
          exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun x hx ↦ (hdiffat x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) (hLK hz) hj)
  have he : g - g₀ = (I ∘ (Q - Q₀)) ∘ Prod.fst := by
    funext z
    simp [g, g₀, I, Function.comp_def]
  have hinner : cNorm L m (g - g₀) < d := by
    rw [he]
    exact hp.trans_lt ((lt_div_iff₀' hD).mp (hsmall.trans_le (min_le_right _ _)))
  simpa only [f, g, g₀, Function.comp_def, Pi.sub_def, normalizedSymbol,
    determinantNormalization] using hcomp f g hf hg hrange (by simpa using hd) hinner

/-- Primitive immersion closeness controls the SAME normalized Hamilton
symbol at any fixed admissible positive reference, with loss two. This is the
symbol input of `app:lem:common-hamilton-phase`, used in
`app:ch_background:prop:bg-frame`; the separate metric and normal gaps and
the original rank hypotheses are retained. -/
theorem exists_projected_normalizedSymbol_sub_tolerance {n N : ℕ}
    {K U : Set (Euclidean n)} {L : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hKU : K ⊆ U)
    (hLK : MapsTo Prod.fst L K) (hzero : ∀ z ∈ L, z.2 ≠ 0)
    {F₀ : Euclidean n → Euclidean N} (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U) (hrank₀ : HasFullNormalRankOn F₀ U)
    {C₀ κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm K 4 F₀ ≤ C₀)
    (hmet₀ : ∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ K, ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean N,
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 4 F ≤ C₀ →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm K (m + 2) (F - F₀) < δ →
      cNorm L m (normalizedSymbol (projectedStress F) -
        normalizedSymbol (projectedStress F₀)) < ε := by
  obtain ⟨d, hd, hs⟩ := exists_normalizedSymbol_sub_tolerance hK hL hU hKU hLK hzero
    (contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF₀ hi₀ hrank₀)) m hε
  obtain ⟨δ, hδ, hstress⟩ := exists_projectedStress_sub_tolerance hK hU hKU hF₀ hi₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ m hd
  refine ⟨δ, hδ, ?_⟩
  intro F hF hi hrank hlow hmet hnormal hsmall
  exact hs _ (contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank))
    (hstress F hF hi hlow hmet hnormal hsmall)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
