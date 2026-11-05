module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Potential

/-!
# Instantiating the joint potential estimate

The consumer is `exists_uniform_coefficients`, which supplies the
low input budget and the adapted denominator gap from primitive frame
closeness. Every high bound here is proved for the literal current carrier
and projected stress, with fixed reserve five in `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open NullTransport.CoefficientBounds
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open ActualCarriers.ConstructedCarrierJets

/-- The actual potential, including the induced connection, has a joint
one-high estimate with reserve five. The two low coefficient inputs are
instantiated by `exists_uniform_coefficients` from the primitive closeness threshold and the existing carrier-center gap (`app:ch_waves:eq:joint-tame`). -/
theorem exists_projected_fullPotential_bound {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall a ρ ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κnormal L ε : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hL : 0 < L) (hε : 0 < ε) (r c : Fin n) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        cNorm (closedBall a ρ) 1 (fullInput T Q) ≤ L →
        (∀ w ∈ closedBall a ρ, ε ≤ |adaptedDenominator T Q r c w|) →
        ∀ m, cNorm (closedBall a ρ) m (transportPotential T Q F r c) ≤
          C m * (1 + cNorm K (m + 5) F) := by
  obtain ⟨A, hA, ha⟩ := exists_projected_fullInput_bound (N := N)
    T a ρ hx hc hK hKU hball C₀ hκmet hκnormal
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le
    (G := StressJet n N) (isCompact_closedBall a ρ) hK
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) (fun _ hw ↦ hball (hx hw))
  obtain ⟨E, hE, he⟩ := exists_full_potential_formula_bounds (N := N)
    a hρ T.data.adapted.normal r c hL hε hκmet (2 * C₀) (max 1 (κnormal ^ 2)⁻¹)
  refine ⟨fun m ↦ E m * (1 + A (m + 1) + 2 * D m),
    fun m ↦ mul_pos (hE m) (by have := hA (m + 1); have := hD m; positivity), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro hinput hgap m
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨hc hw, hKU (hball (hx hw))⟩
  have hFat : ∀ x ∈ K, ContDiffAt ℝ ∞ F x :=
    fun x hx ↦ hF.contDiffAt (hU.mem_nhds (hKU hx))
  have hJ := contDiffOn_stressJet hU hF
  have hjoint : ContDiffOn ℝ ∞ (stressJet F ∘ Prod.fst) (inputDomain T) :=
    hJ.comp contDiffOn_fst (fun _ hw ↦ hw.2)
  have hmap : MapsTo (stressJet F ∘ Prod.fst) (closedBall a ρ)
      (admissibleStressJets n N (2 * C₀) κmet (max 1 (κnormal ^ 2)⁻¹)) := by
    intro w hw
    exact stressJet_mem_admissibleStressJets hK hFat hκnormal hlowF (hball (hx hw))
      (hi _ (hKU (hball (hx hw)))) (hmet _ (hball (hx hw))) (hnormal _ (hball (hx hw)))
  have hout := he (inputDomain T) (isOpen_inputDomain T) hdom
    (fullInput T Q) (stressJet F ∘ Prod.fst) (smooth_fullInput T Q) hjoint
    hinput hgap hmap m
  have hid : cNorm (closedBall a ρ) m
      (fun w ↦ fullPotentialFormula T.data.adapted.normal r c
        (fullInput T Q w, fderiv ℝ (right c ∘ fullInput T Q) w, (stressJet F ∘ Prod.fst) w)) =
      cNorm (closedBall a ρ) m (transportPotential T Q F r c) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro w hw
    filter_upwards [(isOpen_inputDomain T).mem_nhds (hdom hw)] with y hy
    exact fullPotentialFormula_actual T Q hF r c hy
  rw [hid] at hout
  have hinputHigh := ha F hF hi hrank hlowF hmet hnormal hlow (m + 1)
  have hjetHigh := (hd (stressJet F)
    (fun x hx ↦ hJ.contDiffAt (hU.mem_nhds (hKU hx))) m).trans
      (mul_le_mul_of_nonneg_left (cNorm_stressJet_le hK hFat m) (hD m).le)
  have horder : cNorm K (m + 2) F ≤ cNorm K (m + 5) F := cNorm_mono_order (by omega)
  have hjbound : cNorm (closedBall a ρ) m (stressJet F ∘ Prod.fst) ≤
      2 * D m * cNorm K (m + 5) F := by
    calc
      _ ≤ D m * (2 * cNorm K (m + 2) F) := hjetHigh
      _ = (2 * D m) * cNorm K (m + 2) F := by ring
      _ ≤ (2 * D m) * cNorm K (m + 5) F :=
        mul_le_mul_of_nonneg_left horder (mul_nonneg (by norm_num) (hD m).le)
  have hinbound : cNorm (closedBall a ρ) (m + 1) (fullInput T Q) ≤
      A (m + 1) * (1 + cNorm K (m + 5) F) := by
    simpa only [show m + 1 + 4 = m + 5 by omega] using hinputHigh
  apply hout.trans
  have hinner : 1 + cNorm (closedBall a ρ) (m + 1) (fullInput T Q) +
      cNorm (closedBall a ρ) m (stressJet F ∘ Prod.fst) ≤
      (1 + A (m + 1) + 2 * D m) * (1 + cNorm K (m + 5) F) := by
    nlinarith [cNorm_nonneg K (m + 5) F, hD m]
  exact (mul_le_mul_of_nonneg_left hinner (hE m).le).trans_eq (by ring)

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
