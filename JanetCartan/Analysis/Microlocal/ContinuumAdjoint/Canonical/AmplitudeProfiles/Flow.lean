module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Flow.Cutoff
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Interpolation

/-!
# Global profiles of the literal unit-initial flow extension

The scalar tame theorem is applied with initial scalar exactly one. Its
coefficients, paired flow bounds, domain maps and regularity inputs are the
retained outputs of `NullTransport.exists_projected_local_positive_amplitude`.
The fixed support containment is supplied by
`exists_supportedChart_initialBuffer_cap` and `chartBump_tsupport_subset`:
the parent chooses `24a` below that cap before the immersion varies.

Consumer: `hflow` and `F₀` in
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow FlowAmplitude AmplitudeTame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Smoothness of the actual unit-initial extension follows from the scalar
regularity retained by the positive transport producer and containment of the
fixed cutoff in its domain (`app:ch_background:prop:bg-adjoint`). -/
theorem extendedFlowFactor_contDiff
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))} (hD : IsOpen D)
    (hs : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (tsupport (chartBump z₀ ha)) D)
    (hα : ContDiffOn ℝ ∞ (carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1))
      ((coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D)) :
    ContDiff ℝ ∞ (extendedFlowFactor T Q F row col Φ Y z₀ ha) := by
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let O := (C ∘ ψ) ⁻¹' D
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_fst.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  have hO : IsOpen O := hD.preimage (C.continuous.comp hψ.continuous)
  have hf : ContDiffOn ℝ ∞
      (fun p ↦ carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) (ψ p)) O :=
    hα.comp hψ.contDiffOn (fun _ hp ↦ hp)
  have hg : ContDiff ℝ ∞ (fun p ↦ chartBump z₀ ha p *
      carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) (ψ p)) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      ((chartBump z₀ ha).contDiff.contDiffOn.mul hf)
      (tsupport_mul_subset_left.trans hs)
  exact hg.comp (contDiff_snd.prodMk contDiff_fst)

/-- The same real extension is smooth as a complex-valued amplitude, exactly
as required by `hflow` in the literal adjoint consumer
(`app:ch_background:prop:bg-adjoint`). -/
theorem extendedFlowFactor_complex_contDiff
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))} (hD : IsOpen D)
    (hs : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (tsupport (chartBump z₀ ha)) D)
    (hα : ContDiffOn ℝ ∞ (carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1))
      ((coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D)) :
    ContDiff ℝ ∞ (fun p ↦ (extendedFlowFactor T Q F row col Φ Y z₀ ha p : ℂ)) :=
  Complex.ofRealLI.contDiff.comp
    (extendedFlowFactor_contDiff T Q F row col Φ Y z₀ ha hD hs hα)

/-- The exact unit-initial flow extension has the global `F₀` profile. The
fixed primitive low order is `2(n+1)+13`, independently of `s`; the only high
immersion norm has order `s+2(n+1)+13`. Every dominating common budget `H` is
allowed. The coefficient, paired flow, domain and scalar/null regularity
hypotheses are precisely retained by
`NullTransport.exists_projected_local_positive_amplitude`, specialized to
initial scalar one. The parent supplies the fixed support containment by
applying `exists_supportedChart_initialBuffer_cap` at `24a`; it also retains
the final common-budget instantiation. No flow-factor norm is an assumption.
Consumer: `hflow` and `F₀` of the literal adjoint endpoint
(`app:ch_background:prop:bg-adjoint`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_extendedFlowFactor_profile
    (K : Set (Euclidean n)) (z₀ : Euclidean 3) {ρ R τ a : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (ha : 0 < a) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) R)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    (A Hflow : ℕ → ℝ) (hA : ∀ j, 0 < A j) (hHflow : ∀ j, 0 < Hflow j)
    (hs : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (tsupport (chartBump z₀ ha))
      (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64)))
    (M : ℝ) (s : ℕ) :
    ∃ F₀ : ℕ → ℝ, (∀ i, 0 ≤ F₀ i) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
      let p₀ := ((0 : Euclidean (n - 1)), z₀)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let Bρ := closedBall ((0 : Euclidean n), z₀) ρ
      let α := carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)
      let b := fun w ↦ α w • carrierNullvector T Q col w
      IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) →
      (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
        ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) →
      (∀ j, cNorm Bρ j (carrierNullvector T Q col) +
        cNorm Bρ j (carrierConullvector T Q row) +
        cNorm Bρ j (carrierAdaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (carrierTransportDirection T Q row col) +
        cNorm Bρ j (carrierTransportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      (∀ j, cNorm J j Φ + cNorm J j Y ≤ Hflow j * (1 + cNorm K (j + 5) F)) →
      ContDiffOn ℝ ∞ α (C ⁻¹' D) → ContDiffOn ℝ ∞ b (C ⁻¹' D) →
      cNorm K (2*(n+1)+13) F ≤ M →
      ContDiff ℝ ∞ (extendedFlowFactor T Q F row col Φ Y z₀ ha) ∧
      ContDiff ℝ ∞ (fun p ↦ (extendedFlowFactor T Q F row col Φ Y z₀ ha p : ℂ)) ∧
      ∀ H : ℝ, 1 + cNorm K (s+2*(n+1)+13) F ≤ H →
        ∀ p : CarrierParameter × Euclidean n, ∀ i ≤ s+2*(n+1),
          ‖iteratedFDeriv ℝ i (extendedFlowFactor T Q F row col Φ Y z₀ ha) p‖ ≤
            F₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) ∧
          ‖iteratedFDeriv ℝ i (fun p ↦ (extendedFlowFactor T Q F row col Φ Y z₀ ha p : ℂ)) p‖ ≤
            F₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  let χ := chartBump (n := n) z₀ ha
  let L := tsupport χ
  have hL : IsCompact L := χ.hasCompactSupport
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  have hLW : MapsTo ψ L (C.symm ''
      (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64))) := by
    intro p hp
    exact ⟨C (ψ p), hs hp, C.symm_apply_apply (ψ p)⟩
  obtain ⟨Mα, _, B, hB, hb⟩ := CanonicalCarrier.exists_canonical_nullAmplitude_bounds T
    (N := N) K z₀ hρ hR hτ hτR hbuffer A Hflow hA hHflow hL hLW
    (le_max_right M 0) (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨r, hr, hsupport⟩ := (hL.image continuous_swap).isBounded.subset_closedBall_lt
    0 (0 : CarrierParameter × Euclidean n)
  let J₀ := closedBall (0 : CarrierParameter × Euclidean n) r
  obtain ⟨E, hE, he⟩ := exists_cNorm_chartCutoff_swap_le z₀ ha
    (isCompact_closedBall (0 : CarrierParameter × Euclidean n) r)
  let G := fun j ↦ 2 * E j * B j
  have hG j : 0 < G j := mul_pos (mul_pos (by norm_num) (hE j)) (hB j)
  let b₀ := 2*(n+1)
  obtain ⟨F₀, hF₀, hprofile⟩ := exists_closedBall_reserve_profile (F := ℝ)
    (0 : CarrierParameter × Euclidean n) hr b₀ s (G b₀ * (1+M)) (G (b₀+s))
  refine ⟨F₀, hF₀, ?_⟩
  intro Q F row col D Φ Y
  dsimp only
  intro hD hsmall hbig hΦD hYU hΦ hY hreg hcoeff hflow hα hbreg hFM
  let α := carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)
  let f := fun p ↦ α (ψ p)
  let O := (C ∘ ψ) ⁻¹' D
  let ext := extendedFlowFactor T Q F row col Φ Y z₀ ha
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_fst.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  have hO : IsOpen O := hD.preimage (C.continuous.comp hψ.continuous)
  have hLO : L ⊆ O := fun p hp ↦ hsmall ((workingCylinder_subsets _ hτ hR).1 (hs hp))
  have hf : ContDiffOn ℝ ∞ f O := hα.comp hψ.contDiffOn (fun _ hp ↦ hp)
  obtain ⟨hext, hcut⟩ := he f O hO hLO hf
  change ContDiff ℝ ∞ ext at hext
  have hcomplex : ContDiff ℝ ∞ (fun p ↦ (ext p : ℂ)) :=
    Complex.ofRealLI.contDiff.comp hext
  refine ⟨hext, hcomplex, ?_⟩
  have hFM₁₅ : cNorm K 15 F ≤ max M 0 :=
    ((cNorm_mono_order (by omega : 15 ≤ 2*(n+1)+13)).trans hFM).trans (le_max_left M 0)
  have hscalar := (hb Q F row col D Φ Y (fun _ ↦ 1) hD hsmall hbig hΦD hYU
    hΦ hY hreg hcoeff hflow contDiff_const.contDiffOn hα hbreg hFM₁₅
    (cNorm_unitInitial_le _ 15)).2
  have hbound (j) : cNorm J₀ j ext ≤ G j * (1 + cNorm K (j+13) F) := by
    have hb' : cNorm L j f ≤ B j * (1 + cNorm K (j+13) F + 1) := by
      have hh := (hscalar j).trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (cNorm_unitInitial_le _ (j+13))) (hB j).le)
      exact (le_add_of_nonneg_right (cNorm_nonneg L j
        (fun p ↦ α (ψ p) • carrierNullvector T Q col (ψ p)))).trans hh
    apply ((hcut j).trans (mul_le_mul_of_nonneg_left hb' (hE j).le)).trans
    dsimp only [G]
    nlinarith [mul_nonneg (mul_nonneg (hE j).le (hB j).le) (cNorm_nonneg K (j+13) F)]
  have hlow : cNorm J₀ b₀ ext ≤ G b₀ * (1+M) :=
    (hbound b₀).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hFM) (hG b₀).le)
  intro H hH p i hi
  have hH₁ : 1 ≤ H := (by linarith [cNorm_nonneg K (s+2*(n+1)+13) F])
  have hhigh : cNorm J₀ (b₀+s) ext ≤ G (b₀+s) * H := by
    apply (hbound (b₀+s)).trans
    apply mul_le_mul_of_nonneg_left _ (hG (b₀+s)).le
    simpa only [b₀, show 2*(n+1)+s+13 = s+2*(n+1)+13 by omega] using hH
  have hreal : ‖iteratedFDeriv ℝ i ext p‖ ≤
      F₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
    by_cases hp : p ∈ J₀
    · exact hprofile ext hext hlow H hH₁ hhigh i (by dsimp [b₀]; omega) p hp
    · have hnot : (p.2,p.1) ∉ L := fun hh ↦ hp (hsupport (mem_image_of_mem Prod.swap hh))
      have hzero : ext =ᶠ[𝓝 p] 0 := by
        have hh := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
          continuous_swap.continuousAt
        filter_upwards [hh] with q hq
        change χ (q.2,q.1) * flowFactor T Q F row col Φ Y q = 0
        rw [show χ (q.2,q.1) = 0 from hq, zero_mul]
      rw [(hzero.iteratedFDeriv ℝ i).eq_of_nhds]
      simpa only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero] using
        mul_nonneg (hF₀ i) (Real.rpow_nonneg (zero_le_one.trans hH₁) _)
  refine ⟨hreal, ?_⟩
  exact (Complex.ofRealLI.norm_iteratedFDeriv_comp_left hext.contDiffAt (by simp)).trans_le hreal

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
