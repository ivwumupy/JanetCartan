module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Flow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.PositiveBound
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.TameBounds

/-! # Constructing full-modulation positive transport from coefficient budgets

For `app:ch_waves:thm:leading` and `app:ch_waves:eq:joint-tame`, the producer
`jc-leading-full-modulation-coefficients` supplies the named coefficient bounds
on a fixed physical ball and smoothness on its open enlargement. This module
constructs the actual flow, footpoint and literal scalar from those inputs.
All radii, time, lower bound and tame constants precede `F` and `r`.

This conditional coefficient-to-construction theorem is consumed by
`jc-leading-wave`; that parent must instantiate the coefficient producer and
assemble the finite cover. It is not the unconditional leading-wave theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude

/-- A nonzero adapted denominator forces both selected nullvectors to be
nonzero (`app:ch_waves:thm:leading`). -/
theorem nullvectors_ne_zero_of_denominator {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (row col : Fin n) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    (hd : adaptedDenominator T Q row col w ≠ 0) :
    nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 := by
  have heq : adaptedDenominator T Q row col w =
      ∑ a, transportField (Q.1 w.1) (conullvector T Q row w)
        (fun j ↦ nullvector T Q col w j) a * T.data.adapted.normal a := by
    simp only [adaptedDenominator, adaptedTimeCoefficient, nullvector, conullvector, PiLp.toLp_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  constructor
  · intro hk
    apply hd
    rw [heq]
    simp [hk, transportField, Matrix.mulVec, dotProduct]
  · intro hl
    apply hd
    rw [heq]
    simp [hl, transportField]

/-- Actual positive full-parameter transport with reserve thirteen, from the
six named coefficient budgets. The parameter is the independent pair `(z,ζ)`;
the initial datum is the ORIGINAL `r(y,z)`. The explicit lower bound and every
constant are chosen before the frame, immersion and datum. The final leading
wave assembler must supply these coefficient hypotheses from its actual
projected frame (`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_positive_amplitude {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (K : Set (Euclidean n)) (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hΩ : IsOpen Ω)
    (hball : closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ ⊆ Ω)
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    {M₁₂ Mᵣ m : ℝ} (hM₁₂ : 0 ≤ M₁₂) (hMᵣ : 0 ≤ Mᵣ) (hm : 0 < m) :
    ∃ R τ g : ℝ, ∃ H B : ℕ → ℝ,
      0 < R ∧ 0 < τ ∧ 0 < g ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧
      τ ≤ R / 16 ∧
      g = m * Real.exp (-(A 0 * (1 + M₁₂)) * τ) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R)
        (closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n),
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ContDiffOn ℝ ∞ (nullvector T Q col) Ω →
      ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω →
      ContDiffOn ℝ ∞ (transportPotential T Q F row col) Ω →
      (∀ w ∈ Ω, adaptedDenominator T Q row col w ≠ 0) →
      (∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm) →
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      (∀ j, cNorm Bρ j (nullvector T Q col) +
        cNorm Bρ j (conullvector T Q row) +
        cNorm Bρ j (adaptedDenominator T Q row col) +
        cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
        cNorm Bρ j (transportDirection T Q row col) +
        cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) →
      cNorm K 12 F ≤ M₁₂ →
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) := by
  let z := (z₀, T.reference.spatialPatch z₀)
  let p₀ := ((0 : Euclidean (n - 1)), z)
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  let Bρ := closedBall ((0 : Euclidean n), z) ρ
  obtain ⟨R, hR, hbuffer⟩ := exists_adapted_buffer T z₀ hρ
  let M := A 1 * (1 + M₁₂)
  have hM : 0 ≤ M := mul_nonneg (hA 1).le (by linarith)
  let τ := existenceTime R (liftedLowBound T M) / 4
  have hτ : 0 < τ := div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hM)) (by norm_num)
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hM)).1
    dsimp [τ]
    linarith
  obtain ⟨H₀, hH₀, hflow⟩ := exists_uniform_actual_flow_chart T hΩ
    (isCompact_closedBall _ _) hball hM hR hbuffer
  let H := fun j ↦ H₀ j * (1 + A j)
  have hH (j) : 0 < H j := mul_pos (hH₀ j) (by linarith [hA j])
  obtain ⟨B, hB, htame⟩ := exists_scalarAmplitude_joint_tame (N := N) T K z
    hρ hR hτ hτR hbuffer A H hA hH hM₁₂ hMᵣ
  let g := m * Real.exp (-(A 0 * (1 + M₁₂)) * τ)
  have hg : 0 < g := mul_pos hm (Real.exp_pos _)
  refine ⟨R, τ, g, H, B, hR, hτ, hg, hH, hB, hτR, rfl, hbuffer, ?_⟩
  intro Q F row col
  dsimp only
  intro hk hd hc hden hsym hphase hcoeff hFlow
  have hdir (j) : cNorm Bρ j (transportDirection T Q row col) ≤
      A j * (1 + cNorm K (j + 5) F) := by
    have hh := hcoeff j
    linarith [cNorm_nonneg Bρ j (nullvector T Q col),
      cNorm_nonneg Bρ j (conullvector T Q row),
      cNorm_nonneg Bρ j (adaptedDenominator T Q row col),
      cNorm_nonneg Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg Bρ j (transportPotential T Q F row col)]
  have hdirLow : cNorm Bρ 1 (transportDirection T Q row col) ≤ M :=
    (hdir 1).trans (mul_le_mul_of_nonneg_left
      (add_le_add_right ((cNorm_mono_order (by omega : 1 + 5 ≤ 12)).trans hFlow) 1) (hA 1).le)
  obtain ⟨D, Φ, Y, _, hD, hsmall, hbig, _, hΦ, hY, hdomain, hΦD, hYU,
      hinit, hYΦ, hΦY, hcarrier, hYcarrier, hvelocity, hΦbuffer, hYbuffer, hflowHigh⟩ :=
    hflow Q row col hd hdirLow
  have hphys : C ⁻¹' D ⊆ Ω := by
    intro w hw
    have hh := hdomain hw
    change C.symm (C w) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hY' := hY.mono hbig
  have hhigh (j) :
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) j Φ +
        cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) j Y ≤
          H j * (1 + cNorm K (j + 5) F) := by
    apply (hflowHigh j).trans
    have hh : 1 + cNorm Bρ j (transportDirection T Q row col) ≤
        (1 + A j) * (1 + cNorm K (j + 5) F) := by
      have := hdir j
      nlinarith [cNorm_nonneg K (j + 5) F]
    exact (mul_le_mul_of_nonneg_left hh (hH₀ j).le).trans_eq (by dsimp [H]; ring)
  have hballDomain : MapsTo C.symm D Bρ := by
    intro q hq
    apply hbuffer
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have hh := hbig hq
    constructor
    · simpa only [Real.dist_eq, sub_zero] using
        (abs_le.mpr ⟨hh.1.1.le, hh.1.2.le⟩).trans (show τ ≤ R by linarith)
    · exact (mem_ball.mp hh.2).le.trans (by linarith)
  have hpotBound (w) (hw : w ∈ C ⁻¹' D) :
      |transportPotential T Q F row col w| ≤ A 0 * (1 + M₁₂) := by
    have hmem : w ∈ Bρ := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hballDomain hw
    have hb : |transportPotential T Q F row col w| ≤
        cNorm Bρ 0 (transportPotential T Q F row col) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
          (fun q hq ↦ (hc.contDiffAt (hΩ.mem_nhds (hball hq))).of_le
            (show (0 : ℕ∞ω) ≤ ∞ by simp)) hmem (Nat.zero_le 0)
    have hh := hcoeff 0
    have hlo : cNorm K (0 + 5) F ≤ M₁₂ := (cNorm_mono_order (by omega)).trans hFlow
    have hm' := mul_le_mul_of_nonneg_left (add_le_add_right hlo 1) (hA 0).le
    linarith [cNorm_nonneg Bρ 0 (nullvector T Q col),
      cNorm_nonneg Bρ 0 (conullvector T Q row),
      cNorm_nonneg Bρ 0 (adaptedDenominator T Q row col),
      cNorm_nonneg Bρ 0 (fun w ↦ (adaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg Bρ 0 (transportDirection T Q row col)]
  refine ⟨D, Φ, Y, hD, hsmall, hbig, hphys, hΦ, hY', hΦD, hYU,
    hinit, hYΦ, hΦY, ?_, ?_, hvelocity, hΦbuffer, hYbuffer, hhigh, ?_⟩
  · intro p hp t ht
    exact ⟨congrArg Prod.fst (hcarrier p hp t ht), congrArg Prod.snd (hcarrier p hp t ht)⟩
  · intro q hq
    exact ⟨congrArg Prod.fst (hYcarrier q hq), congrArg Prod.snd (hYcarrier q hq)⟩
  · intro r hr hrLow hrmin
    have hproj : initialProjection '' ball p₀ (R / 8) ⊆
        ball ((0 : Euclidean (n - 1)), z₀) (R / 8) := by
      rintro _ ⟨p, hp, rfl⟩
      exact initialProjection_mapsTo_ball p₀ (R / 8) hp
    have hr' : ContDiffOn ℝ ∞ r (initialProjection '' ball p₀ (R / 8)) :=
      hr.mono (hproj.trans (ball_subset_ball (by linarith)))
    have hrpos : ∀ p ∈ initialProjection '' ball p₀ (R / 8), 0 < r p :=
      fun p hp ↦ hm.trans_le (hrmin p (hproj hp))
    obtain ⟨hα, hαk, hinitial, hpos, _, hpde, hsymbol, hreduce⟩ :=
      scalarAmplitude_spec T Q F row col isOpen_Ioo ordConnected_Ioo isOpen_ball hD
        ⟨neg_neg_of_pos hτ, hτ⟩ (hk.mono hphys) (hc.mono hphys)
        (fun w hw ↦ hsym w (hphys hw)) (fun w hw ↦ hden w (hphys hw))
        (fun w hw ↦ hphase w (hphys hw)) hr' hrpos hΦ hΦD hinit hY' hYU hYΦ hΦY hvelocity
    refine ⟨hα, hαk, hinitial, ?_, hpde, hsymbol, hreduce, ?_⟩
    · intro w hw
      have hne := nullvectors_ne_zero_of_denominator T Q row col w (hden w (hphys hw))
      refine ⟨?_, hpos w hw, hne.1, hne.2, smul_ne_zero (hpos w hw).ne' hne.1⟩
      exact scalarAmplitude_lower_bound T Q F row col hτ
        (mul_nonneg (hA 0).le (by linarith)) hm.le hΦD hYU hpotBound
        (fun p hp ↦ hrmin p (hproj hp)) hw
    · exact htame Q F row col D Φ Y r hsmall hbig hΦD hYU hΦbuffer hYbuffer
        (fun w hw ↦ ⟨hk.contDiffAt (hΩ.mem_nhds (hball hw)),
          hd.contDiffAt (hΩ.mem_nhds (hball hw)), hc.contDiffAt (hΩ.mem_nhds (hball hw))⟩)
        hcoeff hhigh hr hFlow hrLow

end JanetCartan.LeadingWave.FullModulation
