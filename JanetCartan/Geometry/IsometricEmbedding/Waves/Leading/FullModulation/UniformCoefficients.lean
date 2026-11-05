module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Smoothness
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.ActualPotential

/-!
# Uniform full-modulation coefficients for an existing selected minor

This extends the SAME coefficients and current Hamilton phase to independent
`(z,ζ)` parameters for `app:ch_waves:thm:leading`. The sole retained transport
input is the actual carrier denominator bound at `(0,z₀)`. Its producer is
`LeadingWave.exists_actual_local_leading_wave`: the returned gap holds at
that fixed center before the initial scalar is chosen.

The radius, primitive-frame threshold, gaps and all tame constants precede
the immersion and its high norms. Primitive phase continuity supplies the low
input budget. Every full-neighborhood gap, coefficient smoothness statement,
and reserve-five coefficient estimate is then proved for the literal objects.
The leading-wave parent retains the actual flow and final assembly obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open NullTransport.CoefficientBounds UniformCoefficients

/-- Extend the existing row and column to a uniform full-covector neighborhood.
The only carrier input is `g ≤ |carrierAdaptedDenominator ... (0,z₀)|`, with
`g > 0` fixed before the immersion. The actual local leading-wave constructor
produces precisely this bound. No full-covector gap, compact jet containment,
or coefficient estimate is assumed (`app:ch_waves:thm:leading`,
`app:ch_waves:eq:joint-tame`). -/
theorem exists_uniform_coefficients {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (row col : Fin n) (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius)
    {g : ℝ} (hg : 0 < g) :
    ∃ η ρ b B : ℝ, ∃ A : ℕ → ℝ,
      0 < η ∧ η ≤ T.family.threshold ∧ 0 < ρ ∧ 0 < b ∧ 0 < B ∧ (∀ m, 0 < A m) ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      IsOpen Ω ∧ closedBall a ρ ⊆ Ω ∧ closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        g ≤ |carrierAdaptedDenominator T Q row col (0, z₀)| →
        ContDiffOn ℝ ∞ (nullvector T Q col) Ω ∧
        ContDiffOn ℝ ∞ (conullvector T Q row) Ω ∧
        ContDiffOn ℝ ∞ (adaptedDenominator T Q row col) Ω ∧
        ContDiffOn ℝ ∞ (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) Ω ∧
        ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω ∧
        ContDiffOn ℝ ∞ (transportPotential T Q F row col) Ω ∧
        (∀ w ∈ closedBall a (2 * ρ),
          g / 2 ≤ |adaptedDenominator T Q row col w| ∧
          adaptedDenominator T Q row col w ≠ 0 ∧
          |(adaptedDenominator T Q row col w)⁻¹| ≤ (g / 2)⁻¹ ∧
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖conullvector T Q row w‖ ∧
          b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
          phaseGradient T Q w.1 w.2.2 ≠ 0 ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun j ↦ nullvector T Q col w j) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        cNorm (closedBall a ρ) 1 (transportDirection T Q row col) ≤ B ∧
        ∀ m,
          cNorm (closedBall a ρ) m (nullvector T Q col) +
          cNorm (closedBall a ρ) m (conullvector T Q row) +
          cNorm (closedBall a ρ) m (adaptedDenominator T Q row col) +
          cNorm (closedBall a ρ) m (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm (closedBall a ρ) m (transportDirection T Q row col) +
          cNorm (closedBall a ρ) m (transportPotential T Q F row col) ≤
            A m * (1 + cNorm K (m + 5) F) := by
  let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
    (0, (z₀, T.reference.spatialPatch z₀))
  obtain ⟨R, hR, hdomR, hxR⟩ := exists_carrier_center_ball T hP z₀ hz₀ hball
  have hx : MapsTo Prod.fst (closedBall a R)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) :=
    fun w hw ↦ ball_subset_closedBall (hxR hw).1
  obtain ⟨δ, ρ, L, b, hδ, hρ, hL, hb, hρR, hneigh⟩ :=
    exists_uniform_denominator_neighborhood T hn a hR hx (hball.trans hKU) hdomR row col hg
  have hbig : closedBall a (2 * ρ) ⊆ closedBall a R := closedBall_subset_closedBall hρR
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hdom : closedBall a ρ ⊆ domain T := hsmall.trans (hbig.trans hdomR)
  have hxsmall : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) :=
    fun w hw ↦ hx (hbig (hsmall hw))
  have hinputDomain : closedBall a (2 * ρ) ⊆ UniformCoefficients.inputDomain T :=
    fun w hw ↦ ⟨hdomR (hbig hw), hKU (hball (hx (hbig hw)))⟩
  obtain ⟨D, hD, hhigh⟩ := exists_projected_fullInput_bound (N := N)
    T a ρ hxsmall hdom hK hKU hball M hκmet hκnormal
  obtain ⟨B, A, hB, hA, hprincipal⟩ := exists_full_principal_formula_bounds
    a hρ T.data.adapted.normal row col hL (half_pos hg)
  obtain ⟨E, hE, hpotential⟩ := exists_projected_fullPotential_bound (N := N)
    T a hρ hxsmall hdom hK hKU hball M hκmet hκnormal hL (half_pos hg) row col
  refine ⟨min δ T.family.threshold, ρ, b, B, fun m ↦ A m * (1 + D m) + E m,
    lt_min hδ T.family.threshold_pos, min_le_right _ _, hρ, hb, hB,
    fun m ↦ add_pos (mul_pos (hA m) (by have := hD m; linarith)) (hE m), ?_⟩
  refine ⟨isOpen_ball, closedBall_subset_ball (by linarith), hbig.trans hdomR,
    fun w hw ↦ hxR (hbig hw), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hlocal : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < min δ T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt hclose
    intro x hxK
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hxK))).sub contDiffAt_const).of_le (by simp)
  have hlow := hlocal.trans_le (min_le_right _ _)
  refine ⟨hlow, ?_⟩
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F, hframe, hlow⟩
  change g ≤ |carrierAdaptedDenominator T Q row col (0, z₀)| → _
  intro hcenter
  obtain ⟨hlowInput, hgap⟩ := hneigh Q (hlocal.trans_le (min_le_left _ _)) hcenter
  have hlowWork : cNorm (closedBall a ρ) 1 (fullInput T Q) ≤ L :=
    (cNorm_mono_set_of_contDiffAt hsmall (isCompact_closedBall a (2 * ρ))
      (fun w hw ↦ ((smooth_fullInput T Q).contDiffAt
        ((UniformCoefficients.isOpen_inputDomain T).mem_nhds (hinputDomain hw))).of_le (by simp))).trans hlowInput
  have hnonzero (w) (hw : w ∈ closedBall a (2 * ρ)) : adaptedDenominator T Q row col w ≠ 0 :=
    abs_pos.mp ((half_pos hg).trans_le (hgap w hw).1)
  obtain ⟨hk, hl, hd, hinv, hdir, hpot⟩ := smooth_full_coefficients T Q hF hi row col
    isOpen_ball (ball_subset_closedBall.trans hinputDomain)
    (fun w hw ↦ hnonzero w (ball_subset_closedBall hw))
  obtain ⟨hlowDir, hprincipalBound⟩ := hprincipal
    (UniformCoefficients.inputDomain T) (UniformCoefficients.isOpen_inputDomain T)
    (hsmall.trans hinputDomain) (fullInput T Q) (smooth_fullInput T Q) hlowWork
    (fun w hw ↦ (hgap w (hsmall hw)).1)
  have hlowDir' : cNorm (closedBall a ρ) 1 (transportDirection T Q row col) ≤ B := by
    rw [transportDirection_eq_formula]
    exact hlowDir
  refine ⟨hk, hl, hd, hinv, hdir, hpot, ?_, hlowDir', ?_⟩
  · intro w hw
    obtain ⟨hdw, hkw, hlw, hξw⟩ := hgap w hw
    refine ⟨hdw, hnonzero w hw, ?_, hkw, hlw, hξw,
      norm_pos_iff.mp (hb.trans_le hkw), norm_pos_iff.mp (hb.trans_le hlw),
      norm_pos_iff.mp (hb.trans_le hξw), nullvector_relations T Q row col (hdomR (hbig hw))⟩
    simpa only [abs_inv, one_div] using one_div_le_one_div_of_le (half_pos hg) hdw
  · intro m
    have hh := hhigh F hF hi hrank hFM hmet hnormal hlow m
    have horder : cNorm K (m + 4) F ≤ cNorm K (m + 5) F := cNorm_mono_order (by omega)
    have hinner : 1 + cNorm (closedBall a ρ) m (fullInput T Q) ≤
        (1 + D m) * (1 + cNorm K (m + 5) F) := by
      have hbound := hh.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) horder) (hD m).le)
      nlinarith [cNorm_nonneg K (m + 5) F]
    have hprincipal' := (hprincipalBound m).trans
      (mul_le_mul_of_nonneg_left hinner (hA m).le)
    have hpotential' := hpotential F hF hi hrank hFM hmet hnormal hlow hlowWork
      (fun w hw ↦ (hgap w (hsmall hw)).1) m
    rw [nullvector_eq_formula, conullvector_eq_formula, adaptedDenominator_eq_formula,
      transportDirection_eq_formula]
    exact (add_le_add hprincipal' hpotential').trans_eq (by ring)

end JanetCartan.LeadingWave.FullModulation
