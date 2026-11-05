module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.NormalGap

/-!
# Full-modulation thresholds before source-dependent geometry

The full leading-wave assembly in `main:prop:current-scale` must select a
source scale after the frame tolerance and before its geometric budgets.
The neighborhood and principal-formula producers already have this order;
we retain it through the actual six-coefficient estimates. The principal-normal
threshold likewise precedes the map budget and the positive amplitude gap.
Only high constants and the resulting normal lower bound depend on these
later quantities (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open NullTransport.CoefficientBounds LeadingWave LeadingWave.FullModulation AmbientResponse
open LeadingWave.FullModulation.UniformCoefficients

/-- `app:ch_waves:eq:joint-tame`, `main:prop:current-scale`: extend the existing
carrier minor to a fixed full-covector neighborhood before choosing the map
budget and separate geometric gaps. The threshold, radius, null/covector gaps
and direction C1 bound use only the fixed phase family and carrier center gap.
The latter comes from `exists_local_positive_amplitude_before_geometry`.
All six literal coefficient estimates are proved with reserve five. This is the
ordering input to the remaining full-modulation amplitude assembly. -/
theorem exists_full_modulation_coefficient_bounds_before_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (row col : Fin n) (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius)
    {g : ℝ} (hg : 0 < g) :
    ∃ η ρ b B : ℝ,
      0 < η ∧ η ≤ T.family.threshold ∧ 0 < ρ ∧ 0 < b ∧ 0 < B ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      IsOpen Ω ∧ closedBall a ρ ⊆ Ω ∧ closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      ∀ (M κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
      ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
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
  obtain ⟨B, A, hB, hA, hprincipal⟩ := exists_full_principal_formula_bounds
    a hρ T.data.adapted.normal row col hL (half_pos hg)
  refine ⟨min δ T.family.threshold, ρ, b, B,
    lt_min hδ T.family.threshold_pos, min_le_right _ _, hρ, hb, hB,
    isOpen_ball, closedBall_subset_ball (by linarith), hbig.trans hdomR,
    (fun w hw ↦ hxR (hbig hw)), ?_⟩
  intro M κmet κnormal hκmet hκnormal
  obtain ⟨D, hD, hhigh⟩ := exists_projected_fullInput_bound (N := N)
    T a ρ hxsmall hdom hK hKU hball M hκmet hκnormal
  obtain ⟨E, hE, hpotential⟩ := exists_projected_fullPotential_bound (N := N)
    T a hρ hxsmall hdom hK hKU hball M hκmet hκnormal hL (half_pos hg) row col
  refine ⟨fun m ↦ A m * (1 + D m) + E m,
    (fun m ↦ add_pos (mul_pos (hA m) (by have := hD m; linarith)) (hE m)), ?_⟩
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

/-- The principal-normal gap in `app:ch_waves:thm:leading` has a frame
threshold independent of both the low map budget and scalar positivity gap.
The projected-frame basis neighborhood alone fixes that threshold; the actual
normal-pairing bound then gives the positive lower bound. This prevents a
circular source-scale choice in the full-modulation history assembly. -/
theorem exists_full_modulation_normal_threshold_before_budgets {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    : ∃ δ > (0 : ℝ),
      ∀ M cξ cb : ℝ, 0 < cξ → 0 < cb →
      ∃ cν > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (_hF : ContDiffOn ℝ ∞ F U) (_hi : IsImmersionOn F U)
        (_hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ x ∈ K, ∀ ξ b : Euclidean n,
          pencil (projectedStress F x) ξ *ᵥ (fun j ↦ b j) = 0 →
          cξ ≤ ‖ξ‖ → cb ≤ ‖b‖ →
          cν ≤ ‖principalNormal (canonicalNormalCompletion F x) ξ b‖ := by
  obtain ⟨ε, hε, γ, _hγ, hbasis⟩ := exists_projectedStress_basis_neighborhood hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨ε / n, div_pos hε hnpos, ?_⟩
  intro M cξ cb hcξ hcb
  let C : ℝ := 1 + 2 * n * |M|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨cξ * cb / (2 * C),
    div_pos (mul_pos hcξ hcb) (mul_pos (by norm_num) hC), ?_⟩
  intro F hF hi hrank hFM hclose x hxK ξ b hnull hξ hb
  have hFx : ContDiffAt ℝ 2 F x := (hF.contDiffAt (hU.mem_nhds (hKU hxK))).of_le (by simp)
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hs : ∀ y ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) y :=
    fun y hy ↦ ((hframe.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hop : ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C := by
    apply (normalMapLinear_adjoint_norm_le_cNorm_four hK
      (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hxK).trans
    calc
      2 * n * cNorm K 4 F ≤ 2 * n * |M| :=
        mul_le_mul_of_nonneg_left (hFM.trans (le_abs_self M)) (by positivity)
      _ ≤ C := by dsimp [C]; linarith
  have hpoint : ‖projectedStress F x - cubeStress n‖ < ε / n := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hxK (Nat.zero_le 6)
    have he : ‖projectedStress F x - cubeStress n‖ ≤
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact he.trans_lt (hclose.trans_le (le_refl _))
  have hsum : (∑ i, ‖projectedStress F x i - cubeStress n i‖) < ε := by
    calc
      _ < ∑ _ : Fin n, ε / n := by
        apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        intro i _
        exact (norm_le_pi_norm (projectedStress F x - cubeStress n) i).trans_lt hpoint
      _ = ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hbas := (hbasis F x hFx (hi x (hKU hxK)) (hrank x (hKU hxK)) hsum).1
  exact (principalNormal_norm_lower_of_pencil_null hFx (hrank x (hKU hxK)) hbas hnull
    hcξ hcb hC hξ hb hop).2


end JanetCartan.CurrentCoefficientProfiles
