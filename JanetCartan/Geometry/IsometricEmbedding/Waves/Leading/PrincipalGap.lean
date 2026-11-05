module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalGap.NormalOperator
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalGap.Carrier

/-!
# Positive principal-normal gaps for the actual carrier

This closes the lower-bound deduction in `app:ch_waves:thm:leading` for the
literal `PatchQuantitativeFamily.carrierGradient`, projected stress frame,
and `NullTransport.carrierNullvector`. The only transport input is a fixed
positive lower bound for its scalar amplitude, produced by `jc-null-transport`.

`exists_principal_gap_threshold` accepts any selected primitive minor, so it
can be applied to the exact refinement already used by transport. The final
existence theorem instantiates this minor with `exists_actual_nullvectors`.
Neither result constructs the scalar transport solution or proves the full
leading-wave theorem. All constants precede the current map and amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.LeadingWave
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ProjectedStressFrame AmbientResponse

/-- Fixed geometric data and a primitive cofactor gap imply the positive
principal-normal bound on the same buffered carrier domain. This adapter makes
no choice of minor or refinement: transport's existing row and column are
retained. The scalar lower bound `a₀` is the sole transport premise; the
gradient gap, column gap, frame basis, pencil-null identity and upper adjoint
bound are proved here (`app:ch_waves:thm:leading`). -/
theorem exists_principal_gap_threshold {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {μ a₀ : ℝ} (hμ : 0 < μ) (ha₀ : 0 < a₀) :
    ∃ δ cξ cν C : ℝ, 0 < δ ∧ 0 < cξ ∧ 0 < cν ∧ 0 < C ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
        ∀ z ∈ parameterCube (3 * P.radius / 2),
          cξ ≤ ‖T.carrierGradient Q x z‖ ∧
          ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C ∧
          ∀ r c, μ ≤ |(reducedSymbol (Q.1 x) (T.carrierGradient Q x z)).adjugate r c| →
            μ ≤ ‖carrierNullvector T Q c (x, z)‖ ∧
            ∀ α : ℝ, a₀ ≤ α →
              cν ≤ ‖principalNormal (canonicalNormalCompletion F x)
                (T.carrierGradient Q x z) (α • carrierNullvector T Q c (x, z))‖ := by
  obtain ⟨dξ, hdξ, cξ, hcξ, hξ⟩ := exists_buffered_carrierGradient_norm_lower hP T
  obtain ⟨ε, hε, γ, _hγ, hbasis⟩ := exists_projectedStress_basis_neighborhood hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let C : ℝ := 1 + 2 * n * |M|
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := min T.family.threshold (min dξ (ε / n))
  have hδ : 0 < δ := lt_min T.family.threshold_pos (lt_min hdξ (div_pos hε hnpos))
  refine ⟨δ, cξ, cξ * (a₀ * μ) / (2 * C), C, hδ, hcξ,
    div_pos (mul_pos hcξ (mul_pos ha₀ hμ)) (mul_pos (by norm_num) hC), hC, ?_⟩
  intro F hF hi hrank hM hclose
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hs : ∀ y ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) y := by
    intro y hy
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hlocal := (cNorm_mono_set_of_contDiffAt hball hK hs).trans_lt hclose
  have hlow := hlocal.trans_le (min_le_left T.family.threshold (min dξ (ε / n)))
  refine ⟨hlow, ?_⟩
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, hframe, hlow⟩
  change ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, _
  intro x hx hxK z hz
  have hFx : ContDiffAt ℝ 2 F x := (hF.contDiffAt (hU.mem_nhds (hKU hxK))).of_le (by simp)
  have hgrad : cξ ≤ ‖T.carrierGradient Q x z‖ :=
    hξ Q (hlocal.trans_le ((min_le_right _ _).trans (min_le_left _ _))) x hx z hz
  have hop : ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C := by
    apply (normalMapLinear_adjoint_norm_le_cNorm_four hK
      (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hxK).trans
    calc
      2 * n * cNorm K 4 F ≤ 2 * n * |M| :=
        mul_le_mul_of_nonneg_left (hM.trans (le_abs_self M)) (by positivity)
      _ ≤ C := by dsimp [C]; linarith
  have hpoint : ‖projectedStress F x - cubeStress n‖ < ε / n := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hxK (Nat.zero_le 6)
    have he : ‖projectedStress F x - cubeStress n‖ ≤
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact he.trans_lt (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
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
  refine ⟨hgrad, hop, ?_⟩
  intro r c hminor
  have hk : μ ≤ ‖carrierNullvector T Q c (x, z)‖ :=
    carrierNullvector_norm_lower_of_minor T Q (x, z) r c hminor
  refine ⟨hk, fun α hα ↦ ?_⟩
  have hαpos : 0 < α := ha₀.trans_le hα
  have hb : a₀ * μ ≤ ‖α • carrierNullvector T Q c (x, z)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
    exact mul_le_mul hα hk hμ.le hαpos.le
  have hchar := T.carrier_characteristic Q hx
    (fun i ↦ (hz i).trans_lt (by linarith [hP.1]))
  have hdet : (reducedSymbol (Q.1 x) (T.carrierGradient Q x z)).det = 0 := hchar
  have hnull : pencil (projectedStress F x) (T.carrierGradient Q x z) *ᵥ
      (fun j ↦ (α • carrierNullvector T Q c (x, z)) j) = 0 := by
    change reducedSymbol (Q.1 x) (T.carrierGradient Q x z) *ᵥ
      (α • rightNullvector (reducedSymbol (Q.1 x) (T.carrierGradient Q x z)) c) = 0
    rw [Matrix.mulVec_smul, mulVec_rightNullvector hdet, smul_zero]
  exact (principalNormal_norm_lower_of_pencil_null hFx (hrank x (hKU hxK)) hbas hnull
    hcξ (mul_pos ha₀ hμ) hC hgrad hb hop).2

/-- Instantiate the preceding deduction with the finite fixed-minor refinement
from `exists_actual_nullvectors` (and hence `exists_actual_null_gaps`). The
minor and adapted denominator bounds are retained alongside a common positive
lower bound for the actual gradient, cofactor column, and principal normal.
The projected frame, its basis and the normal-pairing upper bound are all
instantiated from the primitive geometric hypotheses. The parent supplies
`α ≥ a₀` from its actual transport construction on this same domain
(`app:ch_waves:thm:leading`). -/
theorem exists_actual_principal_gaps {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ δ μ κ g C : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧ 0 < g ∧ 0 < C ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
          (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
          (hrank : HasFullNormalRankOn F U),
          cNorm K 4 F ≤ M →
          cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
          ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
          ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
          ∀ z ∈ parameterCube (3 * P.radius / 2), ∀ r c, z ∈ V r c →
            μ ≤ |(reducedSymbol (Q.1 x) (T.carrierGradient Q x z)).adjugate r c| ∧
            pencil (projectedStress F x) (T.carrierGradient Q x z) *ᵥ
              (fun j ↦ carrierNullvector T Q c (x, z) j) = 0 ∧
            μ * κ ≤ |carrierAdaptedDenominator T Q r c (x, z)| ∧
            g ≤ ‖T.carrierGradient Q x z‖ ∧ g ≤ ‖carrierNullvector T Q c (x, z)‖ ∧
            ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤ C ∧
            ∀ α : ℝ, a₀ ≤ α →
              g ≤ ‖principalNormal (canonicalNormalCompletion F x)
                (T.carrierGradient Q x z) (α • carrierNullvector T Q c (x, z))‖ := by
  obtain ⟨δm, μ, κ, hδm, hμ, hκ, V, hV, hcover, hnull⟩ :=
    exists_actual_nullvectors (by omega : 2 ≤ n) hP T hK hKU hball
  obtain ⟨δp, cξ, cν, C, hδp, hcξ, hcν, hC, hprincipal⟩ :=
    exists_principal_gap_threshold hn hP T hK hKU hball M hμ ha₀
  refine ⟨min δm δp, μ, κ, min cξ (min μ cν), C,
    lt_min hδm hδp, hμ, hκ, lt_min hcξ (lt_min hμ hcν), hC, V, hV, hcover, ?_⟩
  intro F hF hi hrank hM hclose
  obtain ⟨hlow, hbound⟩ := hprincipal F hF hi hrank hM
    (hclose.trans_le (min_le_right _ _))
  refine ⟨hlow, ?_⟩
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  change ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, _
  intro x hx hxK z hz r c hzV
  have hsym (y) (hy : y ∈ U) (i) : (Q.1 y i).IsSymm :=
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds hy)).of_le (by simp)) (hrank y hy) i).1
  have hm := hnull Q (hclose.trans_le (min_le_left _ _)) hsym x hx hxK z hz r c hzV
  have hb := hbound x hx hxK z hz
  have hk := hb.2.2 r c hm.2.1
  refine ⟨hm.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.2.1,
    (min_le_left _ _).trans hb.1,
    ((min_le_right _ _).trans (min_le_left _ _)).trans hk.1, hb.2.1, ?_⟩
  intro α hα
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans (hk.2 α hα)

end JanetCartan.LeadingWave
