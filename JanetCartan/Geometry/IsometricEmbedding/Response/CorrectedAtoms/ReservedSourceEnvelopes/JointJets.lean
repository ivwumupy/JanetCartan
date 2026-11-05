module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReservedSourceEnvelopes.FiniteJets

/-!
# Joint jets of the same cutoff full-strain source

Retain the joint physical/carrier derivatives before Fourier conversion.
This supplies the source factor in the classical reconstruction of the same
fixed response, with the same derivative reserve and scalar size.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
open ResponsePrimarySources ResponseSourceExtension RawPrimary NullTransport
  ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

variable {n N : ℕ} {core chart : Set (Euclidean n)}
local notation "Par" => Euclidean 3 × Euclidean (n - 1)

/-- The original cutoff full-strain source retains its actual joint jet size
at the same derivative order. The constant precedes the amplitude and size;
no source or reconstruction norm is assumed. Consumer: the source factor in
the classical reconstruction of `fullPrimaryResponse`
(`app:ch_response:eq:response-graded-source`). -/
theorem exists_fullStrain_cutoff_joint_bounds
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set Par} (hV : IsOpen V) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
    ∀ {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
      (T : PatchQuantitativeFamily P U hU)
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (F : Euclidean n → Euclidean N) (row col : Fin n)
      (Φ Y : ℝ × (Euclidean (n - 1) × Par) → Euclidean (n - 1) × Par)
      (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ),
      (∀ w ∈ chart ×ˢ V, w.1 ∈ U) →
      (∀ w ∈ chart ×ˢ V, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) (chart ×ˢ V) →
      (∀ w ∈ chart ×ˢ V, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      ∀ A : ℕ → ℝ, (∀ m, 0 ≤ A m) → Monotone A →
      (∀ w ∈ chart ×ˢ V, ∀ m : ℕ,
        ‖iteratedFDeriv ℝ m (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) w‖ ≤
          B m * A m) →
      let f := fun w : Euclidean n × Par ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1
      ContDiffOn ℝ ∞ f (univ ×ˢ V) ∧
        ∀ m w, w.2 ∈ V → ‖iteratedFDeriv ℝ m f w‖ ≤ C m * A m := by
  classical
  have hX (j : ℕ) : ∃ X : ℝ, 0 ≤ X ∧ ∀ x ∈ tsupport χ.toFun,
      ‖iteratedFDeriv ℝ j χ.toFun x‖ ≤ X := by
    obtain ⟨X, hX⟩ := χ.compact.exists_bound_of_continuousOn
      (χ.smooth.continuous_iteratedFDeriv (by simp)).continuousOn
    exact ⟨max 0 X, le_max_left _ _, fun x hx ↦ (hX x hx).trans (le_max_right _ _)⟩
  choose X hX hXbound using hX
  let C := fun m ↦ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * X i * B (m - i)
  have hC (m : ℕ) : 0 ≤ C m := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hX i)) (hB _)
  refine ⟨C, hC, ?_⟩
  intro P U hU T Q F row col Φ Y r τ hspace hphase hF hi hrank hα hn A hA hmono hb f
  let a := fullPrimaryStrainAmplitude T Q F row col Φ Y r τ
  have ha : ContDiffOn ℝ ∞ a (chart ×ˢ V) :=
    contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
      (hchart.prod hV) hspace hphase hF hi hrank hα hn
  have heq : f = fun w : Euclidean n × Par ↦ χ.toFun w.1 • a w := by
    funext w
    exact congrFun (fullStrainEnvelope_eq T Q F row col Φ Y r χ τ w.2) w.1
  have hzero (w : Euclidean n × Par) (hw : w.1 ∉ tsupport χ.toFun) : f =ᶠ[𝓝 w] 0 := by
    filter_upwards [((isClosed_tsupport χ.toFun).isOpen_compl.preimage continuous_fst).mem_nhds hw]
      with y hy
    rw [heq]
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul, Pi.zero_apply]
  have hcutoff (j : ℕ) (w : Euclidean n × Par) (hw : w.1 ∈ tsupport χ.toFun) :
      ‖iteratedFDeriv ℝ j (fun y : Euclidean n × Par ↦ χ.toFun y.1) w‖ ≤ X j := by
    let π := ContinuousLinearMap.fst ℝ (Euclidean n) Par
    change ‖iteratedFDeriv ℝ j (χ.toFun ∘ π) w‖ ≤ X j
    rw [π.iteratedFDeriv_comp_right χ.smooth w (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    have hπ : ‖π‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (by intro y; change ‖y.1‖ ≤ 1 * ‖y‖; simpa only [one_mul] using norm_fst_le y)
    apply le_trans (b := ‖iteratedFDeriv ℝ j χ.toFun w.1‖) ?_ (hXbound j w.1 hw)
    change ‖iteratedFDeriv ℝ j χ.toFun w.1‖ * (∏ _i : Fin j, ‖π‖) ≤
      ‖iteratedFDeriv ℝ j χ.toFun w.1‖
    simpa using mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ j χ.toFun w.1))
      (pow_le_one₀ (norm_nonneg π) hπ)
  constructor
  · intro w hw
    by_cases hx : w.1 ∈ tsupport χ.toFun
    · rw [heq]
      exact (((χ.smooth.comp contDiff_fst).contDiffAt).smul
        (ha.contDiffAt ((hchart.prod hV).mem_nhds ⟨χ.support_chart hx, hw.2⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero w hx)).contDiffWithinAt
  · intro m w hw
    by_cases hx : w.1 ∈ tsupport χ.toFun
    · rw [heq]
      have hw' : w ∈ chart ×ˢ V := ⟨χ.support_chart hx, hw⟩
      have ht := norm_iteratedFDerivWithin_smul_le (χ.smooth.comp contDiff_fst).contDiffOn ha
        (hchart.prod hV).uniqueDiffOn hw' (by simp : (m : ℕ∞ω) ≤ ∞)
      simp only [iteratedFDerivWithin_of_isOpen _ (hchart.prod hV) hw'] at ht
      apply ht.trans
      simp only [C, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hraw := (hb w hw' (m - i)).trans
        (mul_le_mul_of_nonneg_left (hmono (Nat.sub_le m i)) (hB _))
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hcutoff i w hx) (Nat.cast_nonneg _))
        hraw (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hX i))).trans_eq (by ring)
    · rw [((hzero w hx).iteratedFDeriv ℝ m).self_of_nhds]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hC m) (hA m)

end JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
