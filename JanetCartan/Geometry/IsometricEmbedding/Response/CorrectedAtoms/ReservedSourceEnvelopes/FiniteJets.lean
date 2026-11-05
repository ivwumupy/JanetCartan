module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.SourceMatrixEnvelopes

/-!
# Finite joint jets of the original full-strain source

Apply the original output cutoff and the integer Fourier estimate using only
joint jets through the requested total order. An arbitrary monotone numerical
jet size is retained outside all constants, so derivative reserves and scalar
homogeneity can be supplied independently by the WKB producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
open ResponseTransfer ResponsePrimarySources ResponseSourceExtension Pseudodifferential
  RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

variable {n N : ℕ} {core chart : Set (Euclidean n)}
local notation "Par" => Euclidean 3 × Euclidean (n - 1)
local notation "Tensor" => Matrix (Fin n) (Fin n) ℂ

/-- Finite joint jet bounds produce the exact matrix Fourier source for the
same original full strain. Only orders at most `p+k` enter the bound; no
Sobolev embedding or derivative loss occurs. This is the common finite
conversion used by the reserved and homogeneous source producers for
`app:ch_response:eq:response-graded-source`.
-/
theorem exists_fullStrain_matrixFourier_bounds_of_joint_jets
    (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set Par} (hV : IsOpen V) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k p, 0 ≤ C k p) ∧
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
      ∀ k (v : Fin k → Par), (∀ j, ‖v j‖ ≤ 1) → ∀ c ∈ V,
      let f := fun x ↦ iteratedFDeriv ℝ k
        (fun b ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ b x) c v
      ∃ ua : PiLp 2 (fun _ : Fin n × Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
        (∀ ij, ua ij =ᵐ[volume] fun x ↦ f x ij.1 ij.2) ∧
        ∀ p : ℕ, MemMatrixFourierSobolev (p : ℝ) ua ∧
          matrixFourierSobolevNorm (p : ℝ) ua ≤ C k p * A (p + k) := by
  classical
  have hX (j : ℕ) : ∃ X : ℝ, 0 ≤ X ∧ ∀ x ∈ tsupport χ.toFun,
      ‖iteratedFDeriv ℝ j χ.toFun x‖ ≤ X := by
    obtain ⟨X, hX⟩ := χ.compact.exists_bound_of_continuousOn
      (χ.smooth.continuous_iteratedFDeriv (by simp)).continuousOn
    exact ⟨max 0 X, le_max_left _ _, fun x hx ↦ (hX x hx).trans (le_max_right _ _)⟩
  choose X hX hXbound using hX
  let J := fun k j ↦ ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * X i * B (j - i + k)
  have hJ (k j : ℕ) : 0 ≤ J k j := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hX i)) (hB _)
  let C := fun k p ↦ ((n * n : ℕ) : ℝ) * LowEnvelope.compactCoordinateSobolevConstant n p *
    Real.sqrt (volume.real (tsupport χ.toFun)) * ∑ j ∈ Finset.range (p + 1), J k j
  have hC (k p : ℕ) : 0 ≤ C k p := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (LowEnvelope.compactCoordinateSobolevConstant_pos n p).le)
        (Real.sqrt_nonneg _)) (Finset.sum_nonneg fun j _ ↦ hJ k j)
  refine ⟨C, hC, ?_⟩
  intro P U hU T Q F row col Φ Y r τ hspace hphase hF himm hrank hα hn A hA hmono hb
    k v hv c hc f
  let a := fullPrimaryStrainAmplitude T Q F row col Φ Y r τ
  have ha : ContDiffOn ℝ ∞ a (chart ×ˢ V) :=
    contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
      (hchart.prod hV) hspace hphase hF himm hrank hα hn
  let word := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ a (x, b)) c v
  obtain ⟨hword, hwordJet⟩ := primary_carrier_derivative_spatial_bounds hchart hV ha k v hv hc
  have hfEq : f = χ.zeroExtend (fun x : chart ↦ word x) := by
    exact primary_zeroExtend_carrier_derivative_eq χ hchart hV ha k v hc
  have hf : ContDiff ℝ ∞ f := by rw [hfEq]; exact χ.contDiff_zeroExtend_restrict hchart hword
  have hs : tsupport f ⊆ tsupport χ.toFun := by
    rw [hfEq]
    exact χ.tsupport_zeroExtend_subset _
  have hjet (p j : ℕ) (hj : j ≤ p) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j f x‖ ≤
        (∑ q ∈ Finset.range (p + 1), J k q) * A (p + k) := by
    have hJsum : J k j ≤ ∑ q ∈ Finset.range (p + 1), J k q :=
      Finset.single_le_sum (fun q _ ↦ hJ k q) (Finset.mem_range_succ_iff.mpr hj)
    apply le_trans (b := J k j * A (p + k)) ?_
      (mul_le_mul_of_nonneg_right hJsum (hA _))
    by_cases hx : x ∈ tsupport χ.toFun
    · have hxchart := χ.support_chart hx
      rw [hfEq, χ.zeroExtend_restrict]
      have ht := norm_iteratedFDerivWithin_smul_le χ.smooth.contDiffOn hword
        hchart.uniqueDiffOn hxchart (by simp : (j : ℕ∞ω) ≤ ∞)
      simp only [iteratedFDerivWithin_of_isOpen _ hchart hxchart] at ht
      apply ht.trans
      simp only [J, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hlocal := (hwordJet x hxchart (j - i)).trans (hb (x, c) ⟨hxchart, hc⟩ (j - i + k))
      have hlocal' := hlocal.trans
        (mul_le_mul_of_nonneg_left (hmono (by omega : j - i + k ≤ p + k)) (hB _))
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hXbound i x hx) (Nat.cast_nonneg _))
        hlocal' (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hX i))).trans_eq (by ring)
    · have hz : f =ᶠ[𝓝 x] 0 := by
        rw [hfEq, χ.zeroExtend_restrict]
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
      rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hJ k j) (hA _)
  let proj := fun ij : Fin n × Fin n ↦
    (EuclideanSpace.proj (finProdFinEquiv ij)).comp
      (SingleChannel.matrixChannelEquiv n n).toContinuousLinearEquiv.toContinuousLinearMap
  have hproj (ij : Fin n × Fin n) (z : Tensor) : proj ij z = z ij.1 ij.2 := by
    change z (finProdFinEquiv.symm (finProdFinEquiv ij)).1
      (finProdFinEquiv.symm (finProdFinEquiv ij)).2 = _
    rw [Equiv.symm_apply_apply]
  have hprojNorm (ij : Fin n × Fin n) : ‖(proj ij).restrictScalars ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    exact (PiLp.norm_apply_le (SingleChannel.matrixChannelEquiv n n z) _).trans_eq
      (by simp only [one_mul, LinearIsometryEquiv.norm_map])
  let g := fun ij : Fin n × Fin n ↦ proj ij ∘ f
  have hg (ij : Fin n × Fin n) : ContDiff ℝ ∞ (g ij) :=
    ((proj ij).restrictScalars ℝ).contDiff.comp hf
  have hgs (ij : Fin n × Fin n) : tsupport (g ij) ⊆ tsupport χ.toFun :=
    (tsupport_comp_subset (proj ij).map_zero f).trans hs
  have hgm (ij : Fin n × Fin n) : MemLp (g ij) 2 volume :=
    (hg ij).continuous.memLp_of_hasCompactSupport
      (χ.compact.of_isClosed_subset (isClosed_tsupport _) (hgs ij))
  let ua := WithLp.toLp 2 (fun ij : Fin n × Fin n ↦ (hgm ij).toLp (g ij))
  refine ⟨ua, ?_, ?_⟩
  · intro ij
    filter_upwards [(hgm ij).coeFn_toLp] with x hx
    exact hx.trans (hproj ij (f x))
  · intro p
    have hcomponents (ij : Fin n × Fin n) := LowEnvelope.exists_compactCoordinateSobolev p
      (g ij) (hg ij) χ.compact ((subset_tsupport _).trans (hgs ij))
      (mul_nonneg (Finset.sum_nonneg fun j _ ↦ hJ k j) (hA (p + k)))
      (fun α hα x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv (hg ij) α x).trans
        ((((proj ij).restrictScalars ℝ).norm_iteratedFDeriv_comp_left
          hf.contDiffAt (by simp)).trans
          ((mul_le_of_le_one_left (norm_nonneg _) (hprojNorm ij)).trans (hjet p α.length hα x))))
    have hmem (ij : Fin n × Fin n) : MemFourierSobolev (p : ℝ) (ua ij) := by
      obtain ⟨hm, hmem, _⟩ := hcomponents ij
      exact hmem
    refine ⟨hmem, ?_⟩
    apply (matrixFourierSobolevNorm_le_sum (p : ℝ) ua).trans
    calc
      _ ≤ ∑ _ij : Fin n × Fin n, LowEnvelope.compactCoordinateSobolevConstant n p *
          Real.sqrt (volume.real (tsupport χ.toFun)) *
            ((∑ j ∈ Finset.range (p + 1), J k j) * A (p + k)) := by
        apply Finset.sum_le_sum
        intro ij _
        obtain ⟨hm, _hmem, hnorm⟩ := hcomponents ij
        exact hnorm
      _ = C k p * A (p + k) := by simp [C]; ring

end JanetCartan.CorrectedAtoms.ReservedSourceEnvelopes
