module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Phase
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Fixed-cutoff estimates for the actual affine extension

These bounds supply the primitive input to the graph and rational-field profiles
in `app:ch_background:prop:bg-adjoint`. The compact correction has a global
seminorm; the affine extension itself is estimated only on fixed compact sets.
All constants precede the varying immersion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow FullPhaseCharts.InverseEstimates
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ}

/-- Fixed multiplication by the cutoff bounds the compact correction globally.
Only jets on its closed support are used. Consumer: the affine graph and field
profiles in `app:ch_background:prop:bg-adjoint`. -/
theorem exists_cNorm_affineCorrection_le
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Y : Euclidean n × CarrierParameter → Euclidean (n - 1)),
        ContDiffOn ℝ ∞ Y O → ∀ m,
        cNorm univ m (fun p ↦ χ p • (Y p - A p.1)) ≤
          C m * (1 + cNorm (tsupport χ) m Y) := by
  let a := fun p : Euclidean n × CarrierParameter ↦ A p.1
  have ha : ContDiff ℝ ∞ a := A.contDiff.comp contDiff_fst
  let B := fun m ↦ (∑ j ∈ Finset.range (m + 1),
    ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclidean (n-1) →L[ℝ] Euclidean (n-1))‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm (tsupport χ) m χ
  have hB m : 0 ≤ B m := mul_nonneg (Finset.sum_nonneg
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))))
    (cNorm_nonneg ..)
  refine ⟨fun m ↦ (m + 1 : ℝ) * (1 + B m) * (1 + cNorm (tsupport χ) m a),
    fun m ↦ by
      have := hB m
      have := cNorm_nonneg (tsupport χ) m a
      positivity, ?_⟩
  intro Y hY m
  let f := fun p ↦ χ p • (Y p - A p.1)
  have hf : ContDiff ℝ ∞ f :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      (hχ.contDiffOn.smul (hY.sub ha.contDiffOn))
      ((tsupport_smul_subset_left χ _).trans hs)
  have hsub : cNorm (tsupport χ) m (Y - a) ≤
      cNorm (tsupport χ) m Y + cNorm (tsupport χ) m a := by
    simpa only [sub_eq_add_neg, cNorm_neg] using cNorm_add_le_of_contDiffAt (r := m) (f := Y) (g := -a) hc
      (fun p hp ↦ (hY.contDiffAt (hO.mem_nhds (hs hp))).of_le (by simp))
      (fun _ _ ↦ ha.neg.contDiffAt.of_le (by simp))
  have hloc : cNorm (tsupport χ) m f ≤ B m * cNorm (tsupport χ) m (Y - a) :=
    cNorm_bilinear_le_on (ContinuousLinearMap.lsmul ℝ ℝ) hc hO hs
      hχ.contDiffOn (hY.sub ha.contDiffOn) m
  have hglobal : cNorm univ m f ≤ (m + 1 : ℝ) * cNorm (tsupport χ) m f := by
    apply (cNorm_le_sum_of_bounds
      (C := fun _ ↦ cNorm (tsupport χ) m f) (fun _ _ ↦ cNorm_nonneg ..) ?_).trans_eq
    · simp
    · intro j hj p _
      by_cases hp : p ∈ tsupport χ
      · exact norm_iteratedFDeriv_le_cNorm hc (hf.of_le (by simp)) hp hj
      · have hz : iteratedFDeriv ℝ j f p = 0 := by
          by_contra hn
          exact hp ((tsupport_smul_subset_left χ _) (support_iteratedFDeriv_subset j hn))
        simpa only [hz, norm_zero] using cNorm_nonneg (tsupport χ) m f
  apply (hglobal.trans (mul_le_mul_of_nonneg_left
    (hloc.trans (mul_le_mul_of_nonneg_left hsub (hB m))) (by positivity))).trans
  have hy := cNorm_nonneg (tsupport χ) m Y
  have ha0 := cNorm_nonneg (tsupport χ) m a
  have hpoly : B m * (cNorm (tsupport χ) m Y + cNorm (tsupport χ) m a) ≤
      (1 + B m) * (1 + cNorm (tsupport χ) m a) * (1 + cNorm (tsupport χ) m Y) := by
    nlinarith [hB m, mul_nonneg (hB m) ha0, mul_nonneg ha0 hy,
      mul_nonneg (hB m) (mul_nonneg ha0 hy)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ (m+1 : ℝ))

/-- The unbounded affine extension has uniform seminorm bounds on every fixed
compact set. Its varying input is measured only on the cutoff support, which
lies inside the actual transport domain (`app:ch_background:eq:bg-mixed-input`). -/
theorem exists_cNorm_affineExtension_le
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {O L : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O) (hL : IsCompact L)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Y : Euclidean n × CarrierParameter → Euclidean (n - 1)),
        ContDiffOn ℝ ∞ Y O → ∀ m,
        cNorm L m (affineExtension A χ Y) ≤ C m * (1 + cNorm (tsupport χ) m Y) := by
  obtain ⟨B, hB, hb⟩ := exists_cNorm_affineCorrection_le A hO hχ hc hs
  let a := fun p : Euclidean n × CarrierParameter ↦ A p.1
  have ha : ContDiff ℝ ∞ a := A.contDiff.comp contDiff_fst
  refine ⟨fun m ↦ cNorm L m a + B m, fun m ↦ by
    linarith [cNorm_nonneg L m a, hB m], ?_⟩
  intro Y hY m
  let f := fun p ↦ χ p • (Y p - A p.1)
  have hf : ContDiff ℝ ∞ f :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      (hχ.contDiffOn.smul (hY.sub ha.contDiffOn))
      ((tsupport_smul_subset_left χ _).trans hs)
  have hmono : cNorm L m f ≤ cNorm univ m f := by
    apply cNorm_mono_set_of_bddAbove (subset_univ L)
    intro j hj
    refine ⟨cNorm (tsupport χ) m f, ?_⟩
    rintro _ ⟨p, _, rfl⟩
    by_cases hp : p ∈ tsupport χ
    · exact norm_iteratedFDeriv_le_cNorm hc (hf.of_le (by simp)) hp hj
    · have hz : iteratedFDeriv ℝ j f p = 0 := by
        by_contra hn
        exact hp ((tsupport_smul_subset_left χ _) (support_iteratedFDeriv_subset j hn))
      simpa only [hz, norm_zero] using cNorm_nonneg (tsupport χ) m f
  have hadd := cNorm_add_le hL (ha.of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    (hf.of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  change cNorm L m (affineExtension A χ Y) ≤ cNorm L m a + cNorm L m f at hadd
  have hh := hmono.trans (hb Y hY m)
  nlinarith [mul_nonneg (cNorm_nonneg L m a) (cNorm_nonneg (tsupport χ) m Y)]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The affine extension of the actual projected-stress transported position
has one high immersion norm, with loss four. No composite profile is assumed.
Consumer: both interpolation endpoints for `app:ch_background:prop:bg-adjoint`.
-/
theorem exists_projected_affineExtension_bound {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ extensionDomain T)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm L m (affineExtension A χ (CanonicalCarrier.transportPosition T Q)) ≤
          B m * (1 + cNorm K (m + 4) F) := by
  have hs' : tsupport χ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have hh := hs hp
    refine ⟨hh.1, fun i ↦ ?_⟩
    have hh' := hh.2 i
    linarith [hP.1]
  obtain ⟨B, hB, hb⟩ := CanonicalCarrier.exists_projected_transportPosition_bound
    T (N := N) hP hc hs' hK hKU hball C₀ hκmet hκ
  obtain ⟨D, hD, hd⟩ := exists_cNorm_affineExtension_le A
    (extensionDomain_open T) hL hχ hc hs
  refine ⟨fun m ↦ D m * (1 + B m), fun m ↦ mul_pos (hD m) (by linarith [hB m]), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  intro m
  have h := hb F hF hi hrank hFM hmet hnormal hlow m
  apply (hd _ (transportPosition_contDiffOn_extensionDomain T hP _) m).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hD m).le
  nlinarith [cNorm_nonneg K (m + 4) F]

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
