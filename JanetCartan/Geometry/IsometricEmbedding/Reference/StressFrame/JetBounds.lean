module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Jet

/-!
# Tame composition of the stress second jet

The analytic composition step of `app:ch_seed:eq:seed-frame-tame` on a
closed chart ball. Compactness of the admissible jet range is explicit here;
the final geometric estimate must obtain that range from the stipulated low
bound and the two singular-value gaps.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius JanetCartan.StressFrame

namespace JanetCartan.ProjectedStressFrame

/-- Each derivative of the second jet costs at most two derivatives of the
immersion (`app:ch_seed:eq:seed-frame-tame`). -/
theorem norm_iteratedFDeriv_stressJet_le {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} (hF : ContDiffAt ℝ ∞ F x)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (stressJet F) x‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) F x‖ + ‖iteratedFDeriv ℝ (j + 2) F x‖ := by
  have hd := hF.fderiv_right (show ∞ + 1 ≤ ∞ by simp)
  unfold stressJet
  rw [iteratedFDeriv_prodMk hd (hd.fderiv_right (by simp)) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  simp only [norm_iteratedFDeriv_fderiv]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- The actual sum-of-suprema seminorm of the second jet has precisely loss two
(`app:ch_seed:eq:seed-frame-tame`), for maps smooth near the compact domain. -/
theorem cNorm_stressJet_le {n N : ℕ} {F : Euclidean n → Euclidean N}
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hF : ∀ x ∈ K, ContDiffAt ℝ ∞ F x) (r : ℕ) :
    cNorm K r (stressJet F) ≤ 2 * cNorm K (r + 2) F := by
  have hb (j : ℕ) : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j F x‖) '' K) :=
    bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun x hx ↦ (hF x hx).of_le (by simp : (j : ℕ∞ω) ≤ ∞)) le_rfl
  have h := cNorm_le_sum_of_bounds (s := K) (r := r) (f := stressJet F)
    (C := fun j ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j + 1) F x‖) '' K) +
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j + 2) F x‖) '' K))
    (fun j _ ↦ add_nonneg (sSup_norm_iteratedFDeriv_nonneg K _ F)
      (sSup_norm_iteratedFDeriv_nonneg K _ F)) (by
      intro j _ x hx
      exact (norm_iteratedFDeriv_stressJet_le (hF x hx) j).trans
        (add_le_add (le_csSup (hb _) ⟨x, hx, rfl⟩) (le_csSup (hb _) ⟨x, hx, rfl⟩)))
  rw [Finset.sum_add_distrib] at h
  have h1 : (∑ j ∈ Finset.range (r + 1),
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j + 1) F x‖) '' K)) ≤ cNorm K (r + 2) F := by
    calc
      _ = cNorm K r (fderiv ℝ F) := by simp only [cNorm, norm_iteratedFDeriv_fderiv]
      _ ≤ cNorm K (r + 1) F := GeometricProfile.cNorm_fderiv_le K r F
      _ ≤ cNorm K (r + 2) F := cNorm_mono_order (by omega)
  have h2 : (∑ j ∈ Finset.range (r + 1),
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j + 2) F x‖) '' K)) ≤ cNorm K (r + 2) F := by
    calc
      _ = cNorm K r (fderiv ℝ (fderiv ℝ F)) := by
        simp only [cNorm, norm_iteratedFDeriv_fderiv]
      _ ≤ cNorm K (r + 1) (fderiv ℝ F) := GeometricProfile.cNorm_fderiv_le K r _
      _ ≤ cNorm K (r + 2) F := GeometricProfile.cNorm_fderiv_le K (r + 1) F
  linarith

/-- The stipulated `C⁴` bound controls the actual second jet pointwise
(`app:ch_seed:setup:seed-current`). -/
theorem norm_stressJet_le_cNorm_four {n N : ℕ} {F : Euclidean n → Euclidean N}
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hF : ∀ x ∈ K, ContDiffAt ℝ ∞ F x) {x : Euclidean n} (hx : x ∈ K) :
    ‖stressJet F x‖ ≤ 2 * cNorm K 4 F := by
  have h := norm_iteratedFDeriv_stressJet_le (hF x hx) 0
  rw [norm_iteratedFDeriv_zero] at h
  have h1 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun y hy ↦ (hF y hy).of_le (by simp : (4 : ℕ∞ω) ≤ ∞)) hx (by omega : 1 ≤ 4)
  have h2 := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun y hy ↦ (hF y hy).of_le (by simp : (4 : ℕ∞ω) ≤ ∞)) hx (by omega : 2 ≤ 4)
  linarith

/-- The second-jet coefficient has a linear high-norm bound with loss two on
any fixed compact admissible jet range (`app:ch_seed:eq:seed-frame-tame`). The
range and its unit conditions are inputs to this intermediate theorem, not
an assertion that the geometric low hypotheses have already supplied them. -/
theorem exists_cNorm_jetStress_le_tame_of_compact_range {n N : ℕ}
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (StressJet n N)} (ht : IsCompact t)
    (hg : ∀ J ∈ t, IsUnit (jetMetric J))
    (hA : ∀ J ∈ t, IsUnit (jetAmbient J))
    (Q : MetricTensor n) (r : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      Set.MapsTo (stressJet F) (Metric.closedBall a ρ) t →
      cNorm (Metric.closedBall a ρ) r (fun x ↦ jetStress Q (stressJet F x)) ≤
        C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) F) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
    a hρ ht (le_refl r)
    (fun J hJ ↦ (contDiffAt_jetStress (hg J hJ) (hA J hJ) Q).of_le (by simp))
  refine ⟨2 * C, by positivity, ?_⟩
  intro F hF hFt
  have h := hbound (stressJet F) (contDiff_stressJet hF) hFt
  have hjet := cNorm_stressJet_le (isCompact_closedBall a ρ)
    (fun _ _ ↦ hF.contDiffAt) r
  exact h.trans (by nlinarith)

end JanetCartan.ProjectedStressFrame
