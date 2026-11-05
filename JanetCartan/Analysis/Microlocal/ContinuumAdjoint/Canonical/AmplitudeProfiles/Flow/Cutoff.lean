module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Definitions
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NullAmplitude
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Fixed multiplication for the unit-initial flow

The cutoff is fixed before the actual transport domain and flow vary. These
estimates feed the flow profile of `app:ch_background:prop:bg-adjoint`, with
the scalar tame estimate from `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers.ConstructedCarrierJets
open FullPhaseCharts.InverseEstimates

variable {n : ℕ}

/-- The constant initial scalar has every norm at most one, on the original
initial norm domain as well as its subsets. This discharges all initial-scalar
budgets for the flow factor in `app:ch_waves:eq:joint-tame`. -/
theorem cNorm_unitInitial_le (S : Set (Euclidean (n - 1) × Euclidean 3)) (j : ℕ) :
    cNorm S j (fun _ ↦ (1 : ℝ)) ≤ 1 := by
  induction j with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨p, _, rfl⟩; simp) zero_le_one
  | succ j ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun p : Euclidean (n - 1) × Euclidean 3 ↦
        ‖iteratedFDeriv ℝ (j+1) (fun _ ↦ (1 : ℝ)) p‖) '' S) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨p, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- Fixed chart multiplication and the literal coordinate swap preserve the
one-high bound. The local domain may vary; the constant uses only the fixed
cutoff and target compact set. Consumer: `exists_extendedFlowFactor_profile`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_cNorm_chartCutoff_swap_le (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {J : Set (CarrierParameter × Euclidean n)} (hJ : IsCompact J) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (f : Euclidean n × CarrierParameter → ℝ)
        (O : Set (Euclidean n × CarrierParameter)), IsOpen O →
        tsupport (chartBump (n := n) z₀ ha) ⊆ O → ContDiffOn ℝ ∞ f O →
        ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
          chartBump z₀ ha (p.2,p.1) * f (p.2,p.1)) ∧
        ∀ j, cNorm J j (fun p : CarrierParameter × Euclidean n ↦
          chartBump z₀ ha (p.2,p.1) * f (p.2,p.1)) ≤
          B j * cNorm (tsupport (chartBump z₀ ha)) j f := by
  let χ := chartBump (n := n) z₀ ha
  have hc : IsCompact (tsupport χ) := χ.hasCompactSupport
  let D := fun j ↦ (∑ k ∈ Finset.range (j+1),
    ‖(ContinuousLinearMap.mul ℝ ℝ)‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)) *
      cNorm (tsupport χ) j χ
  have hD j : 0 ≤ D j := mul_nonneg (Finset.sum_nonneg
    (fun _ _ ↦ mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ))
      (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)))) (cNorm_nonneg ..)
  obtain ⟨E, hE, he⟩ := exists_cNorm_fixed_pullback_le (G := ℝ)
    hJ (hJ.image continuous_swap)
    (fun _ _ ↦ (contDiff_snd.prodMk contDiff_fst).contDiffAt)
    (fun p hp ↦ mem_image_of_mem Prod.swap hp)
  refine ⟨fun j ↦ E j * (j+1 : ℝ) * (1+D j), fun j ↦ by
    have := hE j
    have := hD j
    positivity, ?_⟩
  intro f O hO hs hf
  let g := fun p ↦ χ p * f p
  have hg : ContDiff ℝ ∞ g :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      (χ.contDiff.contDiffOn.mul hf) ((tsupport_mul_subset_left).trans hs)
  refine ⟨hg.comp (contDiff_snd.prodMk contDiff_fst), ?_⟩
  intro j
  have hloc : cNorm (tsupport χ) j g ≤ D j * cNorm (tsupport χ) j f :=
    cNorm_bilinear_le_on (ContinuousLinearMap.mul ℝ ℝ) hc hO hs
      χ.contDiff.contDiffOn hf j
  have hglobal : cNorm (Prod.swap '' J) j g ≤
      (j+1 : ℝ) * cNorm (tsupport χ) j g := by
    apply (cNorm_le_sum_of_bounds
      (C := fun _ ↦ cNorm (tsupport χ) j g) (fun _ _ ↦ cNorm_nonneg ..) ?_).trans_eq
    · simp
    · intro k hk p _
      by_cases hp : p ∈ tsupport χ
      · exact norm_iteratedFDeriv_le_cNorm hc (hg.of_le (by simp)) hp hk
      · have hz : iteratedFDeriv ℝ k g p = 0 := by
          by_contra hn
          exact hp (tsupport_mul_subset_left (support_iteratedFDeriv_subset k hn))
        simpa only [hz, norm_zero] using cNorm_nonneg (tsupport χ) j g
  have hh := (he g (fun _ _ ↦ hg.contDiffAt) j).trans
    (mul_le_mul_of_nonneg_left (hglobal.trans
      (mul_le_mul_of_nonneg_left hloc (by positivity))) (hE j).le)
  apply hh.trans
  have hm : D j ≤ 1+D j := by linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hm (cNorm_nonneg (tsupport χ) j f))
    (mul_nonneg (hE j).le (by positivity : 0 ≤ (j+1 : ℝ)))

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
