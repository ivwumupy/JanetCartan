module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.CompletionBounds.LowFrequency

/-!
# Fixed-cutoff estimates on the working annulus

The constants here depend only on the fixed cutoff and the bounded output
frequency interval. The primitive assembly in `CompletionBounds` supplies both
amplitude bounds used in the intermediate Leibniz estimate.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Finite joint jets of the fixed completion cutoff have a uniform constant
on every bounded frequency region, independently of physical positions.
Consumed by the smoothing estimate after `app:ch_background:eq:bg-symbol`. -/
theorem exists_completionCutoff_joint_jet_bound (R : ℝ) (s : ℕ) :
    ∃ A > 0, ∀ p : Variables n, ‖p.2.2‖ ≤ R → ∀ k ≤ s,
      ‖iteratedFDeriv ℝ k (fun q : Variables n ↦ completionCutoff q.2.2) p‖ ≤ A := by
  let L : Variables n →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))
  let A := cNorm (closedBall (0 : Euclidean n) R) s (completionCutoff (n := n))
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  refine ⟨A + 1, by positivity, ?_⟩
  intro p hp k hk
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (by
    intro q
    change ‖q.2.2‖ ≤ 1 * ‖q‖
    simpa only [one_mul] using (norm_snd_le q.2).trans (norm_snd_le q))
  change ‖iteratedFDeriv ℝ k (completionCutoff ∘ L) p‖ ≤ _
  rw [L.iteratedFDeriv_comp_right completionCutoff_contDiff p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k completionCutoff (L p)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k completionCutoff (L p)‖ * ∏ _ : Fin k, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg L)
        (fun _ _ ↦ hL)) (norm_nonneg _)
    _ ≤ A + 1 := by
      simp only [Finset.prod_const_one, mul_one]
      have hp' : L p ∈ closedBall (0 : Euclidean n) R := by
        change dist p.2.2 0 ≤ R
        simpa only [dist_zero_right] using hp
      have hf : ContDiff ℝ (s : ℕ∞ω) (completionCutoff (n := n)) :=
        completionCutoff_contDiff.of_le (by simp)
      exact (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) hf hp' hk).trans
        (le_add_of_nonneg_right zero_le_one)

/-- Local smoothness of the literal spectator amplitude from the relative
support buffer. Used on the fixed annulus in the estimate following
`app:ch_background:eq:bg-symbol`. -/
theorem amplitude_contDiffOn_of_relative_buffer
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {U Z : Set (InputVariables n)}
    {R : Set (Variables n)} (hΩ : IsOpen Ω) (hR : IsOpen R)
    (hreg : PrimitiveRegularity d J U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω U)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hsupp : ∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
      d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → d.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    (hbuffer : closure (F '' Z) ∩ (R ×ˢ univ) ⊆ Ω)
    {S : Set (Euclidean 2)} (hS : IsCompact S) :
    ContDiffOn ℝ ∞ (amplitude d J u Ω S) R := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact contDiffOn_compactParameterIntegral hR isOpen_univ hS (subset_univ S)
    (extendedDensity_contDiffOn_of_relative_buffer d J u F hΩ hreg hu hmap hright hsupp hbuffer)

/-- The local Leibniz step in the bounded-frequency smoothing estimate.
Both amplitude jet bounds are discharged from primitive norms by the final
assembly; this lemma alone is not a primitive estimate.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem norm_iteratedFDeriv_completion_discrepancy_on_le
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    {R : Set (Variables n)} (hR : IsOpen R)
    (ha : ContDiffOn ℝ ∞ (amplitude d J u Ω S) R)
    (hh : ContDiffOn ℝ ∞ (amplitude (homogeneousCoefficients d) J u Ω S) R)
    {s k : ℕ} (hk : k ≤ s) {p : Variables n} (hp : p ∈ R)
    {A B D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hcut : ∀ i ≤ s,
      ‖iteratedFDeriv ℝ i (fun q : Variables n ↦ completionCutoff q.2.2) p‖ ≤ A)
    (hb : ‖iteratedFDeriv ℝ k (amplitude d J u Ω S) p‖ ≤ B)
    (hd : ∀ i ≤ s,
      ‖iteratedFDeriv ℝ i (amplitude (homogeneousCoefficients d) J u Ω S) p‖ ≤ D) :
    ‖iteratedFDeriv ℝ k
      (fun q ↦ amplitude d J u Ω S q - completedAmplitude d J u Ω S q) p‖ ≤
      B + 2 ^ s * A * D := by
  have hc : ContDiff ℝ ∞ (fun q : Variables n ↦ completionCutoff q.2.2) :=
    completionCutoff_contDiff.comp contDiff_snd.snd
  have hcomp : ContDiffOn ℝ ∞ (completedAmplitude d J u Ω S) R := hc.contDiffOn.smul hh
  have hprod := norm_iteratedFDerivWithin_smul_le hc.contDiffOn hh hR.uniqueDiffOn hp
    (show (k : ℕ∞ω) ≤ ∞ by simp)
  have he (i : ℕ) (f : Variables n → ℝ) (hf : ContDiffOn ℝ ∞ f R) :
      iteratedFDerivWithin ℝ i f R p = iteratedFDeriv ℝ i f p :=
    iteratedFDerivWithin_eq_iteratedFDeriv hR.uniqueDiffOn
      ((hf.contDiffAt (hR.mem_nhds hp)).of_le (by simp)) hp
  have hem (i : ℕ) (f : Variables n → Matrix (Fin n) (Fin n) ℝ)
      (hf : ContDiffOn ℝ ∞ f R) :
      iteratedFDerivWithin ℝ i f R p = iteratedFDeriv ℝ i f p :=
    iteratedFDerivWithin_eq_iteratedFDeriv hR.uniqueDiffOn
      ((hf.contDiffAt (hR.mem_nhds hp)).of_le (by simp)) hp
  change ‖iteratedFDerivWithin ℝ k (completedAmplitude d J u Ω S) R p‖ ≤ _ at hprod
  rw [hem k _ hcomp] at hprod
  simp_rw [he _ _ hc.contDiffOn, hem _ _ hh] at hprod
  have hbound : ‖iteratedFDeriv ℝ k (completedAmplitude d J u Ω S) p‖ ≤
      2 ^ s * A * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * D := by
        apply hprod.trans
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hcut i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk)
        · exact hd (k - i) ((Nat.sub_le _ _).trans hk)
      _ = 2 ^ k * A * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose k
      _ ≤ _ := by gcongr; norm_num
  change ‖iteratedFDeriv ℝ k
    (amplitude d J u Ω S - completedAmplitude d J u Ω S) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    ((ha.contDiffAt (hR.mem_nhds hp)).of_le (by simp))
    ((hcomp.contDiffAt (hR.mem_nhds hp)).of_le (by simp))]
  exact (norm_sub_le _ _).trans (add_le_add hb hbound)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
