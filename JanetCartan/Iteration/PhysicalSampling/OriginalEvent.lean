module

public import JanetCartan.Iteration.PhysicalSampling.Probability
public import JanetCartan.Iteration.PhysicalSampling.LocalizedEvent
public import JanetCartan.Iteration.PhysicalSamplingShells.Native

/-!
# The common native scalar event at the original revised stage scales

A single threshold precedes every current-data kernel. The original measured
and half-weighted scalar rows use the same realization, the same original
carrier weights, and the same refined shells. The numerical Bernstein budget,
physical mesh, tolerance, count, and mass bounds are derived, not assumed.
Only the original analytic sharp/full-mean/kernel bounds remain to be supplied
by the actual wave and scalar producers. This is not an unconditional Main.
Consumers: `app:ch_waves:thm:sampling` and `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.PhysicalSampling

open Sampling Sampling.AsymptoticRealization Sampling.Realization SeparatedSampling
open SamplingKernelBounds RawInputPartition LatticeQuadrature Sampling.BackgroundQuadrature
open CanonicalRowComparison PhysicalSamplingShells

/-- Convert the actual outputs of `exists_original_scalar_sampling_bounds`
back to the original half-weighted scalar kernels. The cutoff is exactly one
on active original weights; zero weights are retained without division. -/
theorem scalar_original_inputs_of_carrier_cut
    {A : Type*} [Fintype A] {n J p : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : A → Point → ℝ) (hβ : ∀ a, Continuous (β a)) (hβone : ∀ a z, |β a z| ≤ 1)
    {ψ : A → Point → ℝ} (hplateau : ∀ a z, ψ a z ≠ 0 → β a z = 1)
    (B h : ℝ) (w : ℝ → ℝ) {Cband Cmean : ℝ}
    (hband : ∀ a (i : RefinedIndex J) color z,
      ‖(scalarCarrierCutKernel (D a) (β a) (hβ a) (hβone a)).operator
        (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ Cband * refinedRadius i)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h (fun color z ↦
      refinedKernelPrefix (scalarCarrierCutKernel (D a) (β a) (hβ a) (hβone a)) J (color, z))‖ ≤ Cmean) :
    (∀ a (i : RefinedIndex J) color z, ψ a z ≠ 0 →
      ‖(D a).operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ Cband * refinedRadius i) ∧
    ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun color z ↦ refinedKernelPrefix (D a) J (color, z))‖ ≤ Cmean := by
  constructor
  · intro a i color z hz
    simpa only [scalarCarrierCutKernel, parameterCutKernel_operator,
      hplateau a z hz, Complex.ofReal_one, one_smul] using hband a i color z
  · have heq : (∑ a, patchMeanNormal p B (ψ a) w h (fun color z ↦
        refinedKernelPrefix (scalarCarrierCutKernel (D a) (β a) (hβ a) (hβone a)) J (color, z))) =
        ∑ a, patchMeanNormal p B (ψ a) w h
          (fun color z ↦ refinedKernelPrefix (D a) J (color, z)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact scalarCarrierCutKernel_patchMeanNormal (D a) (β a) (hβ a) (hβone a) (ψ a)
        (hplateau a) B h w J
    rwa [heq] at hmean

/-- The literal revised common event and its full half-weighted native scalar
norm, with one threshold before all admissible current kernels. The measured
and scalar sharp estimates are used only where the ORIGINAL weight is nonzero.
No numerical tail budget, chosen-successful sample, separate scalar sample,
changed detector, new measure, or assumed native operator norm occurs. -/
theorem exists_threshold_original_common_scalar_native
    {A : Type*} [Fintype A] {n p : ℕ} (hn : 1 ≤ n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    {ψ : A → Point → ℝ} {B C_op Cmean : ℝ} {P Q : A → ℝ}
    (hB : 0 ≤ B) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hQ : ∀ a, 0 ≤ Q a) (hC_op : 0 ≤ C_op) :
    ∃ C > (0 : ℝ), ∃ T₀ ≥ (1 : ℝ), ∀ T ≥ T₀,
      let J := cutoffCount (T ^ fineExponent)
      let h := T ^ (-separationExponent)
      let t := T ^ (-((3 : ℝ) / 512))
      let w := convolvedBoxWindow κ p
      ∀ D Dscalar : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n,
        (∀ a, (D a).squaredKernelConstant ≤ Q a) →
        (∀ a, (Dscalar a).squaredKernelConstant ≤ Q a) →
        (∀ a (i : RefinedIndex J) color z, ψ a z ≠ 0 →
          ‖(D a).operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ C_op * refinedRadius i) →
        (∀ a (i : RefinedIndex J) color z, ψ a z ≠ 0 →
          ‖(Dscalar a).operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ C_op * refinedRadius i) →
        ‖∑ a, patchMeanNormal p B (ψ a) w h
          (fun color z ↦ refinedKernelPrefix (D a) J (color, z))‖ ≤ Cmean →
        ‖∑ a, patchMeanNormal p B (ψ a) w h
          (fun color z ↦ refinedKernelPrefix (Dscalar a) J (color, z))‖ ≤ Cmean →
      ∃ ξ : A → ShiftSpace p B h,
        (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧ extendedShift (ξ a) q i < h) ∧
        (∀ L ≤ J, ‖familyDeviation p B ψ w h
          (fun a color z ↦ refinedKernelPrefix (D a) L (color, z)) ξ‖ ≤ t) ∧
        (∀ L ≤ J, ‖familyDeviation p B ψ w h
          (fun a color z ↦ refinedKernelPrefix (Dscalar a) L (color, z)) ξ‖ ≤ t) ∧
        (∀ a, SampleGeometry p B (P a) 1 (ψ a) w h (extendedShift (ξ a))) ∧
        (∀ L ≤ J, ‖nativeScalarOperator hn B ψ w h (fun a ↦ extendedShift (ξ a)) Dscalar L‖ ≤
          Real.sqrt (C + 1)) ∧
        (Fintype.card (SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a))) : ℝ) ≤
          ((Fintype.card A : ℝ) * countConstant p B) * T ^ (1 + samplingSlack) ∧
        (∑ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
          sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i) ≤ countConstant p B * (∑ a, P a) ∧
        (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Qbg : A → ℝ),
          (∀ a color, ContDiff ℝ p (fun z ↦ ψ a z • G a color z)) →
          (∀ a, 0 ≤ Qbg a) →
          (∀ a color z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a color z) z‖ ≤ Qbg a) →
          ‖familyBackgroundError p B ψ w h (fun a ↦ extendedShift (ξ a)) G‖ ≤
            backgroundQuadratureConstant p B * (∑ a, Qbg a) * h ^ p) := by
  obtain ⟨C, hC, hmeanC, T₀, hT₀, hbudget⟩ :=
    exists_original_common_bernstein_budget (n := n) (p := p) (Cmean := Cmean)
      hψ hQ hC_op (by norm_num : (0 : ℝ) < 1 / 43)
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T hT J h t w D Dscalar hkernel hkernelScalar hband hbandScalar hmean hmeanScalar
  have hT1 : 1 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hΛ : 1 ≤ T ^ fineExponent :=
    Real.one_le_rpow hT1 (by norm_num [fineExponent, meanSlack])
  have hΛ₀ : T₀ ≤ T ^ fineExponent :=
    hT.trans (Real.self_le_rpow_of_one_le hT1 (by norm_num [fineExponent, meanSlack]))
  have hh : 0 < h := Real.rpow_pos_of_pos hTpos _
  have hh₁ : h ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num [separationExponent])
  have ht₁ : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  obtain ⟨hR, ht, hthreshold, hfailure⟩ := hbudget (T ^ fineExponent) hΛ₀
  simp only [samplingMesh_fineExponent hTpos.le, samplingTolerance_fineExponent hTpos.le]
    at hR ht hthreshold hfailure
  have hmean' := hmean.trans hmeanC
  have hmeanScalar' := hmeanScalar.trans hmeanC
  obtain ⟨ξ, hξ, hevent, heventScalar, hgeometry, hbackground⟩ :=
    exists_common_original_scalar_realization_of_support (V := V) hc hs hm hkpos hk hp
      D Dscalar hn hψ hψc hh hh₁ hC_op hband hbandScalar
      (block_le hψ hC_op hΛ hh.le) hR hC hmean' hmeanScalar' ht hthreshold
      (hfailure D Dscalar hkernel hkernelScalar)
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  have hμ := sampleWeight_nonneg (fun a ↦ extendedShift (ξ a)) hw hψ hh.le
  refine ⟨ξ, hξ, hevent, heventScalar, hgeometry, ?_, ?_, ?_, hbackground⟩
  · intro L hL
    have hmeanL := (norm_refinedKernelPrefix_mean_le_full Dscalar L hw hψ hψc
      (contDiff_convolvedBoxWindow hc hs p).continuous).trans hmeanScalar'
    exact (norm_nativeScalarOperator_le_of_common_event hn B ψ w h ξ Dscalar L hμ
      (heventScalar L hL) hmeanL).trans (Real.sqrt_le_sqrt (add_le_add le_rfl ht₁))
  · exact UniformStep.sampleIndex_card_le_originalScale p hB ψ w hT1 (fun a ↦ extendedShift (ξ a))
  · simpa only [one_pow, mul_one] using
      UniformStep.sampleWeight_mass_le_originalScale p hw hψ hT1 (fun a ↦ extendedShift (ξ a))

end JanetCartan.PhysicalSampling
