module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Scaling

/-!
# Tangential decay on a half-space

The tangential part of the common kernel estimate in
`app:ch_regular:lem:finite-chain`, “A common kernel estimate” and “Retarded
and signed factors”. Joint derivative bounds restrict to every normal slice
without enlarging the derivative profiles. Integration in the normal variable
then costs only the measure of the normal projection of the common compact
support, giving the fixed amplitude offset of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular:lem:finite-chain`: restricting a joint smooth function to
a tangential slice does not increase the norm of any iterated derivative.
This uses the product norm and differentiates only tangentially. -/
theorem norm_iteratedFDeriv_tangentialSlice_le_joint
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × E → V) (hf : ContDiff ℝ ∞ f) (d : ℝ) (z : E) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun w ↦ f (d, w)) z‖ ≤
      ‖iteratedFDeriv ℝ r f (d, z)‖ := by
  let j := ContinuousLinearMap.inr ℝ ℝ E
  let g := fun x : ℝ × E ↦ f ((d, 0) + x)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have heq : (fun w ↦ f (d, w)) = g ∘ j := by ext w; simp [g, j]
  rw [heq, j.iteratedFDeriv_comp_right hg z (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ r g (j z)‖ * ‖j‖ ^ r := by
      simpa using (iteratedFDeriv ℝ r g (j z)).norm_compContinuousLinearMap_le
        (fun _ ↦ j)
    _ ≤ ‖iteratedFDeriv ℝ r g (j z)‖ :=
      mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ..))
    _ = _ := by simp [g, j, iteratedFDeriv_comp_add_left]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_regular:eq:chain-tail`, tangential half-space estimate from the
joint derivative bounds in `app:ch_regular:lem:finite-chain`. The phase gap is
needed only on the nonnegative normal slices. All slice support, derivative,
integrability and Fubini hypotheses are derived here from the joint data.
The constant uses the original profiles `P`, `A`, is independent of `L`, `R`
and external parameters sharing those profiles and the compact support, and
the amplitude offset `b` is fixed independently of `q`. -/
theorem norm_halfSpaceOscillatoryIntegral_le_tangential
    {U K : Set (ℝ × E)} (hU : IsOpen U) (hK : IsCompact K)
    (e : ι → E) (F : ℝ × E → ℝ) (a : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ K ∩ U)
    {δ G L R : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hgap : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ U →
      δ ≤ Localization.phaseGradientSquare e (fun w ↦ F (d, w)) z)
    (hupper : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ U → ‖fderiv ℝ F (d, z)‖ ≤ G)
    {P A : ℕ → ℝ} (hA : ∀ r, 0 ≤ A r) (b q : ℕ)
    (hp : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r (fderiv ℝ F) x‖ ≤ P r * L ^ r)
    (ha_bound : ∀ x ∈ K, ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ A r * L ^ (r + b)) :
    ‖halfSpaceOscillatoryIntegral μ R F a‖ ≤
      (decayConstant e δ G P A q * volume.real (Prod.fst '' K) *
        μ.real (Prod.snd '' K)) * L ^ b * (L / R) ^ q := by
  have hsK : tsupport a ⊆ K := hs.trans inter_subset_left
  have hc : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport _) hsK
  let C := (decayConstant e δ G P A q * μ.real (Prod.snd '' K)) *
    L ^ b * (L / R) ^ q
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (decayConstant_nonneg e δ G P A hA q) (measureReal_nonneg))
      (pow_nonneg hL0 _)) (pow_nonneg (div_nonneg hL0 hR0) _)
  have hslice (d : ℝ) (hd : 0 ≤ d) :
      ‖∫ z, Localization.phaseOscillation (R • F) (d, z) * a (d, z) ∂μ‖ ≤ C := by
    have hj : Continuous (fun z : E ↦ (d, z)) := continuous_const.prodMk continuous_id
    have hjs : ContDiff ℝ ∞ (fun z : E ↦ (d, z)) :=
      contDiff_const.prodMk contDiff_id
    have hsupport : tsupport (fun z ↦ a (d, z)) ⊆
        (fun z ↦ (d, z)) ⁻¹' (K ∩ U) :=
      (tsupport_comp_subset_preimage a hj).trans (preimage_mono hs)
    have hgrad (z : E) :
        ‖fderiv ℝ (fun w ↦ F (d, w)) z‖ ≤ ‖fderiv ℝ F (d, z)‖ := by
      simpa only [norm_iteratedFDeriv_one] using
        norm_iteratedFDeriv_tangentialSlice_le_joint F hF d z 1
    have hp_slice (z : E) (hz : z ∈ tsupport (fun w ↦ a (d, w))) (r : ℕ) :
        ‖iteratedFDeriv ℝ r (fderiv ℝ (fun w ↦ F (d, w))) z‖ ≤ P r * L ^ r := by
      rw [norm_iteratedFDeriv_fderiv]
      apply (norm_iteratedFDeriv_tangentialSlice_le_joint F hF d z (r + 1)).trans
      rw [← norm_iteratedFDeriv_fderiv]
      exact hp (d, z) (hsupport hz).1 r
    have ha_slice (z : E) (hz : z ∈ tsupport (fun w ↦ a (d, w))) (r : ℕ) :
        ‖iteratedFDeriv ℝ r (fun w ↦ a (d, w)) z‖ ≤ A r * L ^ (r + b) :=
      (norm_iteratedFDeriv_tangentialSlice_le_joint a ha d z r).trans
        (ha_bound (d, z) (hsupport hz).1 r)
    exact norm_oscillatoryIntegral_le (μ := μ) (hU.preimage hj)
      (hK.image continuous_snd) e (fun z ↦ F (d, z)) (fun z ↦ a (d, z))
      (hF.comp hjs).contDiffOn (ha.comp hjs).contDiffOn
      (fun z hz ↦ (hsupport hz).2) (tsupport_slice_subset_projection hK hsK d)
      hδ hL hR (hgap d hd) (fun z hz ↦ (hgrad z).trans (hupper d hd z hz))
      hA b q hp_slice ha_slice
  let f := fun d ↦ ∫ z, Localization.phaseOscillation (R • F) (d, z) * a (d, z) ∂μ
  have hf : tsupport f ⊆ Prod.fst '' K :=
    tsupport_integral_slice_subset_projection μ hK (tsupport_mul_subset_right.trans hsK)
  have hnormal := hK.image continuous_fst
  have hfinite : volume ((Prod.fst '' K) ∩ Ici (0 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) hnormal.measure_lt_top
  have heq : (∫ d in Ici (0 : ℝ), f d) =
      ∫ d in (Prod.fst '' K) ∩ Ici (0 : ℝ), f d := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici inter_subset_right
    intro d hd
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hd.2 ⟨hf h, hd.1⟩
  rw [halfSpaceOscillatoryIntegral_eq_integral_slice hF ha hc]
  change ‖∫ d in Ici (0 : ℝ), f d‖ ≤ _
  rw [heq]
  calc
    _ ≤ C * volume.real ((Prod.fst '' K) ∩ Ici (0 : ℝ)) :=
      norm_setIntegral_le_of_norm_le_const hfinite (fun d hd ↦ hslice d hd.2)
    _ ≤ C * volume.real (Prod.fst '' K) :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono inter_subset_left hnormal.measure_lt_top.ne) hC
    _ = _ := by dsimp [C]; ring

end JanetCartan.FiniteChain.Retarded.HalfSpace
