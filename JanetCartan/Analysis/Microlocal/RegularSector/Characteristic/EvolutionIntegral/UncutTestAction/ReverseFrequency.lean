module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.RetardedLimit
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedReverse

/-!
# The original reversed-triangle frequency datum

The literal adjoint triangle is continuous and bounded in frequency using
only zeroth-order symbol bounds. These are the prerequisites for testing
`Mχsource* Bβ* E_b* Mχout*` against Schwartz data and removing the cutoff in
`app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The original adjoint evolution in frequency, with the conjugate multiplier
outside its reversed time triangle. The conjugate source mask is applied when
this datum is paired with a test. Source: `app:ch_regular_base:lem:retarded-kernel`. -/
def reverseRetardedFrequency (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout β : E → ℂ) (u : E → V) (a c : ℝ) (ξ : E) : V :=
  star (β ξ) • ∫ s in Icc a c, ∫ t in s..c, ∫ y,
    reverseTimeFourierKernel Ψ b χout u ξ t s y

/-- Reversing the actual elapsed slab gives the original adjoint frequency
triangle, with supported regularity and the original lower buffer. Consumer:
`continuous_reverseRetardedFrequency`, for `app:ch_regular_base:lem:retarded-kernel`. -/
theorem reverseRetardedFrequency_eq_elapsed
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (hocs : HasCompactSupport χout)
    (a c : ℝ) (hcΔ : c - a ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a c)
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : E → V) (hu : Continuous u) (ξ : E) :
    reverseRetardedFrequency Ψ b χout β u a c ξ =
      ∫ r in Icc 0 Δ, ∫ x in tsupport χout,
        star (β ξ) • reverseTimeFourierKernel Ψ b χout u ξ (x 0)
          (x 0 - max 0 (min Δ r)) (spatialPart x) := by
  let F : E → ℝ → ℝ → Euclidean d → V := fun ξ t s y ↦
    star (β ξ) • reverseTimeFourierKernel Ψ b χout u ξ t
      (t - max 0 (min Δ (t - s))) y
  have hF : Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦
      F p.2 p.1.1.1 p.1.1.2 p.1.2) := by
    simpa only [one_mul] using continuous_supported_reverseTimeFourierKernel
      Ψ b χout β Δ hΔ hΨ hb ho hβ (fun _ ↦ 1) continuous_const u hu
  have ht : (∫ r in Icc 0 Δ, ∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) =
      ∫ s in Icc a c, ∫ t in s..c, ∫ y, F ξ t s y := by
    apply integral_elapsed_space_eq_reverse_triangle (F ξ)
      (hF.comp (continuous_id.prodMk continuous_const))
      (hocs.image continuous_spatialPart) a c Δ hcΔ
    · intro t s y h
      have hx : χout (timeSpacePoint t y) = 0 := by
        by_contra hn
        rcases h with ht | hy
        · exact ht (by simpa only [timeSpacePoint_time] using hout _ hn)
        · exact hy ⟨timeSpacePoint t y, subset_tsupport χout hn, spatialPart_timeSpacePoint t y⟩
      simp [F, reverseTimeFourierKernel, hx]
    · intro t s y hs
      by_cases hx : χout (timeSpacePoint t y) = 0
      · simp [F, reverseTimeFourierKernel, hx]
      have ht : t ∈ Icc a c := by simpa only [timeSpacePoint_time] using hout _ hx
      have hlow : t - max 0 (min Δ (t - s)) ≤ a := by
        have h1 : t - a ≤ Δ := by linarith [ht.2]
        have h2 : t - a ≤ t - s := by linarith
        have h3 := (le_min h1 h2).trans (le_max_right 0 (min Δ (t - s)))
        linarith
      simp [F, reverseTimeFourierKernel, hzero _ _ _ _ hlow]
  have heF : (∫ s in Icc a c, ∫ t in s..c, ∫ y, F ξ t s y) =
      star (β ξ) •
        ∫ s in Icc a c, ∫ t in s..c, ∫ y, reverseTimeFourierKernel Ψ b χout u ξ t s y := by
    simp_rw [← integral_smul, ← intervalIntegral.integral_smul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs.2] at ht
    have hr0 : 0 ≤ t - s := sub_nonneg.mpr ht.1
    have hrΔ : t - s ≤ Δ := by linarith [ht.2, hs.1]
    dsimp only
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [F, min_eq_right hrΔ, max_eq_right hr0, sub_sub_cancel]
  unfold reverseRetardedFrequency
  rw [← heF, ← ht]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  have he : (∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) =
      ∫ x in tsupport χout, F ξ (x 0) (x 0 - r) (spatialPart x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have he : timeSpacePoint (x 0) (spatialPart x) = x :=
        timeSpaceMeasurableEquiv.symm_apply_apply x
      simp [F, reverseTimeFourierKernel, he, image_eq_zero_of_notMem_tsupport hx])).symm
  simpa only [F, sub_sub_cancel] using he

/-- The original adjoint frequency datum is continuous, even though the
phase regularity is required only on the original masks. Consumer: absolute
integrability of all reversed-triangle test pairings in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem continuous_reverseRetardedFrequency
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (hocs : HasCompactSupport χout)
    (a c : ℝ) (hcΔ : c - a ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a c)
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : E → V) (hu : Continuous u) :
    Continuous (reverseRetardedFrequency Ψ b χout β u a c) := by
  have hF := continuous_supported_reverseTimeFourierKernel
    Ψ b χout β Δ hΔ hΨ hb ho hβ (fun _ ↦ 1) continuous_const u hu
  have hc : Continuous (fun p : (E × ℝ) × E ↦
      star (β p.1.1) • reverseTimeFourierKernel Ψ b χout u p.1.1 (p.2 0)
        (p.2 0 - max 0 (min Δ p.1.2)) (spatialPart p.2)) := by
    have htime : Continuous (fun p : (E × ℝ) × E ↦ p.2 0) := by fun_prop
    have hx : Continuous (fun p : (E × ℝ) × E ↦
      (((p.2 0, p.2 0 - p.1.2), spatialPart p.2), p.1.1)) :=
      ((htime.prodMk (htime.sub continuous_fst.snd)).prodMk
        (continuous_spatialPart.comp continuous_snd)).prodMk continuous_fst.fst
    simpa only [Function.comp_def, one_mul, sub_sub_cancel] using hF.comp hx
  have hi : Continuous (fun p : E × ℝ ↦ ∫ x in tsupport χout,
      star (β p.1) • reverseTimeFourierKernel Ψ b χout u p.1 (x 0)
        (x 0 - max 0 (min Δ p.2)) (spatialPart x)) :=
    continuous_parametric_integral_of_continuous hc hocs
  have ht : Continuous (fun ξ : E ↦ ∫ r in Icc 0 Δ, ∫ x in tsupport χout,
      star (β ξ) • reverseTimeFourierKernel Ψ b χout u ξ (x 0)
        (x 0 - max 0 (min Δ r)) (spatialPart x)) :=
    continuous_parametric_integral_of_continuous hi isCompact_Icc
  have he := funext (reverseRetardedFrequency_eq_elapsed Ψ b χout β Δ hΔ hΨ hb ho hβ
    hocs a c hcΔ hout hzero u hu)
  rw [he]
  exact ht

/-- Zeroth-order bounds suffice to bound the whole reversed-triangle
frequency datum. No derivative of the output datum or integrated Sobolev bound
is used. The original primitive budgets produce `hβbound` at order zero and
`hbound` by `norm_elapsedSpatialAmplitude_le_orderSeminorm`. Consumer: cutoff
removal in all test pairings of `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_bound_reverseRetardedFrequency
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (hocs : HasCompactSupport χout)
    (a c : ℝ) (hcΔ : c - a ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a c)
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : E → V) (hu : Continuous u)
    (Cβ Cb : ℝ) (hCβ : 0 ≤ Cβ) (hCb : 0 ≤ Cb)
    (hβbound : ∀ ξ, ‖β ξ‖ ≤ Cβ)
    (hbound : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ‖b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)‖ ≤ Cb) :
    ∃ B ≥ 0, ∀ ξ, ‖reverseRetardedFrequency Ψ b χout β u a c ξ‖ ≤ B := by
  obtain ⟨D, hD⟩ := hocs.exists_bound_of_continuousOn (ho.star.smul hu).continuousOn
  change ∀ x ∈ tsupport χout, ‖star (χout x) • u x‖ ≤ D at hD
  let B := Cβ * (sourceMatrixAction (r := q)).opNorm * Cb * max 0 D
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (mul_nonneg hCβ (sourceMatrixAction (r := q)).opNorm_nonneg) hCb)
    (le_max_left 0 D)
  refine ⟨B * volume.real (tsupport χout) * volume.real (Icc 0 Δ), by positivity, ?_⟩
  intro ξ
  rw [reverseRetardedFrequency_eq_elapsed Ψ b χout β Δ hΔ hΨ hb ho hβ
    hocs a c hcΔ hout hzero u hu]
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro r hr
  apply norm_setIntegral_le_of_norm_le_const hocs.measure_lt_top
  intro x hx
  by_cases hξ : ξ ∈ tsupport β
  · have hx' : timeSpacePoint (x 0) (spatialPart x) = x :=
      timeSpaceMeasurableEquiv.symm_apply_apply x
    simp only [reverseTimeFourierKernel, norm_smul, norm_star, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul, min_eq_right hr.2, max_eq_right hr.1, hx']
    calc
      _ ≤ Cβ * ‖(b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)).conjTranspose.mulVec
          (star (χout x) • u x)‖ :=
        mul_le_mul_of_nonneg_right (hβbound ξ) (norm_nonneg _)
      _ ≤ Cβ * ((sourceMatrixAction (r := q)).opNorm *
          ‖(b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)).conjTranspose‖ *
          ‖star (χout x) • u x‖) :=
        mul_le_mul_of_nonneg_left ((sourceMatrixAction (r := q)).le_opNorm₂ _ _) hCβ
      _ ≤ B := by
        rw [Matrix.frobenius_norm_conjTranspose]
        dsimp only [B]
        rw [mul_assoc Cβ, mul_assoc Cβ]
        apply mul_le_mul_of_nonneg_left _ hCβ
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound r hr x hx ξ hξ)
            (sourceMatrixAction (r := q)).opNorm_nonneg)
          ((hD x hx).trans (le_max_right 0 D)) (norm_nonneg _)
          (mul_nonneg (sourceMatrixAction (r := q)).opNorm_nonneg hCb)
  · simpa only [image_eq_zero_of_notMem_tsupport hξ, star_zero, zero_smul, norm_zero] using hB

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
