module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedPhaseWeighted
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ReverseFourier
/-!
# Reversed time triangle with support-local regularity

The conjugate multiplier is retained outside the reversed time triangle.
Clamping elapsed time proves continuity from the original supported primitive
phase. Lower-buffer vanishing survives this clamping and both endpoints are
retained. Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ
/-- The cutoff multiplier times the reverse integrand is continuous from
regularity only near the physical and conic supports. Consumer:
`integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier_of_support`,
for `app:ch_regular_base:lem:retarded-kernel`. -/
theorem continuous_supported_reverseTimeFourierKernel
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (θ : E → ℂ) (hθ : Continuous θ)
    (u : E → V) (hu : Continuous u) :
    Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦
      star (θ p.2 * β p.2) • reverseTimeFourierKernel Ψ b χout u p.2
        p.1.1.1 (p.1.1.1 - max 0 (min Δ (p.1.1.1 - p.1.1.2))) p.1.2) := by
  have hW := continuous_supported_elapsed_phaseWeightedAmplitude Ψ b χout (fun _ ↦ 1) β
    Δ hΔ hΨ hb ho continuous_const hβ θ hθ
  have hx : Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦ timeSpacePoint p.1.1.1 p.1.2) :=
    continuous_timeSpacePoint.comp (continuous_fst.fst.fst.prodMk continuous_fst.snd)
  have hr : Continuous (fun p : ((ℝ × ℝ) × Euclidean d) × E ↦ p.1.1.1 - p.1.1.2) := by fun_prop
  have hp := ((hr.prodMk hx).prodMk (continuous_const (y := (0 : E)))).prodMk continuous_snd
  have hc := (hW.comp hp).matrix_conjTranspose.matrix_mulVec (hu.comp hx)
  convert hc using 1
  funext p
  simp only [Function.comp_apply, reverseTimeFourierKernel, frequencyCutFullAmplitude, elapsedAmplitude,
    elapsedPhase, timeSpacePoint_time, spatialPart_timeSpacePoint, mul_one,
    Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, star_mul]
  congr 1
  ring

/-- The actual compact adjoint elapsed integral equals the reversed time
triangle, assuming regularity only where the original kernel is supported.
The expression retains `Mχsource* Bβ* E_b* Mχout*`, its normalization and lower
buffer. No uncut test identity is assumed. Source:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier_of_support
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hβ : Continuous β)
    (θ : E → ℂ) (hθ : Continuous θ)
    (hocs : HasCompactSupport χout) (hθcs : HasCompactSupport θ)
    (a c : ℝ) (hcΔ : c - a ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a c)
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : E → V) (hu : Continuous u) (z : E) :
    (∫ r in Icc 0 Δ, reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z) =
      cutReverseRetardedFourier Ψ b χout χsource β θ u a c z := by
  let F : E → ℝ → ℝ → Euclidean d → V := fun ξ t s y ↦
    star (θ ξ * β ξ) • reverseTimeFourierKernel Ψ b χout u ξ t
      (t - max 0 (min Δ (t - s))) y
  let k : E → ℂ := fun ξ ↦ Complex.exp (Complex.I * (inner ℝ z ξ : ℂ))
  have hF := continuous_supported_reverseTimeFourierKernel Ψ b χout β Δ hΔ hΨ hb ho hβ θ hθ u hu
  have hfx : Continuous (fun p : (ℝ × E) × E ↦ F p.1.2 (p.2 0) (p.2 0 - p.1.1)
      (spatialPart p.2)) := hF.comp
    (((show Continuous (fun p : (ℝ × E) × E ↦ p.2 0) by fun_prop).prodMk
      (by fun_prop)).prodMk (continuous_spatialPart.comp continuous_snd) |>.prodMk continuous_fst.snd)
  have hfxzero (r : ℝ) (ξ x : E) (hx : x ∉ tsupport χout) :
      F ξ (x 0) (x 0 - r) (spatialPart x) = 0 := by
    have he : timeSpacePoint (x 0) (spatialPart x) = x := timeSpaceMeasurableEquiv.symm_apply_apply x
    simp [F, reverseTimeFourierKernel, he, image_eq_zero_of_notMem_tsupport hx]
  have he (r : ℝ) (ξ : E) : (∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) =
      ∫ x in tsupport χout, F ξ (x 0) (x 0 - r) (spatialPart x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hfxzero r ξ)).symm
  have hI : Continuous (fun p : ℝ × E ↦ ∫ x, F p.2 (x 0) (x 0 - p.1) (spatialPart x)) := by
    simp_rw [he]
    exact continuous_parametric_integral_of_continuous hfx hocs
  have hk : Continuous k := by fun_prop
  have hG : Continuous (fun p : ℝ × E ↦ k p.2 • ∫ x, F p.2 (x 0) (x 0 - p.1) (spatialPart x)) :=
    (hk.comp continuous_snd).smul hI
  have hmask (r : ℝ) (hr : r ∈ Icc 0 Δ) : reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z =
      star (χsource z) • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
        ∫ ξ, k ξ • ∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) := by
    rw [cut_reverse_elapsedGraph_masks]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [graphOscillation_star_split]
    have he : timeSpacePoint (x 0) (spatialPart x) = x := timeSpaceMeasurableEquiv.symm_apply_apply x
    simp only [F, k, reverseTimeFourierKernel, sub_sub_cancel, min_eq_right hr.2,
      max_eq_right hr.1, he, elapsedPhase, mul_smul]
    exact smul_comm _ _ _
  have hm : (∫ r in Icc 0 Δ, reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z) =
      star (χsource z) • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
        ∫ r in Icc 0 Δ, ∫ ξ, k ξ • ∫ x, F ξ (x 0) (x 0 - r) (spatialPart x)) := by
    simp_rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simpa only [integral_smul] using hmask r hr
  rw [hm, integral_compact_frequency_slab_swap _ hG hθcs
    (fun r ξ hξ ↦ by simp [F, image_eq_zero_of_notMem_tsupport hξ]) Δ]
  unfold cutReverseRetardedFourier
  congr 2
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [integral_smul]
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
  rw [ht]
  have heF : (∫ s in Icc a c, ∫ t in s..c, ∫ y, F ξ t s y) =
      star (θ ξ * β ξ) •
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
  rw [heF]
  simp only [k, mul_smul]
  exact smul_comm _ _ _

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
