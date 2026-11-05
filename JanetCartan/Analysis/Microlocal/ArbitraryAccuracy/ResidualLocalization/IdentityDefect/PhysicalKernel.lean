module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades.Products
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Buffers

/-!
# Physical tails of the right-localizer kernel

The actual right-quantized kernel is written in the physical `2π`
normalization and estimated by integration by parts in its compact frequency
variable. Smoothness and compact support of the fixed mask produce every
derivative constant. Consumer: the physical source/output tails in
`actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails` and the identity
leakage in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral FiniteChain.Graph Pseudodifferential
open FiniteChain.Retarded.KernelDecay

variable {n : ℕ}
local notation "E" => Euclidean n

/-- The scalar kernel of the original physical right localizer. It retains
the source base `y`, with no approximation or accuracy parameter
(`app:ch_regular:eq:chain-tail`). -/
def rightLocalizerScalarKernel (ρ : ℝ) (mi : LocalizerSymbol n) (x y : E) : ℂ :=
  (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) * ∫ ξ,
    Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) * (mi (y, ρ⁻¹ • ξ) : ℂ)

/-- The scalar kernel is the original right quantization on continuous test
data, not a replacement operator. Absolute integrability and Fubini follow
from the original compact joint symbol; no derivatives of the datum are
used (`app:ch_regular:eq:chain-tail`). -/
theorem rightLocalizer_eq_integral_scalarKernel {r : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : Continuous mi) (his : HasCompactSupport mi)
    (g : E → Fin r → ℂ) (hg : Continuous g) (x : E) :
    rightLocalizer ρ mi g x = ∫ y, rightLocalizerScalarKernel ρ mi x y • g y := by
  let a : E × E → ℂ := fun p ↦ (mi (p.1, ρ⁻¹ • p.2) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (hi.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
  have hca : HasCompactSupport a := by
    apply HasCompactSupport.intro
      (his.image (continuous_fst.prodMk (continuous_snd.const_smul ρ)))
    intro p hp
    have hz : mi (p.1, ρ⁻¹ • p.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hp ⟨(p.1, ρ⁻¹ • p.2), h, by simp [smul_smul, hρ]⟩
    simp only [a, hz, Complex.ofReal_zero]
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (inner ℝ (x - p.1) p.2 : ℂ)) * a p) • g p.1
  have hF : Continuous F := by
    have hp : Continuous (fun p : E × E ↦
        Complex.exp (Complex.I * (inner ℝ (x - p.1) p.2 : ℂ))) := by fun_prop
    exact (hp.mul ha).smul (hg.comp continuous_fst)
  have hcF : HasCompactSupport F := hca.mul_left.smul_right
  have hint : Integrable F (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hF.integrable_of_hasCompactSupport hcF
  have he : rightLocalizer ρ mi g x =
      (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) • ∫ ξ, ∫ y, F (y, ξ) := by
    simp only [rightLocalizer, graphOperator, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, F, a, graphOscillation, inner_sub_left,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [he, ← integral_integral_swap hint]
  simp only [F, a, rightLocalizerScalarKernel, mul_smul, integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [← mul_smul, integral_smul_const]

/-- Exact rescaling of the original physical kernel into the Fourier
transform of its normalized frequency slice. The sign and `2π` conversion
are explicit (`app:ch_regular:eq:chain-tail`). -/
theorem rightLocalizerScalarKernel_eq_fourier {ρ : ℝ} (hρ : 0 < ρ)
    (mi : LocalizerSymbol n) (x y : E) :
    rightLocalizerScalarKernel ρ mi x y =
      ((ρ / (2 * Real.pi)) ^ n : ℝ) •
        𝓕 (fun η ↦ (mi (y, η) : ℂ)) (-(ρ / (2 * Real.pi)) • (x - y)) := by
  let F := fun η : E ↦
    Complex.exp (Complex.I * ((ρ * inner ℝ (x - y) η : ℝ) : ℂ)) * (mi (y, η) : ℂ)
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume F hρ.le
  simp only [Euclidean, finrank_euclideanSpace_fin] at hscale
  have hf : 𝓕 (fun η ↦ (mi (y, η) : ℂ)) (-(ρ / (2 * Real.pi)) • (x - y)) = ∫ η, F η := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [] with η
    have hp : -2 * Real.pi * inner ℝ η (-(ρ / (2 * Real.pi)) • (x - y)) =
        ρ * inner ℝ (x - y) η := by
      rw [inner_smul_right, real_inner_comm η (x - y)]
      field_simp
    simp only [hp, F, smul_eq_mul, mul_comm _ Complex.I]
  have hrescale : (fun ξ : E ↦ F (ρ⁻¹ • ξ)) = fun ξ ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) * (mi (y, ρ⁻¹ • ξ) : ℂ) := by
    funext ξ
    dsimp only [F]
    rw [inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
  rw [rightLocalizerScalarKernel, ← hrescale, hscale, hf]
  rw [← Complex.ofReal_inv]
  change ((2 * Real.pi) ^ n : ℝ)⁻¹ • (ρ ^ n • ∫ η, F η) =
    ((ρ / (2 * Real.pi)) ^ n : ℝ) • ∫ η, F η
  rw [smul_smul, div_pow, div_eq_mul_inv, mul_comm (((2 * Real.pi) ^ n : ℝ)⁻¹)]

private theorem exists_uniform_frequencySlice_fourier_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y θ : E,
      (1 + ‖θ‖) ^ N * ‖𝓕 (fun η ↦ (mi (y, η) : ℂ)) θ‖ ≤ C := by
  let a : E × E → ℂ := fun p ↦ (mi p : ℂ)
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp hi
  have hca : HasCompactSupport a := his.comp_left (g := fun t : ℝ ↦ (t : ℂ)) rfl
  obtain ⟨B, hB, hbound⟩ := hca.exists_bound_iteratedFDeriv ha N
  obtain ⟨R, _, hR⟩ := (his.image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : E)
  let v := volume.real (Metric.closedBall (0 : E) R)
  refine ⟨(2 ^ (N - 1) * (1 + 2 ^ N)) * ((N + 1 : ℕ) : ℝ) * v * B,
    by dsimp [v]; positivity, ?_⟩
  intro y θ
  have hs : tsupport (fun η ↦ a (y, η)) ⊆ Metric.closedBall (0 : E) R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro η hη
    apply hR
    refine ⟨(y, η), subset_tsupport mi ?_, rfl⟩
    simpa only [a, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hη
  have hc : HasCompactSupport (fun η ↦ a (y, η)) :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport _) hs
  have hsm : ContDiff ℝ ∞ (fun η ↦ a (y, η)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hint k : Integrable (iteratedFDeriv ℝ k (fun η ↦ a (y, η))) :=
    ((hsm.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).continuous).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv k)
  have hmass : sourceDerivativeMass (fun η ↦ a (y, η)) N ≤ ((N + 1 : ℕ) : ℝ) * v * B := by
    unfold sourceDerivativeMass
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), v * B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Metric.closedBall (0 : E) R) (fun η hη ↦ by
            rw [image_eq_zero_of_notMem_tsupport
              (fun hh ↦ hη (hs (tsupport_iteratedFDeriv_subset k hh))), norm_zero])]
        calc
          _ ≤ ‖∫ η in Metric.closedBall (0 : E) R,
              ‖iteratedFDeriv ℝ k (fun η ↦ a (y, η)) η‖‖ := le_abs_self _
          _ ≤ B * v := by
            apply norm_setIntegral_le_of_norm_le_const
              (isCompact_closedBall (0 : E) R).measure_lt_top
            intro η _
            simpa only [norm_norm] using
              (norm_iteratedFDeriv_symbol_slice_le ha k y η).trans
                (hbound k (by simpa using Finset.mem_range.mp hk) (y, η))
          _ = v * B := mul_comm _ _
      _ = _ := by simp [mul_assoc]
  have hd := one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    (fun η ↦ a (y, η)) N (hsm.of_le (by simp)) (fun k _ ↦ hint k) θ
  exact hd.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring))

/-- Uniform global decay of the actual rescaled kernel, derived entirely
from the fixed compact smooth proof mask. The only frequency prefactor is
`ρ^n`, independent of the integration accuracy. This is a kernel estimate;
the physical-tail L²-to-Sobolev extension is still required by the consumer
(`app:ch_regular:eq:chain-tail`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_rightLocalizerScalarKernel_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 < ρ → ∀ x y : E,
      (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N * ‖rightLocalizerScalarKernel ρ mi x y‖ ≤
        C * ρ ^ n := by
  intro N
  obtain ⟨B, hB, hb⟩ := exists_uniform_frequencySlice_fourier_decay mi hi his N
  refine ⟨B / (2 * Real.pi) ^ n, by positivity, ?_⟩
  intro ρ hρ x y
  rw [rightLocalizerScalarKernel_eq_fourier hρ, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (ρ / (2 * Real.pi)) ^ n)]
  have h := hb y (-(ρ / (2 * Real.pi)) • (x - y))
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / (2 * Real.pi))] at h
  calc
    _ = (ρ / (2 * Real.pi)) ^ n *
        ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          ‖𝓕 (fun η ↦ (mi (y, η) : ℂ)) (-(ρ / (2 * Real.pi)) • (x - y))‖) := by ring
    _ ≤ (ρ / (2 * Real.pi)) ^ n * B := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- A fixed physical shoulder gap yields arbitrary frequency decay, while
retaining any prescribed integrable spatial weight. The mask and gap are
fixed before accuracy; both polynomial losses are independent of accuracy
(`ρ^n`, with no coefficient loss). This proves the kernel estimate needed
for the original physical cutoff tails from primitive compact smooth masks,
without a shell-majorant or localized-operator premise
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizerScalarKernel_separated_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ x y : E, δ ≤ ‖x - y‖ →
      (1 + ‖x - y‖) ^ M * ‖rightLocalizerScalarKernel ρ mi x y‖ ≤
        C * ρ ^ n * (L / ρ) ^ N := by
  intro N
  obtain ⟨B, hB, hb⟩ := exists_rightLocalizerScalarKernel_decay mi hi his (N + M)
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D := a ^ N * c ^ M
  have hD : 0 < D := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨B / D, div_nonneg hB hD.le, ?_⟩
  intro ρ L hL hLρ x y hgap
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hfreq : ρ * a ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      ρ * a = ρ / (2 * Real.pi) * δ := by dsimp [a]; ring
      _ ≤ ρ / (2 * Real.pi) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ ≤ _ := by linarith
  have hcρ : c ≤ ρ / (2 * Real.pi) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right hρ (by positivity))
  have hspace : c * (1 + ‖x - y‖) ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      _ = c + c * ‖x - y‖ := by ring
      _ ≤ _ := add_le_add (min_le_left _ _)
        (mul_le_mul_of_nonneg_right hcρ (norm_nonneg _))
  have hcombined :
      (ρ ^ N * D) * ((1 + ‖x - y‖) ^ M * ‖rightLocalizerScalarKernel ρ mi x y‖) ≤
        B * ρ ^ n := by
    calc
      _ = ((ρ * a) ^ N * (c * (1 + ‖x - y‖)) ^ M) *
          ‖rightLocalizerScalarKernel ρ mi x y‖ := by
            dsimp [D]
            simp only [mul_pow]
            ring
      _ ≤ ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ M) *
            ‖rightLocalizerScalarKernel ρ mi x y‖ := by gcongr
      _ ≤ B * ρ ^ n := by rw [← pow_add]; exact hb ρ hρpos x y
  have hdiv := (le_div_iff₀ (mul_pos (pow_pos hρpos N) hD)).mpr
    (show ((1 + ‖x - y‖) ^ M * ‖rightLocalizerScalarKernel ρ mi x y‖) *
      (ρ ^ N * D) ≤ B * ρ ^ n by simpa only [mul_comm] using hcombined)
  calc
    _ ≤ (B * ρ ^ n) / (ρ ^ N * D) := hdiv
    _ = (B / D) * ρ ^ n * (1 / ρ) ^ N := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by gcongr

/-- The right kernel retains the exact source-base support of its original
symbol. Its output may still have tails (`app:ch_regular:eq:chain-tail`). -/
theorem rightLocalizerScalarKernel_zero_off_input
    (ρ : ℝ) (mi : LocalizerSymbol n) (x y : E)
    (hy : y ∉ Prod.fst '' tsupport mi) : rightLocalizerScalarKernel ρ mi x y = 0 := by
  have hm (η : E) : mi (y, η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy ⟨(y, η), h, rfl⟩)
  simp only [rightLocalizerScalarKernel, hm, Complex.ofReal_zero, mul_zero, integral_zero]

/-- The physical cutoff tail has arbitrary weighted kernel decay. Compact
input support and the original open physical plateau produce the separation
gap internally. The range and plateau inputs come from the actual masks
and `ProtectedMasks`; all analytic constants are derived from the SAME
fixed smooth compact localizer. This supplies the undifferentiated kernels
of both tails in `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`.
The Sobolev operator extension remains separate
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_rightLocalizerScalarKernel_physicalTail_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χ x = 1}) (M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ x y : E,
      (1 + ‖x - y‖) ^ M * ‖((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y‖ ≤
        C * ρ ^ n * (L / ρ) ^ N := by
  have hdis : Disjoint (Prod.fst '' tsupport mi) (tsupport (fun x ↦ 1 - χ x)) := by
    apply disjoint_left.mpr
    intro y hy hys
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hys
    filter_upwards [isOpen_interior.mem_nhds (hplateau y hy)] with z hz
    exact sub_eq_zero.mpr (interior_subset hz).symm
  obtain ⟨δ, hδ, hgap⟩ := CompatibleResponse.exists_uniform_source_gap
    (his.image continuous_fst) (isClosed_tsupport _) hdis
  intro N
  obtain ⟨C, hC, hb⟩ := exists_rightLocalizerScalarKernel_separated_decay mi hi his hδ M N
  refine ⟨C, hC, ?_⟩
  intro ρ L hL hLρ x y
  have hρpos : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  by_cases hy : y ∈ Prod.fst '' tsupport mi
  · by_cases hx : χ x = 1
    · simp only [hx, sub_self, Complex.ofReal_zero, zero_mul, norm_zero, mul_zero]
      positivity
    · have hs : x ∈ tsupport (fun x ↦ 1 - χ x) :=
        subset_tsupport _ (sub_ne_zero.mpr (Ne.symm hx))
      have hd : δ ≤ ‖x - y‖ := by
        simpa only [dist_eq_norm, norm_sub_rev] using (hgap y hy x hs).le
      have hc : ‖((1 - χ x : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hχ x).2)]
        linarith [(hχ x).1]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) hc) (by positivity)).trans
          (hb ρ L hL hLρ x y hd)
  · rw [rightLocalizerScalarKernel_zero_off_input ρ mi x y hy]
    simp only [mul_zero, norm_zero]
    positivity

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
