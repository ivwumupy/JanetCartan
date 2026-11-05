module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.CompactSobolev
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# Frobenius Fourier envelopes from compact classical jets

For `app:ch_response:eq:response-graded-source`, the existing integer
weak-derivative comparison is applied to every complex component of the
original Frobenius tensor. The actual Hilbert-valued Fourier transform is
identified componentwise by its Lebesgue integral, with the same physical
`2π` convention. No Sobolev embedding or extra derivative is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory FourierTransform
open scoped ContDiff ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponsePrimarySources
open Pseudodifferential ResponseTransfer SourceNegative AmplitudeBound

variable {n : ℕ}
local notation "E" => Euclidean n
local notation "F" => Matrix (Fin n) (Fin n) ℂ

private theorem fourier_toLp_ae {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {f : E → H}
    (hf : MemLp f 2 volume) (hi : Integrable f) :
    (𝓕 (hf.toLp f) : Lp H 2 volume) =ᵐ[volume] 𝓕 f :=
  (Localization.fourierTransform_coeFn_ae_integral_hilbert _
    (hi.congr hf.coeFn_toLp.symm)).trans
      (Eventually.of_forall (Real.fourier_congr_ae hf.coeFn_toLp))

private theorem fourier_component (L : F →L[ℂ] ℂ) {f : E → F}
    (hi : Integrable f) (ξ : E) : L (𝓕 f ξ) = 𝓕 (L ∘ f) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff ξ).mpr hi)]
  congr 1
  funext x
  exact L.map_smul_of_tower _ _

private theorem tensor_norm_le_component_sum (z : F) :
    ‖z‖ ≤ ∑ i : Fin (n * n), ‖SingleChannel.matrixChannelEquiv n n z i‖ := by
  rw [← (SingleChannel.matrixChannelEquiv n n).norm_map z, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_iff.mpr
  exact ⟨Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)⟩

/-- Bounded compact spatial jets imply actual tensor Fourier membership and
its norm bound. Only jets through `p` enter this deduction of
`app:ch_response:eq:response-graded-source`. -/
theorem primary_tensor_fourier_bound_of_compact_jets
    {S : Set E} (hS : IsCompact S) (p : ℕ) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ S) (hmem : MemLp f 2 volume)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ p, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    MemLp (fun ξ ↦ euclideanSobolevWeight (p : ℝ) ξ •
      (𝓕 (hmem.toLp f) : Lp F 2 volume) ξ) 2 volume ∧
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight (p : ℝ) ξ •
      (𝓕 (hmem.toLp f) : Lp F 2 volume) ξ) 2 volume).toReal ≤
        ((n * n : ℕ) : ℝ) * LowEnvelope.compactCoordinateSobolevConstant n p *
          Real.sqrt (volume.real S) * B := by
  let L (i : Fin (n * n)) : F →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp
      (SingleChannel.matrixChannelEquiv n n).toContinuousLinearEquiv.toContinuousLinearMap
  have hL (i : Fin (n * n)) : ‖(L i).restrictScalars ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [L] using (PiLp.norm_apply_le (SingleChannel.matrixChannelEquiv n n z) i).trans_eq
      ((SingleChannel.matrixChannelEquiv n n).norm_map z)
  have hc (i : Fin (n * n)) : ContDiff ℝ ∞ (L i ∘ f) :=
    ((L i).restrictScalars ℝ).contDiff.comp hf
  have hsc (i : Fin (n * n)) : Function.support (L i ∘ f) ⊆ S :=
    (subset_tsupport _).trans ((tsupport_comp_subset (L i).map_zero f).trans hs)
  have hbc (i : Fin (n * n)) (a : List (Fin n)) (ha : a.length ≤ p) (x : E) :
      ‖euclideanCoordinateDerivList a (L i ∘ f) x‖ ≤ B := by
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv (hc i) a x).trans
    apply (((L i).restrictScalars ℝ).norm_iteratedFDeriv_comp_left
      hf.contDiffAt (by simp)).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (hL i)).trans (hb _ ha x)
  choose hm hsob hbound using fun i ↦ LowEnvelope.exists_compactCoordinateSobolev
    p (L i ∘ f) (hc i) hS (hsc i) hB (hbc i)
  let w (ξ : E) := euclideanSobolevWeight (p : ℝ) ξ •
    (𝓕 (hmem.toLp f) : Lp F 2 volume) ξ
  let g (i : Fin (n * n)) := weightedL2Fourier (p : ℝ) ((hm i).toLp (L i ∘ f))
  have hw : AEStronglyMeasurable w volume :=
    (continuous_euclideanSobolevWeight _).aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)
  have hgm : ∀ i, MemLp (g i) 2 volume := hsob
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _) hs)
  have he (i : Fin (n * n)) : (fun ξ ↦ L i (w ξ)) =ᵐ[volume] g i := by
    filter_upwards [fourier_toLp_ae hmem hi,
      fourier_toLp_ae (hm i) ((L i).integrable_comp hi)] with ξ hξ hξi
    simp only [w, g, weightedL2Fourier, ContinuousLinearMap.map_smul_of_tower,
      hξ, hξi, fourier_component (L i) hi]
  have hsum : MemLp (fun ξ ↦ ∑ i, ‖g i ξ‖) 2 volume :=
    memLp_finsetSum _ (fun i _ ↦ (hgm i).norm)
  have hle : ∀ᵐ ξ ∂volume, ‖w ξ‖ ≤ ‖∑ i, ‖g i ξ‖‖ := by
    filter_upwards [ae_all_iff.mpr he] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
    convert tensor_norm_le_component_sum (w ξ) using 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg norm (hξ i).symm
  refine ⟨hsum.of_le hw hle, ?_⟩
  calc
    (eLpNorm w 2 volume).toReal ≤ (eLpNorm (fun ξ ↦ ∑ i, ‖g i ξ‖) 2 volume).toReal :=
      ENNReal.toReal_mono hsum.ne_top (eLpNorm_mono_ae hw hle)
    _ ≤ ∑ i, (eLpNorm (g i) 2 volume).toReal := by
      have ht : eLpNorm (fun ξ ↦ ∑ i, ‖g i ξ‖) 2 volume ≤
          ∑ i, eLpNorm (g i) 2 volume := by
        simpa only [Finset.sum_fn, eLpNorm_norm _ (hgm _).aestronglyMeasurable] using
          (eLpNorm_sum_le (μ := volume) (f := fun i ξ ↦ ‖g i ξ‖) (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      exact (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ ↦ (hgm i).ne_top)) ht).trans_eq
        (ENNReal.toReal_sum (fun i _ ↦ (hgm i).ne_top))
    _ ≤ ∑ _i : Fin (n * n), LowEnvelope.compactCoordinateSobolevConstant n p *
        Real.sqrt (volume.real S) * B := Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = _ := by simp; ring

/-- The strong `A*L^p` profile is preserved in the genuine Frobenius Fourier
norm. All constants precede the amplitude and the scale, as required by
`app:ch_response:eq:response-graded-source`. -/
theorem exists_primary_tensor_sobolev_constants {S : Set E} (hS : IsCompact S)
    (J : ℕ → ℝ) (hJ : ∀ j, 0 ≤ J j) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧
      ∀ (f : E → F) (hmem : MemLp f 2 volume) (A L : ℝ),
      0 ≤ A → 1 ≤ L → ContDiff ℝ ∞ f → tsupport f ⊆ S →
      (∀ x j, ‖iteratedFDeriv ℝ j f x‖ ≤ J j * A * L ^ j) →
      SobolevEnvelopeBounds f hmem A L C := by
  let C := fun p ↦ ((n * n : ℕ) : ℝ) * LowEnvelope.compactCoordinateSobolevConstant n p *
    Real.sqrt (volume.real S) * ∑ j ∈ Finset.range (p + 1), J j
  have hC : ∀ p, 0 ≤ C p := fun p ↦ mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (LowEnvelope.compactCoordinateSobolevConstant_pos n p).le) (Real.sqrt_nonneg _))
    (Finset.sum_nonneg (fun j _ ↦ hJ j))
  refine ⟨C, hC, ?_⟩
  intro f hmem A L hA hL hf hs hb
  have hp (p : ℕ) := primary_tensor_fourier_bound_of_compact_jets hS p f hf hs hmem
    (B := (∑ j ∈ Finset.range (p + 1), J j) * A * L ^ p)
    (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hJ j)) hA)
      (pow_nonneg (zero_le_one.trans hL) _))
    (fun j hj x ↦ (hb x j).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ ↦ hJ i)
        (Finset.mem_range_succ_iff.mpr hj)) hA)
      (pow_le_pow_right₀ hL hj) (pow_nonneg (zero_le_one.trans hL) _)
      (mul_nonneg (Finset.sum_nonneg (fun i _ ↦ hJ i)) hA)))
  exact ⟨hf, hA, hL, hC, fun p ↦ (hp p).1,
    fun p ↦ (hp p).2.trans_eq (by dsimp [C]; ring)⟩

end JanetCartan.ResponsePrimarySources
