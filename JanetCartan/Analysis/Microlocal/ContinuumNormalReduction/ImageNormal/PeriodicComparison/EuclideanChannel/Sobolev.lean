module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Sobolev.Multipliers

/-!
# H¹ preservation of the concrete Euclidean image channel

The actual complex channel `μ P J χ` of `app:ch_background:prop:bg-frame`,
Step 1, preserves Fourier H¹. All coefficient bounds come from the fixed
smooth compact masks. No global bound is imposed on the unmasked `A` or `Z`.
The final estimate supplies the complex input for the real-channel hypothesis
`hB` of `normalCrossTerms_sobolev_one_bounds`; transfer through the real
inclusion is the responsibility of the channel's reality theorem.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)

/-- Each actual scalar entry of `μ P J χ` preserves H¹, for
`app:ch_background:prop:bg-frame`, Step 1. The constant depends only on the
fixed masked coefficients. -/
theorem euclideanChannelBlock_sobolev_one_bound
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (i j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L², MemFourierSobolev 1 f →
      MemFourierSobolev 1 (euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc i j f) ∧
        fourierSobolevNorm 1 (euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc i j f) ≤
          C * fourierSobolevNorm 1 f := by
  obtain ⟨Cχ, hCχ, hχb⟩ := freezingPhysicalMultiplier_sobolev_one_bound χ hχ hχc
  choose CA hCA hAb using fun a : Fin d ↦
    freezingPhysicalMultiplier_sobolev_one_bound (fun x ↦ μ x * A x a i j)
      (hμ.mul (hA a i j)) hμc.mul_right
  obtain ⟨CZ, hCZ, hZb⟩ :=
    freezingPhysicalMultiplier_sobolev_one_bound (fun x ↦ μ x * Z x i j)
      (hμ.mul (hZ i j)) hμc.mul_right
  refine ⟨((∑ a, CA a) + CZ) * Cχ,
    mul_nonneg (add_nonneg (Finset.sum_nonneg (fun a _ ↦ hCA a)) hCZ) hCχ, ?_⟩
  intro f hf
  let g := freezingPhysicalMultiplier χ hχ.continuous hχc f
  have hg := hχb f hf
  let b := fun a ↦ freezingPhysicalMultiplier (fun x ↦ μ x * A x a i j)
    (hμ.continuous.mul (hA a i j).continuous) hμc.mul_right
      (imageDerivativeBesselL2Operator a g)
  let z := freezingPhysicalMultiplier (fun x ↦ μ x * Z x i j)
    (hμ.continuous.mul (hZ i j).continuous) hμc.mul_right (imageBesselL2Operator g)
  have hb (a : Fin d) : MemFourierSobolev 1 (b a) ∧
      fourierSobolevNorm 1 (b a) ≤ CA a * (Cχ * fourierSobolevNorm 1 f) := by
    have hm := imageDerivativeBesselL2Operator_sobolev_one_bound a g hg.1
    have ha := hAb a _ hm.1
    exact ⟨ha.1, ha.2.trans
      (mul_le_mul_of_nonneg_left (hm.2.trans hg.2) (hCA a))⟩
  have hz : MemFourierSobolev 1 z ∧
      fourierSobolevNorm 1 z ≤ CZ * (Cχ * fourierSobolevNorm 1 f) := by
    have hm := imageBesselL2Operator_sobolev_one_bound g hg.1
    have hz := hZb _ hm.1
    exact ⟨hz.1, hz.2.trans
      (mul_le_mul_of_nonneg_left (hm.2.trans hg.2) hCZ)⟩
  have he : euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc i j f =
      (∑ a, b a) + z := by
    simp only [euclideanChannelBlock, ContinuousLinearMap.comp_apply, sum_apply, add_apply,
      b, z, g]
  rw [he]
  have hs := fourierSobolev_finsetSum Finset.univ b (fun a _ ↦ (hb a).1)
  refine ⟨hs.1.add hz.1, (fourierSobolevNorm_add_le hs.1 hz.1).trans ?_⟩
  calc
    _ ≤ (∑ a, fourierSobolevNorm 1 (b a)) + fourierSobolevNorm 1 z :=
      add_le_add hs.2 le_rfl
    _ ≤ (∑ a, CA a * (Cχ * fourierSobolevNorm 1 f)) +
        CZ * (Cχ * fourierSobolevNorm 1 f) :=
      add_le_add (Finset.sum_le_sum (fun a _ ↦ (hb a).2)) hz.2
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The concrete complex Euclidean channel is bounded on actual Fourier H¹,
as required in the image-normal paragraph of `app:ch_background:prop:bg-frame`,
Step 1. This includes all positive dimensions (and also dimension zero).
Every analytic premise is supplied by smoothness and compactness of the
stated fixed data. -/
theorem complexEuclideanChannel_sobolev_one_bound
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ f : C², MemVectorFourierSobolev 1 f →
      MemVectorFourierSobolev 1 (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f) ∧
        vectorFourierSobolevNorm 1
          (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f) ≤
            CB * vectorFourierSobolevNorm 1 f := by
  choose C hC hb using
    euclideanChannelBlock_sobolev_one_bound A Z χ μ hA hZ hχ hχc hμ hμc
  let K := ∑ i, ∑ j, C i j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j))
  have hCK (i j : Fin d) : C i j ≤ K :=
    (Finset.single_le_sum (fun j _ ↦ hC i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j))
        (Finset.mem_univ i))
  refine ⟨(d : ℝ) * d * K, by positivity, ?_⟩
  intro f hf
  have h := vectorMatrixL2Operator_fourierSobolev_bound
    (euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc) 1 1 K 0 hK (by norm_num)
    (fun i j u hu ↦ ⟨(hb i j u hu).1, by
      simpa only [zero_mul, add_zero] using (hb i j u hu).2.trans
        (mul_le_mul_of_nonneg_right (hCK i j) (fourierSobolevNorm_nonneg 1 u))⟩) f hf
  simpa only [complexEuclideanChannel, Fintype.card_fin, zero_mul, add_zero] using h

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
