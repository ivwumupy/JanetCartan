module

public import JanetCartan.Iteration.RevisedStage.Cutoff
public import JanetCartan.Analysis.PhysicalCutoff.Tail

/-!
# The same physical source sum's Fourier-Sobolev profile

For §15, `main:eq:joint-physical-profile` and Step 6 of `paper-v2.tex`,
combine the original primary and secondary norms before applying the actual
cutoff tail. These are the existing physical Bessel weights at `2πξ` and the
actual Lebesgue L² norm. Finiteness is proved from Schwartz regularity, not
assumed or inferred from a total `toReal` norm. This is independent of the
Sobolev embedding and does not duplicate the cutoff-tail proof.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.RevisedStage

open Pseudodifferential PhysicalCutoff

variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "V" => Euclidean N

/-- §15 Step 6: the genuine physical weighted Fourier norm of the SAME sum
is bounded by the two separate source norms. No Fourier identification or
weighted-integrability premise is added. -/
theorem physicalWeightedNorm_add_le (s : ℝ) (P W : SchwartzMap E V) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (P + W)) ξ) 2 volume).toReal ≤
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (complexify P) ξ) 2 volume).toReal +
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (complexify W) ξ) 2 volume).toReal := by
  have he : 𝓕 (complexify (P + W)) = 𝓕 (complexify P) + 𝓕 (complexify W) := by
    change fourierCLM ℝ _ (SchwartzMap.postcompCLM euclideanComplexInclusion (P + W)) = _
    rw [map_add, map_add]
    rfl
  have hsum : (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (P + W)) ξ) =
      (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) • 𝓕 (complexify P) ξ) +
      (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) • 𝓕 (complexify W) ξ) := by
    funext ξ
    rw [he]
    simp only [add_apply, smul_add, Pi.add_apply]
  rw [hsum]
  have hP := (memLp_physicalWeightedFourier s P).eLpNorm_ne_top
  have hW := (memLp_physicalWeightedFourier s W).eLpNorm_ne_top
  apply (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP, hW⟩)
    (eLpNorm_add_le (by norm_num))).trans_eq
  exact ENNReal.toReal_add hP hW

/-- §15 Step 6: the source for the actual cutoff is the SAME `P+W`.
Separate primary `δ` and secondary `δ²` profiles give its required higher-order
physical Sobolev profile, without a loss beyond the literal revised `B₀`. -/
theorem physicalWeightedNorm_add_le_of_profiles
    {P W : SchwartzMap E V} {C δ R : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (hP : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight ((RevisedScales.baselineOrder n : ℝ) + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify P) ξ) 2 volume).toReal ≤
      C * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k))
    (hW : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight ((RevisedScales.baselineOrder n : ℝ) + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify W) ξ) 2 volume).toReal ≤
      C * δ ^ 2 * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k)) :
    (eLpNorm (fun ξ ↦
      euclideanSobolevWeight ((RevisedScales.baselineOrder n : ℝ) + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify (P + W)) ξ) 2 volume).toReal ≤
      (2 * C) * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k) := by
  apply ((physicalWeightedNorm_add_le _ P W).trans (add_le_add hP hW)).trans
  have hδsq := quadratic_amplitude_le hδ hδ1
  calc
    _ ≤ C * δ * R ^ RevisedScales.displacementLoss n *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k) +
        C * δ * R ^ RevisedScales.displacementLoss n *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k) := by gcongr
    _ = _ := by ring

end JanetCartan.RevisedStage
