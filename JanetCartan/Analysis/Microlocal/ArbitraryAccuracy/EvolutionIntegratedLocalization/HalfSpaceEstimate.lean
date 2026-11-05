module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Matrix half-space decay for the elapsed kernel

The consumer is the compact-frequency elapsed joint kernel in
`app:ch_regular:eq:chain-tail`. Duality applies the existing scalar half-space
argument to the actual matrix amplitude without a channel-dimension loss.
The symbol-size factor is separated from the derivative profile, so the
constant and the grade offset remain independent of frequency and accuracy.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open JanetCartan.Localization FiniteChain.Retarded.HalfSpace

/-- The two-branch half-space estimate for Banach-valued amplitudes, with
the SAME scalar decay constant. This supplies the Frobenius matrix estimate
for the actual elapsed kernel (`app:ch_regular:eq:chain-tail`). The only
amplitude assumptions are its primitive smoothness, support and joint grades.
The fixed symbol size `S` is not inserted into the decay profile. -/
theorem norm_halfSpace_vector_integral_le
    {E V ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [IsScalarTower ℝ ℂ V] [CompleteSpace V] [Fintype ι] [Fintype κ]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {UT UI K : Set (ℝ × E)} (hUT : IsOpen UT) (hUI : IsOpen UI) (hK : IsCompact K)
    (eT : ι → E) (eI : κ → ℝ × E) (F : ℝ × E → ℝ)
    (a : ℝ × E → V) (χ : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a) (hχ : ContDiff ℝ ∞ χ)
    (hsK : tsupport a ⊆ K)
    (hχT : K ∩ tsupport χ ⊆ UT)
    (hχI : (K ∩ tsupport (1 - χ)) ∩ {x | 0 < x.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ x, |x.1| < ε → χ x = 1)
    {δT δI GT GI L R S : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hL : 1 ≤ L) (hR : 1 ≤ R) (hS : 0 < S)
    (hgapT : ∀ r, 0 ≤ r → ∀ z, (r, z) ∈ UT →
      δT ≤ phaseGradientSquare eT (fun w ↦ F (r, w)) z)
    (hupperT : ∀ r, 0 ≤ r → ∀ z, (r, z) ∈ UT → ‖fderiv ℝ F (r, z)‖ ≤ GT)
    (hgapI : ∀ x ∈ UI ∩ {x | 0 < x.1}, δI ≤ phaseGradientSquare eI F x)
    (hupperI : ∀ x ∈ UI ∩ {x | 0 < x.1}, ‖fderiv ℝ F x‖ ≤ GI)
    {P H A : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (b q : ℕ)
    (hp : ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (fderiv ℝ F) x‖ ≤ P j * L ^ j)
    (hχ_bound : ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j)
    (ha_bound : ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j a x‖ ≤ S * A j * L ^ (j + b)) :
    ‖∫ x in Ici (0 : ℝ) ×ˢ (univ : Set E),
        phaseOscillation (R • F) x • a x ∂(volume.prod μ)‖ ≤
      collarDecayConstant μ K eT eI δT δI GT GI P H A q * S * L ^ b * (L / R) ^ q := by
  let v := ∫ x in Ici (0 : ℝ) ×ˢ (univ : Set E),
    phaseOscillation (R • F) x • a x ∂(volume.prod μ)
  obtain ⟨g, hg, hv⟩ := exists_dual_vector'' ℂ v
  let a' : ℝ × E → ℂ := S⁻¹ • (g ∘ a)
  have hga : ContDiff ℝ ∞ (g ∘ a) := (g.restrictScalars ℝ).contDiff.comp ha
  have ha' : ContDiff ℝ ∞ a' := hga.const_smul S⁻¹
  have hs' : tsupport a' ⊆ K :=
    (tsupport_smul_subset_right (fun _ : ℝ × E ↦ S⁻¹) (g ∘ a)).trans
      ((tsupport_comp_subset g.map_zero a).trans hsK)
  have hb' (x) (hx : x ∈ K) (j) :
      ‖iteratedFDeriv ℝ j a' x‖ ≤ A j * L ^ (j + b) := by
    have hb := (g.restrictScalars ℝ).norm_iteratedFDeriv_comp_left (x := x)
      ha.contDiffAt (show (j : ℕ∞ω) ≤ ∞ by simp)
    rw [ContinuousLinearMap.norm_restrictScalars] at hb
    have hb1 := hb.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans_eq
      (one_mul _))
    dsimp only [a']
    rw [iteratedFDeriv_const_smul_apply (hga.contDiffAt.of_le (by simp)), norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
    exact (mul_le_mul_of_nonneg_left (hb1.trans (ha_bound x hx j))
      (inv_nonneg.mpr hS.le)).trans_eq (by field_simp)
  have h := norm_halfSpaceOscillatoryIntegral_le (μ := μ) hUT hUI hK eT eI F a' χ
    hF ha' hχ hs' hχT hχI hε hχ_one hδT hδI hL hR hgapT hupperT hgapI hupperI
    hH hA b q hp hχ_bound hb'
  have hc : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport _) hsK
  have hi : Integrable (fun x ↦ phaseOscillation (R • F) x • a x) (volume.prod μ) :=
    integrable_phaseOscillation_smul isOpen_univ (R • F) a
      (hF.const_smul R).contDiffOn ha.contDiffOn (subset_univ _) hc
  have heq : halfSpaceOscillatoryIntegral μ R F a' = S⁻¹ • g v := by
    unfold halfSpaceOscillatoryIntegral halfSpaceIntegral
    change (∫ x in Ici (0 : ℝ) ×ˢ (univ : Set E),
      phaseOscillation (R • F) x * (S⁻¹ • g (a x)) ∂(volume.prod μ)) = _
    simp_rw [mul_smul_comm]
    rw [integral_smul, ← g.integral_comp_comm hi.restrict]
    simp only [map_smul, smul_eq_mul]
  rw [heq, hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hS.le),
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at h
  have h' := mul_le_mul_of_nonneg_left h hS.le
  rw [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul] at h'
  exact h'.trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
