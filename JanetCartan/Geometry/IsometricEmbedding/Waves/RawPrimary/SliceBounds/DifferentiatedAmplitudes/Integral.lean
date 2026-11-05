module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Branches
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.CompactJets

/-!
# Exact differentiated integrals

The density in the raw wide-band field is merely integrable. Compact frequency
support and joint smoothness supply the domination required to differentiate
the same integral, using the accepted physical-jet and compact-synthesis APIs.
The resulting branch integrals retain their exact frequency powers for
`app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.SliceBounds

variable {E Z F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Physical branch amplitudes are jointly smooth in the Fourier variable
on the original product chart (`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiffOn_jointSliceDerivativeAmplitude {U : Set E} {V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) {φ : E × Z → ℝ} {A : E × Z → F}
    (hφ : ContDiffOn ℝ ∞ φ (U ×ˢ V)) (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) :
    ContDiffOn ℝ ∞ (fun q : E × Z ↦ sliceDerivativeAmplitude
      (fun x ↦ φ (x, q.2)) (fun x ↦ A (x, q.2)) v b q.1) (U ×ˢ V) := by
  induction s with
  | zero => exact hA
  | succ s ih =>
    rcases b with ⟨b, t⟩
    have ht := ih (Fin.tail v) t
    cases b
    · exact (contDiffOn_parameterFDeriv hU hV ht).clm_apply contDiffOn_const
    · exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_parameterFDeriv hU hV hφ).clm_apply contDiffOn_const))).smul ht

variable [FiniteDimensional ℝ E] [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace F]
  {U : Set E} {V K : Set Z} {μ : Measure Z} [IsFiniteMeasure (μ.restrict K)]

/-- All mixed physical derivatives commute with the actual compact Fourier
integral. The density has no differentiability hypothesis, and local domination
comes from the original smooth atom (`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_weightedCompactIntegral_apply
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {f : Z → ℂ} (hf : IntegrableOn f K μ) {A : E × Z → F}
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (s : ℕ) {x : E} (hx : x ∈ U) (v : Fin s → E) :
    iteratedFDeriv ℝ s (fun y ↦ ∫ η in K, f η • A (y, η) ∂μ) x v =
      ∫ η in K, f η • iteratedFDeriv ℝ s (fun y ↦ A (y, η)) x v ∂μ := by
  have hi := contDiffOn_weightedCompactIntegral hU hV hK hKV hf hA
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    let B : E × Z → F := fun q ↦ iteratedFDeriv ℝ s (fun y ↦ A (y, q.2)) q.1 (Fin.tail v)
    have hB : ContDiffOn ℝ ∞ B (U ×ˢ V) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s ↦ E) F (Fin.tail v)).contDiff.comp_contDiffOn
        (contDiffOn_atomPhysicalJet hU hV hA s)
    rw [((hi.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top s)).iteratedFDeriv_succ_apply_left']
    have heq : (fun y ↦ iteratedFDeriv ℝ s
        (fun z ↦ ∫ η in K, f η • A (z, η) ∂μ) y (Fin.tail v)) =ᶠ[𝓝 x]
        (fun y ↦ ∫ η in K, f η • B (y, η) ∂μ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy (Fin.tail v)
    rw [heq.fderiv_eq, (hasFDerivAt_weightedCompactIntegral hU hV hK hKV hf hB hx).fderiv,
      ContinuousLinearMap.integral_apply
        (integrableOn_weightedAtom hK hKV hf
          (contDiffOn_parameterFDeriv hU hV hB).continuousOn hx)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with η hη
    simp only [smul_apply]
    congr 1
    have hAx : ContDiffAt ℝ ∞ (fun y ↦ A (y, η)) x :=
      (hA.contDiffAt ((hU.prod hV).mem_nhds ⟨hx, hKV hη⟩)).comp x
        (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hAx.differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top s)).iteratedFDeriv_succ_apply_left').symm

/-- Exact branch integrals of the same compact oscillatory field at every
physical order. All branch integrability and differentiation steps follow
from primitive smoothness and compact frequency support
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_compactOscillatoryIntegral_eq_branches
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {f : Z → ℂ} (hf : IntegrableOn f K μ) {φ : E × Z → ℝ} {A : E × Z → F}
    (hφ : ContDiffOn ℝ ∞ φ (U ×ˢ V)) (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    (κ : ℝ) (s : ℕ) {x : E} (hx : x ∈ U) (v : Fin s → E) :
    iteratedFDeriv ℝ s (fun y ↦ ∫ η in K,
      f η • (Complex.exp (Complex.I * (κ * φ (y, η) : ℝ)) • A (y, η)) ∂μ) x v =
      ∑ b : SliceDerivativeBranch s, (κ : ℂ) ^ b.phaseCount •
        ∫ η in K, (Complex.exp (Complex.I * (κ * φ (x, η) : ℝ)) * f η) •
          sliceDerivativeAmplitude (fun y ↦ φ (y, η)) (fun y ↦ A (y, η)) v b x ∂μ := by
  have he : ContDiffOn ℝ ∞
      (fun q ↦ Complex.exp (Complex.I * (κ * φ q : ℝ))) (U ×ˢ V) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul hφ))).cexp
  have hbranch (b : SliceDerivativeBranch s) :
      IntegrableOn (fun η ↦ (Complex.exp (Complex.I * (κ * φ (x, η) : ℝ)) * f η) •
        sliceDerivativeAmplitude (fun y ↦ φ (y, η)) (fun y ↦ A (y, η)) v b x) K μ := by
    have hb : ContDiffOn ℝ ∞ (fun q : E × Z ↦
        Complex.exp (Complex.I * (κ * φ q : ℝ)) •
          sliceDerivativeAmplitude (fun y ↦ φ (y, q.2)) (fun y ↦ A (y, q.2)) v b q.1)
        (U ×ˢ V) := he.smul (contDiffOn_jointSliceDerivativeAmplitude hU hV hφ hA v b)
    simpa only [mul_smul, smul_comm (f _) (Complex.exp _)] using
      integrableOn_weightedAtom hK hKV hf hb.continuousOn hx
  have hE : ContDiffOn ℝ ∞
      (fun q ↦ Complex.exp (Complex.I * (κ * φ q : ℝ)) • A q) (U ×ˢ V) := he.smul hA
  rw [iteratedFDeriv_weightedCompactIntegral_apply hU hV hK hKV hf hE s hx v]
  calc
    _ = ∫ η in K, ∑ b : SliceDerivativeBranch s, (κ : ℂ) ^ b.phaseCount •
        ((Complex.exp (Complex.I * (κ * φ (x, η) : ℝ)) * f η) •
          sliceDerivativeAmplitude (fun y ↦ φ (y, η)) (fun y ↦ A (y, η)) v b x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with η hη
      have hp : ContDiffOn ℝ ∞ (fun y ↦ φ (y, η)) U :=
        hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hKV hη⟩)
      have ha : ContDiffOn ℝ ∞ (fun y ↦ A (y, η)) U :=
        hA.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hKV hη⟩)
      rw [iteratedFDeriv_oscillation_smul_eq_branches hU hp ha κ s hx v]
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by
      rw [integral_finsetSum _ (fun b _ ↦ Integrable.fun_smul _ (hbranch b))]
      simp only [integral_smul]

end JanetCartan.RawPrimary.SliceBounds
