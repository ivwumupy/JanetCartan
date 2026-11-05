module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.Basic

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Joint Schwartz bounds for the unit-period cutoff kernel

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the concrete kernel is a product
of two Schwartz functions after permuting the parameter coordinates, multiplied
by a temperate bilinear Fourier phase. We prove the separate-variable product
bounds directly from Leibniz's rule. All transverse dimensions, including zero,
are retained.

The consumer is `exists_unitPeriodSchwartz_compactSmooth`, which separately
constructs the Schwartz marginal and uses the kernel representation identity.
-/

@[expose] public noncomputable section

open scoped SchwartzMap ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

/-- Pullback by either product projection does not increase derivative norms.
This supplies the product estimate for the cutoff kernel in
`app:ch_background:eq:bg-density-adjoint`. -/
private theorem norm_iteratedFDeriv_comp_contraction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(E, ℂ)) (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) (m : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right (f.smooth m) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
    _ = _ := mul_one _

/-- The separate-variable product used by `exists_unitPeriodCutoffKernel_schwartz`.
The maximum product norm lets each Leibniz term use a weighted seminorm of
one factor and an unweighted seminorm of the other
(`app:ch_background:eq:bg-density-adjoint`). -/
private def schwartzSeparateProduct
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) : 𝓢(E × F, ℂ) where
  toFun p := f p.1 * g p.2
  smooth' := ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)
  decay' k m := by
    let A := fun i ↦ SchwartzMap.seminorm ℝ k i f
    let A₀ := fun i ↦ SchwartzMap.seminorm ℝ 0 i f
    let B := fun i ↦ SchwartzMap.seminorm ℝ k i g
    let B₀ := fun i ↦ SchwartzMap.seminorm ℝ 0 i g
    refine ⟨∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * (A i * B₀ (m - i) + A₀ i * B (m - i)), ?_⟩
    intro p
    have hfst (i : ℕ) : ‖iteratedFDeriv ℝ i (fun q : E × F ↦ f q.1) p‖ ≤
        ‖iteratedFDeriv ℝ i f p.1‖ :=
      norm_iteratedFDeriv_comp_contraction f (ContinuousLinearMap.fst ℝ E F)
        (ContinuousLinearMap.norm_fst_le ℝ E F) i p
    have hsnd (i : ℕ) : ‖iteratedFDeriv ℝ i (fun q : E × F ↦ g q.2) p‖ ≤
        ‖iteratedFDeriv ℝ i g p.2‖ :=
      norm_iteratedFDeriv_comp_contraction g (ContinuousLinearMap.snd ℝ E F)
        (ContinuousLinearMap.norm_snd_le ℝ E F) i p
    have hweight : ‖p‖ ^ k ≤ ‖p.1‖ ^ k + ‖p.2‖ ^ k := by
      rcases le_total ‖p.1‖ ‖p.2‖ with h | h
      · simp only [Prod.norm_def, max_eq_right h]
        exact le_add_of_nonneg_left (by positivity)
      · simp only [Prod.norm_def, max_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
    calc
      _ ≤ ‖p‖ ^ k * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : E × F ↦ f q.1) p‖ *
            ‖iteratedFDeriv ℝ (m - i) (fun q : E × F ↦ g q.2) p‖ := by
        gcongr
        exact norm_iteratedFDeriv_mul_le ((f.smooth m).comp contDiff_fst)
          ((g.smooth m).comp contDiff_snd) p le_rfl
      _ = ∑ i ∈ Finset.range (m + 1), ‖p‖ ^ k *
          ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : E × F ↦ f q.1) p‖ *
            ‖iteratedFDeriv ℝ (m - i) (fun q : E × F ↦ g q.2) p‖) :=
        Finset.mul_sum ..
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ (‖p.1‖ ^ k + ‖p.2‖ ^ k) *
              ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p.1‖ *
                ‖iteratedFDeriv ℝ (m - i) g p.2‖) := by
            gcongr
            · exact hfst i
            · exact hsnd (m - i)
          _ = (m.choose i : ℝ) *
              ((‖p.1‖ ^ k * ‖iteratedFDeriv ℝ i f p.1‖) *
                  ‖iteratedFDeriv ℝ (m - i) g p.2‖ +
                ‖iteratedFDeriv ℝ i f p.1‖ *
                  (‖p.2‖ ^ k * ‖iteratedFDeriv ℝ (m - i) g p.2‖)) := by ring
          _ ≤ _ := by
            gcongr
            · exact SchwartzMap.le_seminorm ℝ k i f p.1
            · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g (m - i) p.2
            · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f i p.1
            · exact SchwartzMap.le_seminorm ℝ k (m - i) g p.2

open CarrierSobolev
open scoped RealInnerProductSpace

/-- The permutation `((x, η), z) ↦ (x, (z, η))` for the cutoff kernel in
`app:ch_background:eq:bg-density-adjoint`, retaining the Hilbert coordinates. -/
private def unitPeriodCutoffCoordinates (n : ℕ) :
    (InitialSpace n × ParameterSpace) ≃L[ℝ] (ParameterSpace × InitialSpace n) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ParameterSpace (Euclidean (n - 1))
  ((e.prodCongr (ContinuousLinearEquiv.refl ℝ ParameterSpace)).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ParameterSpace (Euclidean (n - 1)) ParameterSpace)).trans
    ((ContinuousLinearEquiv.refl ℝ ParameterSpace).prodCongr
      ((ContinuousLinearEquiv.prodComm ℝ (Euclidean (n - 1)) ParameterSpace).trans e.symm))

/-- The actual Fourier phase is temperate in all joint variables, as needed
by `exists_unitPeriodCutoffKernel_schwartz`
(`app:ch_background:eq:bg-density-adjoint`). -/
private theorem unitPeriodCutoffPhase_temperate (n : ℕ) :
    Function.HasTemperateGrowth (fun p : InitialSpace n × ParameterSpace ↦
      (Real.fourierChar ⟪p.2, p.1.fst⟫ : ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun p : InitialSpace n × ParameterSpace ↦ p.1.fst) :=
    (WithLp.fstL 2 ℝ ParameterSpace (Euclidean (n - 1))).hasTemperateGrowth.comp
      (ContinuousLinearMap.fst ℝ (InitialSpace n) ParameterSpace).hasTemperateGrowth
  have hz := (ContinuousLinearMap.snd ℝ (InitialSpace n) ParameterSpace).hasTemperateGrowth
  have hi : Function.HasTemperateGrowth
      (fun p : InitialSpace n × ParameterSpace ↦ ⟪p.2, p.1.fst⟫) :=
    (innerSL ℝ).bilinear_hasTemperateGrowth hz hx
  have ha := (Function.HasTemperateGrowth.const (2 * Real.pi)).mul hi
  simpa only [Function.comp_def, Pi.mul_apply, Real.fourierChar_apply] using
    Complex.hasTemperateGrowth_exp_mul_I.comp ha

/-- The concrete cutoff Fourier kernel is jointly Schwartz in every initial
and integration coordinate, including zero transverse dimension. This closes
the kernel construction used by `exists_unitPeriodSchwartz_compactSmooth`
for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_unitPeriodCutoffKernel_schwartz (n : ℕ)
    (χ : SchwartzMap CarrierSobolev.ParameterSpace ℂ)
    (f : SchwartzMap (CarrierSobolev.InitialSpace n) ℂ) :
    ∃ K : SchwartzMap (CarrierSobolev.InitialSpace n × CarrierSobolev.ParameterSpace) ℂ,
      ∀ p, K p = unitPeriodCutoffKernel χ f p := by
  let amplitude := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (unitPeriodCutoffCoordinates n) (schwartzSeparateProduct χ f)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun p : InitialSpace n × ParameterSpace ↦
    (Real.fourierChar ⟪p.2, p.1.fst⟫ : ℂ)) amplitude, ?_⟩
  intro p
  rw [SchwartzMap.smulLeftCLM_apply_apply (unitPeriodCutoffPhase_temperate n)]
  change (Real.fourierChar ⟪p.2, p.1.fst⟫ : ℂ) *
    (χ p.1.fst * f (WithLp.toLp 2 (p.2, p.1.snd))) = _
  simp only [unitPeriodCutoffKernel]
  ring

end JanetCartan.ContinuumAdjoint.DensityMultiplier
