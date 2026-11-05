module

public import JanetCartan.Analysis.Extension.Mollification

/-!
# Smooth approximation of finite weak L² jets

For `app:not:fourier` and `app:ch_regular:thm:exact-correction`, normalized
mollification approximates all orders of a finite weak jet simultaneously.
This supplies the approximating sequence for finite-order Sobolev regularity;
it does not yet assert uniform convergence or a continuous representative.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Function ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace JanetCartan.LocalSobolev.FiniteOrder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

-- The public mollification wrapper fixes the domain and codomain to the same
-- universe. These private convolution lemmas keep their universes independent,
-- so the representative theorem applies to an arbitrary finite-dimensional target.
omit [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
private theorem convolution_equiv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (L : F ≃L[ℝ] G)
    (φ : ContDiffBump (0 : E)) (f : E → F) :
    φ.normed μ ⋆[lsmul ℝ ℝ, μ] (L ∘ f) = L ∘ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  ext x
  simp only [convolution, lsmul_apply, comp_apply]
  simp_rw [← L.map_smul]
  exact L.integral_comp_comm _

private theorem iteratedFDeriv_convolution_weakJet {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : Mollification.HasWeakJetOn μ f J univ m) (φ : ContDiffBump (0 : E))
    (j : ℕ) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) =
      φ.normed μ ⋆[lsmul ℝ ℝ, μ] J j := by
  induction j with
  | zero =>
    rw [hw.1, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    exact (convolution_equiv μ
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv φ f).symm
  | succ j ih =>
    let : IsBoundedSMul ℝ (E →L[ℝ] E [×j]→L[ℝ] F) :=
      NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E [×j]→L[ℝ] F)
    have hwj := hw.2 j (by omega)
    have hd : fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] J j) =
        φ.normed μ ⋆[lsmul ℝ ℝ (E := E →L[ℝ] E [×j]→L[ℝ] F), μ]
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F) ∘
            J (j + 1)) := by
      funext x
      exact hwj.fderiv_convolution μ (locallyIntegrableOn_univ.mp hwj.1)
        (locallyIntegrableOn_univ.mp hwj.2.1) φ.contDiff_normed
        φ.hasCompactSupport_normed x (subset_univ _)
    rw [iteratedFDeriv_succ_eq_comp_left, ih (by omega), hd]
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
    have h := convolution_equiv (F := E →L[ℝ] E [×j]→L[ℝ] F)
      (G := E [×(j + 1)]→L[ℝ] F) μ L.symm.toContinuousLinearEquiv φ (L ∘ J (j + 1))
    simpa only [comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using h.symm

omit [CompleteSpace F] in
private theorem memLp_convolution (φ : ContDiffBump (0 : E)) {f : E → F}
    (hf : MemLp f 2 μ) : MemLp (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) 2 μ := by
  have heq : φ.normed μ ⋆[lsmul ℝ ℝ, μ] (hf.toLp f) =
      φ.normed μ ⋆[lsmul ℝ ℝ, μ] f :=
    convolution_congr (lsmul ℝ ℝ) Filter.EventuallyEq.rfl hf.coeFn_toLp
  rw [← heq]
  exact (Mollification.eLpNorm_two_convolution_le μ φ (hf.toLp f)).trans_lt
    (Lp.memLp (hf.toLp f)).eLpNorm_lt_top

private theorem tendsto_eLpNorm_convolution_sub {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0)) {f : E → F}
    (hf : MemLp f 2 μ) :
    Tendsto (fun i ↦ eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) 2 μ)
      atTop (𝓝 0) := by
  have heq : ∀ i, eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) 2 μ =
      eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (hf.toLp f) - (hf.toLp f : E → F))
        2 μ := by
    intro i
    rw [show (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (hf.toLp f) =
        (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f from
      convolution_congr (lsmul ℝ ℝ) Filter.EventuallyEq.rfl hf.coeFn_toLp]
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hf.coeFn_toLp.symm)
  simp_rw [heq]
  exact Mollification.tendsto_eLpNorm_two_convolution_sub μ hφ (hf.toLp f)

/-- The approximation step for `app:not:fourier`: a finite weak L² jet admits
a sequence of smooth L² functions converging in L² at every available order.
No compact-support or classical differentiability assumption is imposed on `f`. -/
theorem exists_smooth_approximation_weakJet {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : Mollification.HasWeakJetOn μ f J univ m) (hf : MemLp f 2 μ)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 μ) :
    ∃ u : ℕ → E → F,
      (∀ i, ContDiff ℝ ∞ (u i)) ∧
      (∀ i, MemLp (u i) 2 μ) ∧
      (∀ i j, j ≤ m → MemLp (iteratedFDeriv ℝ j (u i)) 2 μ) ∧
      Tendsto (fun i ↦ eLpNorm (u i - f) 2 μ) atTop (𝓝 0) ∧
      ∀ j ≤ m, Tendsto (fun i ↦ eLpNorm (iteratedFDeriv ℝ j (u i) - J j) 2 μ)
        atTop (𝓝 0) := by
  let φ : ℕ → ContDiffBump (0 : E) := fun i ↦
    ⟨(1 / ((i : ℝ) + 1)) / 2, 1 / ((i : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun i ↦ (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f,
    fun i ↦ (φ i).hasCompactSupport_normed.contDiff_convolution_left _
      (φ i).contDiff_normed (hf.locallyIntegrable (by norm_num)),
    fun i ↦ memLp_convolution μ (φ i) hf, ?_,
    tendsto_eLpNorm_convolution_sub μ hφ hf, ?_⟩
  · intro i j hj
    rw [iteratedFDeriv_convolution_weakJet μ hw (φ i) j hj]
    exact memLp_convolution μ (φ i) (hJ j hj)
  · intro j hj
    simp_rw [iteratedFDeriv_convolution_weakJet μ hw _ j hj]
    exact tendsto_eLpNorm_convolution_sub μ hφ (hJ j hj)

end JanetCartan.LocalSobolev.FiniteOrder
