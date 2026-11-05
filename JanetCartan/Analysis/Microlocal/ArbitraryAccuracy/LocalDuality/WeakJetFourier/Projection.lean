module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.Components

/-!
# Projection of genuine weak extensions

Continuous real linear maps preserve the actual integration-by-parts identities,
the L² representatives, and a quantitative bound for the weak jet. The consumer
is the componentwise Fourier comparison for `app:ch_regular_base:eq:negative-duality`
and `app:ch_regular:eq:inverse-remainder`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ContDiff

namespace JanetCartan.Mollification

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure E}

/-- Projection preserves the genuine whole-space weak derivative identity,
as needed for the real components in `app:ch_regular_base:eq:negative-duality`. -/
theorem HasWeakFDerivOn.comp_clm_univ {f : E → F} {f' : E → E →L[ℝ] F}
    (hw : HasWeakFDerivOn μ f f' univ) (L : F →L[ℝ] G) :
    HasWeakFDerivOn μ (L ∘ f) (fun x ↦ L.comp (f' x)) univ := by
  refine ⟨L.locallyIntegrableOn_comp hw.1,
    ((ContinuousLinearMap.compL ℝ E F G) L).locallyIntegrableOn_comp hw.2.1, ?_⟩
  intro ψ hψ hc hs v
  have hψd : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x ↦ fderiv ℝ ψ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ ↦ A v) rfl
  have hi : Integrable (fun x ↦ fderiv ℝ ψ x v • f x) μ :=
    (locallyIntegrableOn_univ.mp hw.1).integrable_smul_left_of_hasCompactSupport hψd hψdc
  have hi' : Integrable (fun x ↦ ψ x • f' x v) μ := by
    simpa using (ContinuousLinearMap.apply ℝ F v).integrable_comp
      ((locallyIntegrableOn_univ.mp hw.2.1).integrable_smul_left_of_hasCompactSupport
        hψ.continuous hc)
  simpa only [ContinuousLinearMap.comp_apply, comp_apply, ← L.map_smul,
    L.integral_comp_comm hi, L.integral_comp_comm hi', ← L.map_neg] using
    congrArg L (hw.2.2 ψ hψ hc hs v)

/-- Project every order of a genuine weak jet, including its order-zero value,
for `app:ch_regular_base:eq:negative-duality`. -/
theorem HasWeakJetOn.comp_clm_univ {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {N : ℕ}
    (hw : HasWeakJetOn μ f J univ N) (L : F →L[ℝ] G) :
    HasWeakJetOn μ (L ∘ f) (fun j x ↦ L.compContinuousMultilinearMap (J j x)) univ N := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · ext x v
    simp [hw.1, iteratedFDeriv_zero_apply]
  · convert (hw.2 j hj).comp_clm_univ
      ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ E) F G) L)
      using 1
    · ext x v
      rfl
    · ext x v w
      rfl

end JanetCartan.Mollification

namespace JanetCartan.LocalSobolev.SobolevExtension

variable {n N : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {W : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 W F}

/-- Project an actual weak extension, with all its weak identities and L² jets,
for the component reduction in `app:ch_regular_base:eq:negative-duality`. -/
def mapCLM (e : SobolevExtension W N v) (L : F →L[ℝ] G) :
    SobolevExtension W N (L.compLp v) where
  toFun := L ∘ e.toFun
  jet := fun j x ↦ L.compContinuousMultilinearMap (e.jet j x)
  weakJet := e.weakJet.comp_clm_univ L
  memLp_fun := L.comp_memLp' e.memLp_fun
  memLp_jet := fun j hj ↦
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F G) L).comp_memLp' (e.memLp_jet j hj)
  restrict_eq := by
    filter_upwards [e.restrict_eq, L.coeFn_compLp v] with x hx hL
    exact (congrArg L hx).trans hL.symm

/-- The whole-space representative of the projected extension is the projected
L² class, for `app:ch_regular_base:eq:negative-duality`. -/
theorem toL2_mapCLM (e : SobolevExtension W N v) (L : F →L[ℝ] G) :
    (e.mapCLM L).toL2 = L.compLp e.toL2 := by
  apply Lp.ext
  filter_upwards [(e.mapCLM L).toL2_coeFn, e.toL2_coeFn, L.coeFn_compLp e.toL2]
    with x hx he hL
  exact hx.trans ((congrArg L he.symm).trans hL.symm)

/-- Every projected jet is bounded by the original jet with the same operator
norm factor at every order (`app:ch_regular_base:eq:negative-duality`). -/
theorem jetNorm_mapCLM_le (e : SobolevExtension W N v) (L : F →L[ℝ] G) :
    (e.mapCLM L).jetNorm ≤ ‖L‖ * e.jetNorm := by
  unfold jetNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j ≤ N := by simpa using Finset.mem_range.mp hj
  have hm := e.memLp_jet j hjN
  have hbound := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((e.mapCLM L).memLp_jet j hjN).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ L.norm_compContinuousMultilinearMap_le (e.jet j x)) 2
  exact (ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.eLpNorm_ne_top) hbound).trans_eq
      (by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg L)])

end JanetCartan.LocalSobolev.SobolevExtension
