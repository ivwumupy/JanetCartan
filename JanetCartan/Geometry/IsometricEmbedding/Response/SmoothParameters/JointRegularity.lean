module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.CompactOutput
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Joint regularity from the fixed response's tame bounds

The parameter assertion in `app:ch_response:thm:response-literal-transfer`
requires joint smoothness, rather than smoothness of each spatial slice. The
finite Sobolev-to-uniform estimates prove this for the original response.
Induction differentiates either its physical output or its actual source;
the latter step uses `iteratedFDeriv_response_apply` for that SAME operator.
No joint output regularity is an assumption.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseSmoothParameters
open RetardedSobolev.Spaces ResponseTransfer.ParameterRealization

variable {d p : ℕ} {X G : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {K : Set (ℝ × (Fin d → ℝ))} {L O : Set X} [CompactSpace L]

omit [NormedSpace ℝ X] in
/-- Uniform output-norm continuity gives joint continuity on the open
observation set (`app:ch_response:thm:response-literal-transfer`). -/
private theorem continuousOn_joint_response
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K) (hOL : O ⊆ L)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContinuousOn (B u) L)
    (s : ℕ) (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
      ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ)) :
    ContinuousOn (fun z : Euclidean p × X ↦ B (f z.1) z.2) (U ×ˢ O) := by
  have hc : ContinuousOn (fun c ↦ compactResponse B hBreg (f c)) U :=
    fun a ha ↦ (contDiffAt_compactResponse hU hK B hBreg s hB f hf 0 ha).continuousAt.continuousWithinAt
  rw [continuousOn_iff_continuous_domRestrict]
  have hp : Continuous (fun z : U ×ˢ O ↦ compactResponse B hBreg (f z.val.1)) :=
    hc.comp_continuous continuous_subtype_val.fst (fun z ↦ z.property.1)
  have hx : Continuous (fun z : U ×ˢ O ↦ (⟨z.val.2, hOL z.property.2⟩ : L)) :=
    by fun_prop
  exact continuous_eval.comp (hp.prodMk hx)

/-- Physical differentiation of the SAME response is linear on smooth sources
(`app:ch_response:prop:response-graded`), for the joint-regularity induction. -/
private def spatialResponseDerivative
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContDiff ℝ ∞ (B u)) :
    supportedTests K →ₗ[ℝ] (X → X →L[ℝ] G) where
  toFun u := fderiv ℝ (B u)
  map_add' u v := by
    rw [B.map_add]
    funext x
    exact fderiv_add ((hBreg u).differentiable (by simp) x)
      ((hBreg v).differentiable (by simp) x)
  map_smul' a u := by
    rw [B.map_smul]
    funext x
    exact fderiv_const_smul ((hBreg u).differentiable (by simp) x) a

/-- Every finite joint order follows from the original response's all-order
physical tame estimates (`app:ch_response:thm:response-literal-transfer`).
The compact source and observation sets are fixed. Only the finite source order
and bound may depend on the physical output order; they precede every source.
The producer is the fixed inverse and its ambient reconstruction. -/
theorem contDiffOn_joint_supportedResponse_nat
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K)
    (hO : IsOpen O) (hOL : O ⊆ L)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContDiff ℝ ∞ (B u))
    (hB : ∀ j : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests K, ∀ x ∈ L,
        ‖iteratedFDeriv ℝ j (B u) x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ)) (q : ℕ) :
    ContDiffOn ℝ q (fun z : Euclidean p × X ↦ B (f z.1) z.2) (U ×ˢ O) := by
  classical
  induction q generalizing G f with
  | zero =>
    obtain ⟨s, C, hC, hzero⟩ := hB 0
    have hb0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
        ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖ :=
      ⟨C, hC, by simpa only [norm_iteratedFDeriv_zero] using hzero⟩
    exact contDiffOn_zero.mpr (continuousOn_joint_response hU hK hOL B
      (fun u ↦ (hBreg u).continuous.continuousOn) s hb0 f hf)
  | succ q ih =>
    obtain ⟨s, C, hC, hzero⟩ := hB 0
    have hb0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests K, ∀ x ∈ L,
        ‖B u x‖ ≤ C * ‖ofTest s volume u.val‖ :=
      ⟨C, hC, by simpa only [norm_iteratedFDeriv_zero] using hzero⟩
    have hdx : ContDiffOn ℝ q
        (fun z : Euclidean p × X ↦ fderiv ℝ (B (f z.1)) z.2) (U ×ˢ O) := by
      apply ih (B := spatialResponseDerivative B hBreg)
        (hBreg := fun u ↦ (hBreg u).fderiv_right (m := ∞) (by simp))
        (f := f) (hf := hf)
      intro j
      obtain ⟨t, D, hD, hbound⟩ := hB (j + 1)
      exact ⟨t, D, hD, fun u x hx ↦ by
        simpa only [spatialResponseDerivative, LinearMap.coe_mk, AddHom.coe_mk,
          norm_iteratedFDeriv_fderiv] using hbound u x hx⟩
    have hdp : ContDiffOn ℝ q
        (fun z : Euclidean p × X ↦ fderiv ℝ (fun a ↦ B (f a) z.2) z.1) (U ×ˢ O) := by
      apply contDiffOn_clm_apply.mpr
      intro v
      let df : Euclidean p → supportedTests K := fun a ↦
        if ha : a ∈ U then supportedParameterTest hU hK f hf 1 (fun _ ↦ v) a ha else 0
      have hdf : ContDiffOn ℝ ∞ (fun z ↦ (df z.1).val.val z.2) (U ×ˢ univ) := by
        apply (contDiffOn_parameterField hU (f := fun a ↦ (f a).val.val) hf 1 (fun _ ↦ v)).congr
        intro z hz
        simp only [df, dite_eq_left hz.1, supportedParameterTest, parameterTest]
        rfl
      apply (ih (B := B) (hBreg := hBreg) (hB := hB) (f := df) (hf := hdf)).congr
      intro z hz
      have he := iteratedFDeriv_response_apply hU hK B
        (fun u ↦ (hBreg u).continuous.continuousOn) s hb0 f hf 1 (fun _ ↦ v)
        hz.1 (hOL hz.2)
      simpa only [iteratedFDeriv_one_apply, df, dite_eq_left hz.1] using he
    have hdparam (z : Euclidean p × X) (hz : z ∈ U ×ˢ O) :
        HasFDerivAt (fun a ↦ B (f a) z.2)
          (fderiv ℝ (fun a ↦ B (f a) z.2) z.1) z.1 := by
      have hh := (ContinuousMap.evalCLM ℝ (⟨z.2, hOL hz.2⟩ : L) (M := G)).contDiff.contDiffAt.comp z.1
        (contDiffAt_compactResponse hU hK B
          (fun u ↦ (hBreg u).continuous.continuousOn) s hb0 f hf 1 hz.1)
      exact (hh.differentiableAt (by norm_num)).hasFDerivAt
    let D := fun z : Euclidean p × X ↦
      (fderiv ℝ (fun a ↦ B (f a) z.2) z.1).coprod (fderiv ℝ (B (f z.1)) z.2)
    have hD : ContDiffOn ℝ q D (U ×ˢ O) := by
      apply ((hdp.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ _ _))).add
        (hdx.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ _ _)))).congr
      intro z _
      apply ContinuousLinearMap.ext
      intro v
      rfl
    have hd (z : Euclidean p × X) (hz : z ∈ U ×ˢ O) :
        HasFDerivAt (fun w : Euclidean p × X ↦ B (f w.1) w.2) (D z) z := by
      apply HasStrictFDerivAt.hasFDerivAt
      change HasStrictFDerivAt (fun w : Euclidean p × X ↦ B (f w.1) w.2)
        ((fderiv ℝ (fun a ↦ B (f a) z.2) z.1).coprod (fderiv ℝ (B (f z.1)) z.2)) z
      apply hasStrictFDerivAt_uncurry_coprod
        (f := fun a x ↦ B (f a) x)
        (f₁ := fun a x ↦ fderiv ℝ (fun c ↦ B (f c) x) a)
        (f₂ := fun a x ↦ fderiv ℝ (B (f a)) x)
      · filter_upwards [(hU.prod hO).mem_nhds hz] with w hw using hdparam w hw
      · exact Filter.Eventually.of_forall fun w ↦
          ((hBreg (f w.1)).differentiable (by simp) w.2).hasFDerivAt
      · exact hdp.continuousOn.continuousAt ((hU.prod hO).mem_nhds hz)
      · exact hdx.continuousOn.continuousAt ((hU.prod hO).mem_nhds hz)
    change ContDiffOn ℝ ((q : ℕ∞ω) + 1) _ _
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (hU.prod hO).uniqueDiffOn).mpr
      ⟨by simp, D, hD, fun z hz ↦ (hd z hz).hasFDerivWithinAt⟩

/-- One fixed smooth response is jointly smooth in the source parameters and
physical variables, from its all-order tame estimates and classical compact
source regularity (`app:ch_response:thm:response-literal-transfer`). This is an
independent implication; constructing the fixed inverse and these estimates
remains the upstream producer's obligation. -/
theorem contDiffOn_joint_supportedResponse
    {U : Set (Euclidean p)} (hU : IsOpen U) (hK : IsCompact K)
    (hO : IsOpen O) (hOL : O ⊆ L)
    (B : supportedTests K →ₗ[ℝ] (X → G)) (hBreg : ∀ u, ContDiff ℝ ∞ (B u))
    (hB : ∀ j : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests K, ∀ x ∈ L,
        ‖iteratedFDeriv ℝ j (B u) x‖ ≤ C * ‖ofTest s volume u.val‖)
    (f : Euclidean p → supportedTests K)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val.val z.2) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : Euclidean p × X ↦ B (f z.1) z.2) (U ×ˢ O) :=
  contDiffOn_infty.mpr fun q ↦
    contDiffOn_joint_supportedResponse_nat hU hK hO hOL B hBreg hB f hf q

end JanetCartan.ResponseSmoothParameters
