module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.CriticalHessian

/-!
# A local uniform gap for every averaged carrier Hessian

For `app:ch_response:lem:energy-carrier-jets`, continuity near the constructed
invertible diagonal Hessian gives one convex neighborhood on which EVERY
segment average is invertible, with a common inverse norm bound. Pointwise
invertibility alone would not imply this assertion. The local primary
construction supplies the smooth literal phase and its diagonal invertibility.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.CompatibleResponse
open ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint continuity of the carrier Hessian, obtained by taking two actual
integration-variable derivatives of the joint phase
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffAt_joint_carrierHessian
    {f : E → CarrierVariables n → ℝ} {q : E} {w : CarrierVariables n}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q, w)) :
    ContDiffAt ℝ 1
      (fun v : E × CarrierVariables n ↦ fderiv ℝ (gradient (f v.1)) v.2) (q, w) := by
  have hd : ContDiffAt ℝ 2
      (fun v : E × CarrierVariables n ↦ fderiv ℝ (f v.1) v.2) (q, w) :=
    (hf.comp ((q, w), w) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
      contDiffAt_snd (by simp)
  have hg : ContDiffAt ℝ 2
      (fun v : E × CarrierVariables n ↦ gradient (f v.1) v.2) (q, w) :=
    (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
      (q, w) hd
  exact (hg.comp ((q, w), w) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
    contDiffAt_snd (by norm_num)

/-- Construct a common inverse bound for all segment averages of the SAME
carrier Hessian near an invertible diagonal point. The radius and bound are
chosen before the external variable and BOTH segment endpoints. This is the
local averaged-Hessian input of `new:eq:carrier-ibp`, with no assumed averaged
inverse or desired norm estimate. -/
theorem exists_local_averaged_carrierHessian_gap
    {f : E → CarrierVariables n → ℝ} {q₀ : E} {w₀ : CarrierVariables n}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q₀, w₀))
    (hi : IsUnit (fderiv ℝ (gradient (f q₀)) w₀)) :
    ∃ ρ > (0 : ℝ), ∃ M > (0 : ℝ),
      ∀ q ∈ ball q₀ ρ, ∀ a ∈ ball w₀ ρ, ∀ b ∈ ball w₀ ρ,
        let H := ∫ t in (0 : ℝ)..1, fderiv ℝ (gradient (f q)) (a + t • (b - a))
        IsUnit H ∧ ‖Ring.inverse H‖ ≤ M := by
  let H := fun v : E × CarrierVariables n ↦ fderiv ℝ (gradient (f v.1)) v.2
  let A := H (q₀, w₀)
  have hH : ContDiffAt ℝ 1 H (q₀, w₀) := contDiffAt_joint_carrierHessian hf
  have hi' : IsUnit A := hi
  obtain ⟨u, hu⟩ := hi
  have hu' : (u : CarrierVariables n →L[ℝ] CarrierVariables n) = A := hu
  have hgood : ∀ᶠ L in 𝓝 A, IsUnit L ∧ ‖Ring.inverse L‖ < ‖Ring.inverse A‖ + 1 := by
    have hinv : ContinuousAt Ring.inverse A := hu' ▸ NormedRing.inverse_continuousAt u
    exact Filter.Eventually.and (Units.isOpen.mem_nhds hi')
      (hinv.norm.eventually_lt_const (by linarith))
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  have hnear : ∀ᶠ v in 𝓝 (q₀, w₀),
      ‖H v - A‖ < ε / 2 ∧ ContinuousAt H v := by
    have he := hH.continuousAt.preimage_mem_nhds (ball_mem_nhds A (by positivity : 0 < ε / 2))
    filter_upwards [he, hH.eventually (by norm_num)] with v hv hv'
    exact ⟨by simpa only [mem_preimage, mem_ball, dist_eq_norm] using hv, hv'.continuousAt⟩
  obtain ⟨ρ, hρ, hr⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ρ, hρ, ‖Ring.inverse A‖ + 1, by positivity, ?_⟩
  intro q hq a ha b hb
  have hseg t (ht : t ∈ uIcc (0 : ℝ) 1) : a + t • (b - a) ∈ ball w₀ ρ :=
    (convex_ball w₀ ρ).add_smul_sub_mem ha hb (by simpa using ht)
  have hmem t (ht : t ∈ uIcc (0 : ℝ) 1) : (q, a + t • (b - a)) ∈ ball (q₀, w₀) ρ := by
    rw [← ball_prod_same]
    exact ⟨hq, hseg t ht⟩
  have hpath : Continuous (fun t : ℝ ↦ (q, a + t • (b - a))) := by fun_prop
  have hc : ContinuousOn (fun t : ℝ ↦ H (q, a + t • (b - a))) (uIcc 0 1) := by
    intro t ht
    have hcH : ContinuousAt H (q, a + t • (b - a)) := (hr (hmem t ht)).2
    exact (hcH.comp (x := t) (f := fun u : ℝ ↦ (q, a + u • (b - a))) hpath.continuousAt).continuousWithinAt
  have hd : (∫ t in (0 : ℝ)..1, H (q, a + t • (b - a))) - A =
      ∫ t in (0 : ℝ)..1, H (q, a + t • (b - a)) - A := by
    rw [intervalIntegral.integral_sub hc.intervalIntegrable intervalIntegrable_const]
    simp
  have hbound : ‖(∫ t in (0 : ℝ)..1, H (q, a + t • (b - a))) - A‖ ≤ ε / 2 := by
    rw [hd]
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun t ht ↦ (hr (hmem t (uIoc_subset_uIcc ht))).1.le)
  have hunit := heps (show (∫ t in (0 : ℝ)..1, H (q, a + t • (b - a))) ∈ ball A ε by
    rw [mem_ball, dist_eq_norm]
    exact hbound.trans_lt (by linarith))
  exact ⟨hunit.1, hunit.2.le⟩

end JanetCartan.CompatibleResponse
