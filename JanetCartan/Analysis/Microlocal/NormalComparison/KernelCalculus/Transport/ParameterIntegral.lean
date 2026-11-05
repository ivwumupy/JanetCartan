module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport.CompactSupport

/-!
# Differentiation with a common compact carrier

Differentiation under the original input integral in
`app:ch_osc:prop:osc-normal`, before integration by parts.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.NormalComparison.CompactTransport

variable {n : ℕ} {U : Set ℝ} {D S : Set (Euclidean n)}
  {f : ℝ × Euclidean n → ℂ}

/-- The parameter derivative vanishes outside a common carrier, using an open
parameter neighborhood (`app:ch_osc:prop:osc-normal`). -/
theorem deriv_eq_zero_off_carrier (hU : IsOpen U)
    (hs : ∀ t ∈ U, ∀ u ∉ S, f (t, u) = 0) {s : ℝ} (hsU : s ∈ U)
    {u : Euclidean n} (hu : u ∉ S) : deriv (fun t ↦ f (t, u)) s = 0 := by
  have he : (fun t ↦ f (t, u)) =ᶠ[𝓝 s] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hsU] with t ht using hs t ht u hu
  rw [he.deriv_eq]
  simp

/-- Differentiation under an integral with compact support inside an open input
domain. All domination and integrability follow from joint smoothness and the
common compact carrier (`app:ch_osc:prop:osc-normal`). -/
theorem hasDerivAt_integral_carrier (hU : IsOpen U) (hD : IsOpen D)
    (hS : IsCompact S) (hSD : S ⊆ D)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ D))
    (hs : ∀ t ∈ U, ∀ u ∉ S, f (t, u) = 0) {s : ℝ} (hsU : s ∈ U) :
    HasDerivAt (fun t ↦ ∫ u in D, f (t, u))
      (∫ u in D, deriv (fun t ↦ f (t, u)) s) s := by
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top (μ := volume)⟩
  have hd := (hasFDerivAt_compactParameterIntegral hU hD hS hSD hf hsU
    (μ := volume)).hasDerivAt
  rw [ContinuousLinearMap.integral_apply
    (integrableOn_parameterFDeriv hU hD hS hSD hf hsU)] at hd
  change HasDerivAt (fun t ↦ ∫ u in S, f (t, u))
    (∫ u in S, deriv (fun t ↦ f (t, u)) s) s at hd
  have hzero (u : Euclidean n) (hu : u ∉ S) : deriv (fun t ↦ f (t, u)) s = 0 :=
    deriv_eq_zero_off_carrier hU hs hsU hu
  have he : (∫ u in S, deriv (fun t ↦ f (t, u)) s) =
      ∫ u in D, deriv (fun t ↦ f (t, u)) s := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦ hzero u hu),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦
        hzero u (fun h ↦ hu (hSD h)))]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hsU] with t ht
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦
      hs t ht u (fun h ↦ hu (hSD h))),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hs t ht)]

end JanetCartan.NormalComparison.CompactTransport
