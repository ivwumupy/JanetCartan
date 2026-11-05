module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Compact finite norms of smooth normalized slices

The compactness step in `app:ch_background:prop:bg-normalized` and
`paper-v2.tex`, `new:lem:scaling`. Consumers are the source phase differential
and geometric coefficients in `FamilyInputs.NormalizedTransport` and
`FamilyInputs.NormalizedCoefficients`. The compact set is contained in a fixed
open buffer, and all derivatives are ambient derivatives. No continuity of
inverses, amplitudes or operators is assumed here.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_slice {f : P × E → F} {I : Set P} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (I ×ˢ U))
    {p : P} (hp : p ∈ I) {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y ↦ f (p, y)) x =
      (iteratedFDeriv ℝ j f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let V := (fun y : P × E ↦ y + (p, 0)) ⁻¹' (I ×ˢ U)
  have hV : IsOpen V := (hI.prod hU).preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ (fun y ↦ f (y + (p, 0))) V :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy ↦ hy)
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hxV : L x ∈ V := by simpa [L, V] using And.intro hp hx
  have he := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn
    hxV (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hxV,
    iteratedFDerivWithin_of_isOpen _ hV hxV, iteratedFDeriv_comp_add_right] at he
  simpa [L, Function.comp_def] using he

private theorem continuousOn_slice_jets {f : P × E → F} {I : Set P} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) (j : ℕ) :
    ContinuousOn (fun q : P × E ↦ iteratedFDeriv ℝ j (fun y ↦ f (q.1, y)) q.2)
      (I ×ˢ U) := by
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j ↦ ContinuousLinearMap.inr ℝ P E) (F := F)).continuous.comp_continuousOn
      (ContinuousOn.continuousOn_iteratedFDeriv hf (hI.prod hU) (by simp : (j : ℕ∞ω) ≤ ∞))
  exact hc.congr (fun q hq ↦ iteratedFDeriv_slice hI hU hf hq.1 hq.2 j)

/-- Joint smoothness on a fixed open parameter/coordinate box implies
convergence of each finite ambient `cNorm` on its compact inner coordinate set.
This applies both at scale zero and at a fixed positive scale. The buffer is
fixed before the derivative order. Source: `app:ch_background:prop:bg-normalized`
and `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the limit `σ = 0`. -/
theorem tendsto_cNorm_slice_sub {f : P × E → F} {I : Set P} {U K : Set E}
    (hI : IsOpen I) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (I ×ˢ U))
    (hK : IsCompact K) (hKU : K ⊆ U) {p₀ : P} (hp₀ : p₀ ∈ I) (m : ℕ) :
    Tendsto (fun p ↦ cNorm K m ((fun x ↦ f (p, x)) - (fun x ↦ f (p₀, x))))
      (𝓝 p₀) (𝓝 0) := by
  have hs (p : P) (hp : p ∈ I) : ContDiffOn ℝ ∞ (fun x ↦ f (p, x)) U :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨hp, hx⟩)
  have hsup (j : ℕ) :
      Tendsto (fun p ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j
        ((fun y ↦ f (p, y)) - (fun y ↦ f (p₀, y))) x‖) '' K))
        (𝓝 p₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have he : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun y ↦ f (p, y)) x -
          iteratedFDeriv ℝ j (fun y ↦ f (p₀, y)) x‖ < ε / 2 := by
      apply hK.eventually_forall_of_forall_eventually
      intro x hx
      have hc : ContinuousAt (fun q : P × E ↦
          iteratedFDeriv ℝ j (fun y ↦ f (q.1, y)) q.2) (p₀, x) :=
        (continuousOn_slice_jets hI hU hf j).continuousAt
        ((hI.prod hU).mem_nhds ⟨hp₀, hKU hx⟩)
      have hfix : ContinuousAt
          (fun q : P × E ↦ iteratedFDeriv ℝ j (fun y ↦ f (p₀, y)) q.2) (p₀, x) :=
        hc.comp (g := fun q : P × E ↦ iteratedFDeriv ℝ j (fun y ↦ f (q.1, y)) q.2)
          (f := fun q : P × E ↦ (p₀, q.2)) (show ContinuousAt (fun q : P × E ↦ (p₀, q.2)) (p₀, x) from
          (continuous_const.prodMk continuous_snd).continuousAt)
      have hz := (hc.sub hfix).norm
      simpa using hz.eventually (gt_mem_nhds (by simpa using half_pos hε))
    filter_upwards [he, hI.mem_nhds hp₀] with p hp hpI
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sSup_norm_iteratedFDeriv_nonneg _ _ _)]
    apply lt_of_le_of_lt ?_ (half_lt_self hε)
    apply Real.sSup_le _ (half_pos hε).le
    rintro _ ⟨x, hx, rfl⟩
    change ‖iteratedFDeriv ℝ j ((fun y ↦ f (p, y)) - (fun y ↦ f (p₀, y))) x‖ ≤ ε / 2
    rw [iteratedFDeriv_sub_apply
      (((hs p hpI).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
      (((hs p₀ hp₀).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp : (j : ℕ∞ω) ≤ ∞))]
    exact (hp x hx).le
  simpa only [cNorm, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range (m + 1)) (fun j _ ↦ hsup j)
end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
