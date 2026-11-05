module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.ReferenceLimit.Smooth
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform C¹ reference limit

The reference part of the comparison after `app:ch_seed:eq:seed-quotient-integral`
is proved for the literal `fullChart`. Joint smoothness of the integral quotient
and compact uniform continuity control values, the joint `(p,z,η)` differential,
and the actual `(z,η)` data differential. Epsilon derivatives are not claimed to
vanish. The bound is independent of both physical endpoints.

`U`, `V`, `L`, and `W` are explicit open buffers: the carrier is smooth on `V`,
all shifted covectors lie in the open smoothness domain `Ω`, and `W` contains
`[0,1]`. No global smoothness or chart-error assumption is used. A compact box
`P₀ × (I × J)` is obtained by taking `K` to be that product. The construction of
these buffers belongs to the phase/carrier producer; the parent comparison task
combines this reference limit with its independent phase perturbation estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

private theorem exists_uniform_reference_radius
    {A B : Type*} [TopologicalSpace A] [NormedAddCommGroup B]
    {K : Set A} {L : Set ℝ} {f : A × ℝ → B}
    (hK : IsCompact K) (hL : IsOpen L) (h0 : (0 : ℝ) ∈ L)
    (hf : ContinuousOn f (K ×ˢ L)) {ε₀ τ : ℝ} (hε₀ : 0 < ε₀) (hτ : 0 < τ) :
    ∃ r > 0, r ≤ ε₀ ∧ ∀ ε, |ε| ≤ r →
      ε ∈ L ∧ ∀ q ∈ K, ‖f (q, ε) - f (q, 0)‖ < τ := by
  have hc : ContinuousOn (Function.uncurry (fun ε q ↦ f (q, ε))) (L ×ˢ K) :=
    hf.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun _ h ↦ ⟨h.2, h.1⟩)
  obtain ⟨v, hv, hclose⟩ := hK.mem_uniformity_of_prod hc h0 (Metric.dist_mem_uniformity hτ)
  rw [nhdsWithin_eq_nhds.mpr (hL.mem_nhds h0)] at hv
  obtain ⟨r, hr, hrv⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hv (hL.mem_nhds h0))
  refine ⟨min ε₀ r, lt_min hε₀ hr, min_le_left _ _, ?_⟩
  intro ε hε
  have he : ε ∈ Metric.closedBall 0 r := by
    simpa using hε.trans (min_le_right ε₀ r)
  exact ⟨(hrv he).2, fun q hq ↦ by
    simpa only [mem_ofPred_eq, dist_eq_norm] using hclose ε (hrv he).1 q hq⟩

variable {P E : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E → ℝ} {ζ : P × ℝ → E}
  {K U : Set (P × (ℝ × E))} {V : Set (P × ℝ)} {Ω : Set E} {L W : Set ℝ}

/-- The uniform reference estimate used by `jc-deduce-full-phase-jet-comparison`
for `app:ch_seed:prop:seed-phase-charts`. For any tolerance, one positive
`εStar ≤ ε₀` controls values and both actual Fréchet differentials on the whole
compact spectator/data set, for all physical endpoints. The hypotheses are
local smoothness and buffered shifted-segment containment, not chart convergence.
The joint differential retains all spectator variables. -/
theorem exists_fullChart_reference_c1_radius
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hL : IsOpen L) (h0 : (0 : ℝ) ∈ L)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hH : ContDiffOn ℝ ∞ H Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.1) ∈ V)
    (hshift : ∀ q ∈ U, ∀ ε ∈ L, ∀ s ∈ W,
      ζ (q.1, q.2.1) + (s * ε) • q.2.2 ∈ Ω)
    {ε₀ τ : ℝ} (hε₀ : 0 < ε₀) (hτ : 0 < τ) :
    ∃ εStar > 0, εStar ≤ ε₀ ∧ ∀ ε, |ε| ≤ εStar → ∀ q ∈ K,
      ∀ x x' : WithLp 2 (ℝ × E),
      ‖fullChart (referencePhase H) ζ ε q.1 x x' q.2 -
        frozenChart (fun z ↦ gradient H (ζ (q.1, z))) q.2‖ < τ ∧
      ‖fderiv ℝ (fun a : P × (ℝ × E) ↦
          fullChart (referencePhase H) ζ ε a.1 x x' a.2) q -
        fderiv ℝ (fun a : P × (ℝ × E) ↦
          frozenChart (fun z ↦ gradient H (ζ (a.1, z))) a.2) q‖ < τ ∧
      ‖fderiv ℝ (fullChart (referencePhase H) ζ ε q.1 x x') q.2 -
        fderiv ℝ (frozenChart (fun z ↦ gradient H (ζ (q.1, z)))) q.2‖ < τ := by
  let F : ℝ → (P × (ℝ × E)) → ℝ × E := fun ε q ↦
    fullChart (referencePhase H) ζ ε q.1 0 0 q.2
  let G : (P × (ℝ × E)) → ℝ × E := fun q ↦
    frozenChart (fun z ↦ gradient H (ζ (q.1, z))) q.2
  have hF : ContDiffOn ℝ ∞ (fun a : (P × (ℝ × E)) × ℝ ↦ F a.2 a.1) (U ×ˢ L) :=
    contDiffOn_fullChart_reference hU hΩ hL hW hIW hH hζ hproj hshift 0 0
  have hDF := contDiffOn_parameterFDeriv hU hL hF
  have hdata : ContDiffOn ℝ ∞ (fun a : (P × (ℝ × E)) × ℝ ↦
      fderiv ℝ (fun u ↦ F a.2 (a.1.1, u)) a.1.2) (U ×ˢ L) := by
    intro a ha
    have hat := hF.contDiffAt ((hU.prod hL).mem_nhds ha)
    have hg : ContDiffAt ℝ ∞
        (fun b : ((P × (ℝ × E)) × ℝ) × (ℝ × E) ↦
          F b.1.2 (b.1.1.1, b.2)) (a, a.1.2) :=
      hat.comp (a, a.1.2)
        (f := fun b : ((P × (ℝ × E)) × ℝ) × (ℝ × E) ↦
          ((b.1.1.1, b.2), b.1.2))
        ((contDiffAt_fst.fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
    exact (hg.fderiv contDiffAt_fst.snd (by simp)).contDiffWithinAt
  let jet := fun a : (P × (ℝ × E)) × ℝ ↦
    (F a.2 a.1, fderiv ℝ (F a.2) a.1,
      fderiv ℝ (fun u ↦ F a.2 (a.1.1, u)) a.1.2)
  have hjet : ContinuousOn jet (K ×ˢ L) :=
    (hF.continuousOn.prodMk (hDF.continuousOn.prodMk hdata.continuousOn)).mono
      (prod_mono hKU Subset.rfl)
  obtain ⟨r, hr, hrε, hb⟩ := exists_uniform_reference_radius (f := jet) hK hL h0 hjet hε₀ hτ
  refine ⟨r, hr, hrε, ?_⟩
  intro ε hε q hq x x'
  obtain ⟨hεL, hbε⟩ := hb ε hε
  have hj := hbε q hq
  change max ‖F ε q - F 0 q‖
    (max ‖fderiv ℝ (F ε) q - fderiv ℝ (F 0) q‖
      ‖fderiv ℝ (fun u ↦ F ε (q.1, u)) q.2 -
        fderiv ℝ (fun u ↦ F 0 (q.1, u)) q.2‖) < τ at hj
  rcases max_lt_iff.mp hj with ⟨hval, hj⟩
  rcases max_lt_iff.mp hj with ⟨hjoint, hdat⟩
  have hreg (a : P × (ℝ × E)) (ha : a ∈ U) (e : ℝ) (he : e ∈ L)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 H (ζ (a.1, a.2.1) + (s * e) • a.2.2) :=
    (hH.contDiffAt (hΩ.mem_nhds (hshift a ha e he s (hIW hs)))).of_le (by simp)
  have heq : EqOn (fun a : P × (ℝ × E) ↦
      fullChart (referencePhase H) ζ ε a.1 x x' a.2) (F ε) U := by
    intro a ha
    exact (fullChart_reference_shift ζ a.1 a.2 ε (hreg a ha ε hεL) x x').trans
      (fullChart_reference_shift ζ a.1 a.2 ε (hreg a ha ε hεL) 0 0).symm
  have hzero : EqOn (F 0) G U := by
    intro a ha
    apply fullChart_reference_zero
    have hd := (hreg a ha 0 h0 0 (by simp)).differentiableAt one_ne_zero
    simpa using hd
  have heqN : (fun a : P × (ℝ × E) ↦
      fullChart (referencePhase H) ζ ε a.1 x x' a.2) =ᶠ[𝓝 q] F ε := by
    filter_upwards [hU.mem_nhds (hKU hq)] with a ha using heq ha
  have hzN : F 0 =ᶠ[𝓝 q] G := by
    filter_upwards [hU.mem_nhds (hKU hq)] with a ha using hzero ha
  have hslice : {u : ℝ × E | (q.1, u) ∈ U} ∈ 𝓝 q.2 :=
    (hU.preimage (show Continuous (fun u : ℝ × E ↦ (q.1, u)) from
      continuous_const.prodMk continuous_id)).mem_nhds (hKU hq)
  have heqD : fullChart (referencePhase H) ζ ε q.1 x x'
      =ᶠ[𝓝 q.2] (fun u ↦ F ε (q.1, u)) := by
    filter_upwards [hslice] with u hu using @heq (q.1, u) hu
  have hzD : (fun u ↦ F 0 (q.1, u)) =ᶠ[𝓝 q.2]
      frozenChart (fun z ↦ gradient H (ζ (q.1, z))) := by
    filter_upwards [hslice] with u hu using @hzero (q.1, u) hu
  refine ⟨?_, ?_, ?_⟩
  · have hv : fullChart (referencePhase H) ζ ε q.1 x x' q.2 = F ε q := heq (hKU hq)
    change ‖fullChart (referencePhase H) ζ ε q.1 x x' q.2 - G q‖ < τ
    rw [hv, ← hzero (hKU hq)]
    exact hval
  · rw [heqN.fderiv_eq, ← hzN.fderiv_eq]
    exact hjoint
  · rw [heqD.fderiv_eq, ← hzD.fderiv_eq]
    exact hdat

end JanetCartan.FullPhaseCharts.Comparison
