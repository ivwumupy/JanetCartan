module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Full
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.TransverseProjection

/-! # Uniform transverse perturbation

Projection of the literal full chart gives the transverse value and actual
η derivative comparison in `app:ch_seed:prop:seed-phase-charts`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The transverse value and actual direction derivative satisfy the same
phase `C⁴` perturbation bound as the full chart at common-time endpoints
(`app:ch_seed:prop:seed-phase-charts`). The constant is chosen before the phases. -/
theorem exists_transverseChart_perturbation_bound
    {ζ : P × ℝ → E} {P₀ : Set P} {B : Set (WithLp 2 (ℝ × E))} {I : Set ℝ} {J : Set E}
    {V : Set (P × ℝ)} {Ω K : Set ((WithLp 2 (ℝ × E)) × E)}
    {U : Set (P × ((WithLp 2 (ℝ × E)) × (WithLp 2 (ℝ × E))) × (ℝ × E))} {T : Set (WithLp 2 (ℝ × E))} {W : Set ℝ}
    (hP : IsCompact P₀) (hB : IsCompact B) (hBc : Convex ℝ B)
    (hI : IsCompact I) (hJ : IsCompact J)
    (hV : IsOpen V) (hPV : P₀ ×ˢ I ⊆ V) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hΩ : IsOpen Ω)
    (hU : IsOpen U) (hT : IsOpen T) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hQU : P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)) ⊆ U)
    (hproj : ∀ q ∈ U, (q.1, q.2.2.1) ∈ V)
    (hphys : ∀ q ∈ U, ∀ r ∈ W, q.2.1.2 + r • (q.2.1.1 - q.2.1.2) ∈ T)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hbuffer : ∀ ε, |ε| ≤ ε₀ → ∀ q ∈ U, ∀ y ∈ T, ∀ s ∈ W,
      (y, ζ (q.1, q.2.2.1) + (s * ε) • q.2.2.2) ∈ Ω)
    (hshift : ∀ ε, |ε| ≤ ε₀ → ∀ p ∈ P₀, ∀ x ∈ B, ∀ z ∈ I, ∀ η ∈ J,
      ∀ s ∈ Icc (0 : ℝ) 1, (x, ζ (p,z) + (s * ε) • η) ∈ K) :
    ∃ C > 0, ∀ S S₀ : WithLp 2 (ℝ × E) × E → ℝ,
      ContDiffOn ℝ ∞ S Ω → ContDiffOn ℝ ∞ S₀ Ω →
      ∀ ε, |ε| ≤ ε₀ → ∀ p ∈ P₀, ∀ t : ℝ, ∀ y y' : E,
      WithLp.toLp 2 (t,y) ∈ B → WithLp.toLp 2 (t,y') ∈ B →
      ∀ z ∈ I, ∀ η ∈ J,
        ‖transverseChart S ζ ε p t y y' (z,η) -
          transverseChart S₀ ζ ε p t y y' (z,η)‖ ≤ C * cNorm K 4 (S - S₀) ∧
        ‖fderiv ℝ (fun v ↦ transverseChart S ζ ε p t y y' (z,v)) η -
          fderiv ℝ (fun v ↦ transverseChart S₀ ζ ε p t y y' (z,v)) η‖ ≤
          C * cNorm K 4 (S - S₀) := by
  obtain ⟨C, hC, hb⟩ := exists_fullChart_perturbation_bound
    hP hB hBc hI hJ hV hPV hζ hK hKΩ hΩ hU hT hW hIW hQU hproj hphys hε₀ hbuffer hshift
  refine ⟨C, hC, ?_⟩
  intro S S₀ hS hS₀ ε hε p hp t y y' hy hy' z hz η hη
  obtain ⟨hc, hc₀, hb⟩ := hb S S₀ hS hS₀ ε hε
  let x := WithLp.toLp 2 (t,y)
  let x' := WithLp.toLp 2 (t,y')
  let q := (p, (x,x'), (z,η))
  have hq : q ∈ P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)) := ⟨hp, ⟨hy,hy'⟩, hz,hη⟩
  let D := {u : ℝ × E | (p,(x,x'),u) ∈ U}
  have hD : IsOpen D := hU.preimage (by fun_prop)
  have hu : (z,η) ∈ D := hQU hq
  have hζD : ContDiffOn ℝ ∞ (fun u : ℝ × E ↦ ζ (p,u.1)) D :=
    hζ.comp (contDiffOn_const.prodMk contDiffOn_fst) (fun u hu ↦ hproj _ hu)
  have hsh : ∀ u ∈ D, ∀ b ∈ T, ∀ s ∈ W,
      (b, ζ (p,u.1) + (s * ε) • u.2) ∈ Ω :=
    fun u hu b hb s hs ↦ hbuffer ε hε (p,(x,x'),u) hu b hb s hs
  have hseg : ∀ r ∈ W, WithLp.toLp 2 (t,y' + r • (y-y')) ∈ T := by
    intro r hr
    have heq : WithLp.toLp 2 (t,y' + r • (y-y')) = x' + r • (x-x') := by
      apply WithLp.ofLp_injective
      simp [x,x']
    rw [heq]
    exact hphys q (hQU hq) r hr
  have he (F : WithLp 2 (ℝ × E) × E → ℝ) (hF : ContDiffOn ℝ ∞ F Ω)
      (u : ℝ × E) (hu : u ∈ D) :
      transverseChart F ζ ε p t y y' u = (fullChart F ζ ε p x x' u).2 :=
    transverseChart_eq_fullChart_snd hD hT hΩ hW hIW hF hζD hsh
      (fun r hr ↦ hseg r (hIW hr)) hu
  have hd : DifferentiableAt ℝ (fullChart S ζ ε p x x') (z,η) :=
    ((hc.contDiffAt (hU.mem_nhds (hQU hq))).comp (z,η)
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hd₀ : DifferentiableAt ℝ (fullChart S₀ ζ ε p x x') (z,η) :=
    ((hc₀.contDiffAt (hU.mem_nhds (hQU hq))).comp (z,η)
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hevent (F : WithLp 2 (ℝ × E) × E → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :
      (fun v ↦ transverseChart F ζ ε p t y y' (z,v)) =ᶠ[𝓝 η]
        (fun v ↦ (fullChart F ζ ε p x x' (z,v)).2) := by
    have hev : ∀ᶠ v in 𝓝 η, (z,v) ∈ D :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually (hD.mem_nhds hu)
    filter_upwards [hev] with v hv
    exact he F hF (z,v) hv
  constructor
  · rw [he S hS (z,η) hu, he S₀ hS₀ (z,η) hu]
    exact (norm_snd_le (fullChart S ζ ε p x x' (z,η) -
      fullChart S₀ ζ ε p x x' (z,η))).trans (hb q hq).1
  · rw [(hevent S hS).fderiv_eq, (hevent S₀ hS₀).fderiv_eq]
    have hi : HasFDerivAt (fun v : E ↦ (z,v)) (ContinuousLinearMap.inr ℝ ℝ E) η := by
      convert (hasFDerivAt_const (𝕜 := ℝ) z η).prodMk (hasFDerivAt_id (𝕜 := ℝ) η) using 1 <;> rfl
    have hni : ‖fderiv ℝ (fun v : E ↦ (z,v)) η‖ ≤ 1 := by
      rw [hi.fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro v
      simp
    exact (norm_fderiv_chart_restriction_sub_le hd hd₀ hi.differentiableAt hni
      (ContinuousLinearMap.snd ℝ ℝ E) (ContinuousLinearMap.norm_snd_le ..)).trans (hb q hq).2.2

end JanetCartan.FullPhaseCharts.Comparison
