module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.ReferenceJoint

/-!
# Uniform C¹ comparison of the literal full phase charts

This proves the comparison paragraph following
`app:ch_seed:eq:seed-quotient-integral`. For each positive tolerance, positive
phase-error and shift thresholds are chosen before the perturbed phase. The
literal full chart is close to `frozenChart` in value, its full joint derivative
in `(p,x,x',z,η)`, and its data derivative. The transverse chart is close to the
identity in value and its actual direction derivative.

The inputs are local smoothness, compact convex physical boxes, compact data
and spectator boxes, and explicit open buffers and shifted-segment containment.
`Ωξ` is the reference Hamiltonian's local covector domain, `R` is its open
spectator/data buffer, and `L` is its open shift buffer. No chart-error input is
assumed. The integral differentiation and phase-jet estimates are supplied by
`Perturbation`; `ReferenceLimit` supplies compact uniform reference convergence.

The Hamilton phase and actual-carrier producers must construct the smooth
phase/carrier, instantiate these geometric buffers, and prove the phase's
`cNorm K 4` error. The consumer `jc-full-phase-charts` retains those obligations;
this conditional comparison does not assert unconditional phase existence or
vanishing of epsilon derivatives.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

private theorem norm_sub_lt_of_half_errors
    {F : Type*} [SeminormedAddCommGroup F] {a b c : F} {τ : ℝ}
    (hab : ‖a - b‖ < τ / 2) (hbc : ‖b - c‖ < τ / 2) : ‖a - c‖ < τ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _
    _ < τ / 2 + τ / 2 := add_lt_add hab hbc
    _ = τ := by ring

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform finite-jet comparison for the literal quotient and its two-point
averaged gradients in `app:ch_seed:prop:seed-phase-charts`. The constants `δ`
and `εStar` precede the choice of `S`. The frozen velocity is exactly
`gradient H` composed with the fixed carrier; all physical and spectator
variables remain in the joint differential. Every hypothesis concerns fixed
geometry, local smoothness, or the phase `C⁴` error, never chart closeness.
The phase/carrier producers and `jc-full-phase-charts` must instantiate them. -/
theorem exists_phaseCharts_c1_comparison
    {H : E → ℝ} {ζ : P × ℝ → E}
    {P₀ : Set P} {B : Set (WithLp 2 (ℝ × E))} {I : Set ℝ} {J : Set E}
    {V : Set (P × ℝ)} {Ω K : Set (WithLp 2 (ℝ × E) × E)}
    {U : Set (P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E))}
    {T : Set (WithLp 2 (ℝ × E))} {W : Set ℝ}
    {Ωξ : Set E} {R : Set (P × (ℝ × E))} {L : Set ℝ}
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
      ∀ s ∈ Icc (0 : ℝ) 1, (x, ζ (p,z) + (s * ε) • η) ∈ K)
    (hΩξ : IsOpen Ωξ) (hΩproj : ∀ q ∈ Ω, q.2 ∈ Ωξ)
    (hH : ContDiffOn ℝ ∞ H Ωξ)
    (hR : IsOpen R) (hQR : P₀ ×ˢ (I ×ˢ J) ⊆ R)
    (hRproj : ∀ q ∈ R, (q.1, q.2.1) ∈ V)
    (hL : IsOpen L) (hεL : ∀ ε, |ε| ≤ ε₀ → ε ∈ L)
    (hRshift : ∀ q ∈ R, ∀ ε ∈ L, ∀ s ∈ W,
      ζ (q.1, q.2.1) + (s * ε) • q.2.2 ∈ Ωξ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > 0, ∃ εStar > 0, εStar ≤ ε₀ ∧
      ∀ S : WithLp 2 (ℝ × E) × E → ℝ, ContDiffOn ℝ ∞ S Ω →
      cNorm K 4 (S - referencePhase H) < δ → ∀ ε, |ε| ≤ εStar →
      (∀ q ∈ P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)),
        ‖fullChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2 -
          frozenChart (fun z ↦ gradient H (ζ (q.1,z))) q.2.2‖ < τ ∧
        ‖fderiv ℝ (fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
            fullChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q -
          fderiv ℝ (fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
            frozenChart (fun z ↦ gradient H (ζ (a.1,z))) a.2.2) q‖ < τ ∧
        ‖fderiv ℝ (fullChart S ζ ε q.1 q.2.1.1 q.2.1.2) q.2.2 -
          fderiv ℝ (frozenChart (fun z ↦ gradient H (ζ (q.1,z)))) q.2.2‖ < τ) ∧
      (∀ p ∈ P₀, ∀ t : ℝ, ∀ y y' : E,
        WithLp.toLp 2 (t,y) ∈ B → WithLp.toLp 2 (t,y') ∈ B →
        ∀ z ∈ I, ∀ η ∈ J,
        ‖transverseChart S ζ ε p t y y' (z,η) - η‖ < τ ∧
        ‖fderiv ℝ (fun v ↦ transverseChart S ζ ε p t y y' (z,v)) η -
          ContinuousLinearMap.id ℝ E‖ < τ) := by
  obtain ⟨C, hC, hfull⟩ := exists_fullChart_perturbation_bound
    hP hB hBc hI hJ hV hPV hζ hK hKΩ hΩ hU hT hW hIW hQU hproj hphys hε₀ hbuffer hshift
  obtain ⟨D, hD, htrans⟩ := exists_transverseChart_perturbation_bound
    hP hB hBc hI hJ hV hPV hζ hK hKΩ hΩ hU hT hW hIW hQU hproj hphys hε₀ hbuffer hshift
  have h0 : (0 : ℝ) ∈ L := hεL 0 (by simpa using hε₀.le)
  obtain ⟨εStar, hstar, hstar₀, href⟩ := exists_fullChart_reference_c1_radius
    (hP.prod (hI.prod hJ)) hQR hR hΩξ hL h0 hW hIW hH hζ hRproj hRshift hε₀ (half_pos hτ)
  refine ⟨min ((τ / 2) / C) ((τ / 2) / D),
    lt_min (div_pos (half_pos hτ) hC) (div_pos (half_pos hτ) hD),
    εStar, hstar, hstar₀, ?_⟩
  intro S hS hsmall ε hε
  have hε₀' := hε.trans hstar₀
  have hS₀ := contDiffOn_referencePhase hH hΩproj
  have hsmallC : C * cNorm K 4 (S - referencePhase H) < τ / 2 := by
    have := (lt_div_iff₀ hC).mp (hsmall.trans_le (min_le_left _ _))
    simpa only [mul_comm] using this
  have hsmallD : D * cNorm K 4 (S - referencePhase H) < τ / 2 := by
    have := (lt_div_iff₀ hD).mp (hsmall.trans_le (min_le_right _ _))
    simpa only [mul_comm] using this
  obtain ⟨_, _, hb⟩ := hfull S (referencePhase H) hS hS₀ ε hε₀'
  constructor
  · intro q hq
    have hqd : (q.1, q.2.2) ∈ P₀ ×ˢ (I ×ˢ J) := ⟨hq.1, hq.2.2⟩
    have hr := href ε hε (q.1,q.2.2) hqd q.2.1.1 q.2.1.2
    have hr₀ := href ε hε (q.1,q.2.2) hqd 0 0
    have hj := norm_fderiv_reference_joint_sub_le hR hΩξ hL h0 hW hIW hH hζ
      hRproj hRshift (hεL ε hε₀') q (hQR hqd)
    exact ⟨norm_sub_lt_of_half_errors (F := ℝ × E) ((hb q hq).1.trans_lt hsmallC) hr.1,
      norm_sub_lt_of_half_errors
        (F := (P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E)) →L[ℝ] ℝ × E)
        ((hb q hq).2.1.trans_lt hsmallC) (hj.trans_lt hr₀.2.1),
      norm_sub_lt_of_half_errors (F := (ℝ × E) →L[ℝ] ℝ × E) ((hb q hq).2.2.trans_lt hsmallC) hr.2.2⟩
  · intro p hp t y y' hy hy' z hz η hη
    have hb := htrans S (referencePhase H) hS hS₀ ε hε₀' p hp t y y' hy hy' z hz η hη
    let O := {v : E | (p,z,v) ∈ R}
    have hO : IsOpen O := hR.preimage (by fun_prop)
    have hηO : η ∈ O := hQR ⟨hp,hz,hη⟩
    have hreg (v : E) (hv : v ∈ O) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        ContDiffAt ℝ 1 H (ζ (p,z) + (s * ε) • v) :=
      (hH.contDiffAt (hΩξ.mem_nhds
        (hRshift (p,z,v) hv ε (hεL ε hε₀') s (hIW hs)))).of_le (by simp)
    rw [transverseChart_reference_shift ζ p (z,η) ε (hreg η hηO) t y y',
      fderiv_transverseChart_reference_shift hO hηO p z ε hreg t y y'] at hb
    exact ⟨hb.1.trans_lt (hsmallD.trans (half_lt_self hτ)),
      hb.2.trans_lt (hsmallD.trans (half_lt_self hτ))⟩

end JanetCartan.FullPhaseCharts.Comparison
