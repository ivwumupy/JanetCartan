module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.IntegralModel
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Joint differentiation of the phase chart kernel integral

For `app:ch_seed:prop:seed-phase-charts`, both integrals retain the spectators,
physical endpoints, carrier coordinate, and direction. The only smoothness
assumptions concern the phase and the carrier on open neighborhoods.
The consumer is the perturbation bound for the literal modulation chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

private theorem hasFDerivAt_doubleUnitIntegral
    {A F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set A} {W : Set ℝ} {f : (A × ℝ) × ℝ → F}
    (hU : IsOpen U) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hf : ContDiffOn ℝ ∞ f ((U ×ˢ W) ×ˢ W)) {q : A} (hq : q ∈ U) :
    HasFDerivAt (fun a ↦ ∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, f ((a, r), s))
      (∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, fderiv ℝ (fun a ↦ f ((a, r), s)) q) q := by
  have hi := contDiffOn_unitIntervalParameterIntegral (hU.prod hW) hW hIW hf
  have hd := hasFDerivAt_unitIntervalParameterIntegral hU hW hIW hi hq
  apply hd.congr_fderiv
  apply intervalIntegral.integral_congr
  intro r hr
  have hrW : r ∈ W := hIW (by simpa using hr)
  have hs : ContDiffOn ℝ ∞ (fun a : A × ℝ ↦ f ((a.1, r), a.2)) (U ×ˢ W) :=
    hf.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
      (fun a ha ↦ ⟨⟨ha.1, hrW⟩, ha.2⟩)
  exact (hasFDerivAt_unitIntervalParameterIntegral hU hW hIW hs hq).fderiv

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedSpace ℝ X := InnerProductSpace.toNormedSpace

variable {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
  {U : Set (P × (X × X) × (ℝ × E))} {V : Set (P × ℝ)} {Ω : Set (X × E)} {W : Set ℝ}

/-- Local smoothness of the mixed-Hessian integrand, jointly in all data and
both segment parameters (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem contDiffOn_phaseChartKernel
    (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.2.1) ∈ V)
    (hmem : ∀ q ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω) :
    ContDiffOn ℝ ∞ (fun a : ((P × (X × X) × (ℝ × E)) × ℝ) × ℝ ↦
      phaseChartKernel S ζ ε a.1.1 a.1.2 a.2) ((U ×ˢ W) ×ˢ W) := by
  intro a ha
  have hz : ContDiffAt ℝ ∞
      (fun b : ((P × (X × X) × (ℝ × E)) × ℝ) × ℝ ↦ ζ (b.1.1.1, b.1.1.2.2.1)) a :=
    (hζ.contDiffAt (hV.mem_nhds (hproj a.1.1 ha.1.1))).comp a (by fun_prop)
  have hp : ContDiffAt ℝ ∞
      (fun b : ((P × (X × X) × (ℝ × E)) × ℝ) × ℝ ↦ phaseChartPoint ζ ε b.1.1 b.1.2 b.2) a := by
    unfold phaseChartPoint
    apply ContDiffAt.prodMk
    · fun_prop
    · apply hz.add
      exact ContDiffAt.smul (by fun_prop) (by fun_prop)
  have hk : ContDiffAt ℝ ∞
      (fun b : ((P × (X × X) × (ℝ × E)) × ℝ) × ℝ ↦
        phaseMixedKernel S (phaseChartPoint ζ ε b.1.1 b.1.2 b.2)) a :=
    (contDiffAt_phaseMixedKernel
    (hS.contDiffAt (hΩ.mem_nhds (hmem a.1.1 ha.1.1 a.1.2 ha.1.2 a.2 ha.2)))).comp a
      (f := fun b : ((P × (X × X) × (ℝ × E)) × ℝ) × ℝ ↦
        phaseChartPoint ζ ε b.1.1 b.1.2 b.2) hp
  exact (hk.clm_apply (by fun_prop)).contDiffWithinAt

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]

/-- The double-integral kernel model is smooth in the full data tuple
(`app:ch_seed:prop:seed-phase-charts`). Its identification with the literal
chart is a separate integral-calculus identity. -/
theorem contDiffOn_phaseChartKernelIntegral
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.2.1) ∈ V)
    (hmem : ∀ q ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω) :
    ContDiffOn ℝ ∞ (phaseChartKernelIntegral S ζ ε) U :=
  contDiffOn_unitIntervalParameterIntegral hU hW hIW
    (contDiffOn_unitIntervalParameterIntegral (hU.prod hW) hW hIW
      (contDiffOn_phaseChartKernel hV hΩ hS hζ hproj hmem))

/-- Both segment integrals commute with the actual full data derivative
(`app:ch_seed:prop:seed-phase-charts`). No chart or quotient bound is assumed. -/
theorem hasFDerivAt_phaseChartKernelIntegral
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.2.1) ∈ V)
    (hmem : ∀ q ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω)
    {q : (P × (X × X) × (ℝ × E))} (hq : q ∈ U) :
    HasFDerivAt (phaseChartKernelIntegral S ζ ε)
      (∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        fderiv ℝ (fun a ↦ phaseChartKernel S ζ ε a r s) q) q :=
  hasFDerivAt_doubleUnitIntegral hU hW hIW
    (contDiffOn_phaseChartKernel hV hΩ hS hζ hproj hmem) hq

/-- The full joint derivative of the integral model is controlled by the
phase `C⁴` seminorm times a fixed geometric first-jet budget. The displayed
budget contains only the carrier, shifted point, and direction; no phase or
chart estimate is an input (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_fderiv_phaseChartKernelIntegral_le_cNorm_four
    {K : Set (X × E)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.2.1) ∈ V)
    (hmem : ∀ q ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω)
    {q : (P × (X × X) × (ℝ × E))} (hq : q ∈ U) {C : ℝ}
    (hcompact : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      phaseChartPoint ζ ε q r s ∈ K)
    (hgeom : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun a : (P × (X × X) × (ℝ × E)) ↦ a.2.2.2) q‖ +
        ‖fderiv ℝ (fun a ↦ phaseChartPoint ζ ε a r s) q‖ * ‖q.2.2.2‖ ≤ C) :
    ‖fderiv ℝ (phaseChartKernelIntegral S ζ ε) q‖ ≤ cNorm K 4 S * C := by
  rw [(hasFDerivAt_phaseChartKernelIntegral hU hV hΩ hW hIW hS hζ hproj hmem hq).fderiv]
  have hSK : ∀ a ∈ K, ContDiffAt ℝ 4 S a := fun a ha ↦
    (hS.contDiffAt (hΩ.mem_nhds (hKΩ ha))).of_le (by simp)
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (fun a ↦ phaseChartKernel S ζ ε a r s) q‖ ≤ cNorm K 4 S * C := by
    have hz : ContDiffAt ℝ ∞ (fun a : (P × (X × X) × (ℝ × E)) ↦ ζ (a.1, a.2.2.1)) q :=
      (hζ.contDiffAt (hV.mem_nhds (hproj q hq))).comp q (by fun_prop)
    have hg : DifferentiableAt ℝ (fun a ↦ phaseChartPoint ζ ε a r s) q := by
      unfold phaseChartPoint
      apply DifferentiableAt.prodMk
      · fun_prop
      · exact (hz.differentiableAt (by simp)).add (by fun_prop)
    exact (norm_fderiv_phaseMixedKernel_comp_apply_le_cNorm_four
      (g := fun a : P × (X × X) × (ℝ × E) ↦ phaseChartPoint ζ ε a r s)
      (v := fun a : P × (X × X) × (ℝ × E) ↦ a.2.2.2) hK hSK
      (hcompact r hr s hs) hg (by fun_prop)).trans
      (mul_le_mul_of_nonneg_left (hgeom r hr s hs) (cNorm_nonneg _ _ _))
  have hi (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ‖∫ s in (0 : ℝ)..1, fderiv ℝ (fun a ↦ phaseChartKernel S ζ ε a r s) q‖ ≤
        cNorm K 4 S * C := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := cNorm K 4 S * C)
      (fun s hs ↦ hb r hr s (by simpa using Ioc_subset_Icc_self hs))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := cNorm K 4 S * C)
    (fun r hr ↦ hi r (by simpa using Ioc_subset_Icc_self hr))

end JanetCartan.FullPhaseCharts.Comparison
