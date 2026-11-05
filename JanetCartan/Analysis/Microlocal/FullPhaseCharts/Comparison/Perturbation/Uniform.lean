module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.LiteralIdentity
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Geometry

/-!
# Uniform perturbations of literal modulation charts

The comparison after `app:ch_seed:eq:seed-quotient-integral` follows from the
literal integral identity and the compact geometric budget. The constant is
chosen before either phase. Open buffers are geometric hypotheses only.
The consumer is the full/data/transverse comparison in `Perturbation`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

local instance : NormedSpace ℝ X := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Uniform joint `C¹` perturbation of the literal chart in
`app:ch_seed:prop:seed-phase-charts`. The compact shifted-segment hypothesis
controls the phase jets; the open buffers justify actual differentiation.
The positive constant depends only on compact geometry and the carrier.
No quotient or chart estimate is assumed. -/
theorem exists_modulationChart_perturbation_bound
    {ζ : P × ℝ → E} {P₀ : Set P} {B : Set X} {I : Set ℝ} {J : Set E}
    {V : Set (P × ℝ)} {Ω K : Set (X × E)}
    {U : Set (P × (X × X) × (ℝ × E))} {T : Set X} {W : Set ℝ}
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
    ∃ C > 0, ∀ S S₀ : X × E → ℝ,
      ContDiffOn ℝ ∞ S Ω → ContDiffOn ℝ ∞ S₀ Ω →
      ∀ ε, |ε| ≤ ε₀ →
      ContDiffOn ℝ ∞ (fun q : P × (X × X) × (ℝ × E) ↦
        modulationChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U ∧
      ContDiffOn ℝ ∞ (fun q : P × (X × X) × (ℝ × E) ↦
        modulationChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U ∧
      ∀ q ∈ P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)),
        ‖modulationChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2 -
          modulationChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2‖ ≤ C * cNorm K 4 (S - S₀) ∧
        ‖fderiv ℝ (fun a : P × (X × X) × (ℝ × E) ↦
            modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q -
          fderiv ℝ (fun a : P × (X × X) × (ℝ × E) ↦
            modulationChart S₀ ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q‖ ≤
          C * cNorm K 4 (S - S₀) := by
  obtain ⟨C, hC, hb⟩ := exists_phaseChartPoint_geometric_bound
    hP hB hI hJ hV hPV hζ hε₀
  refine ⟨C, hC, ?_⟩
  intro S S₀ hS hS₀ ε hε
  have hm : ∀ q ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω :=
    fun q hq r hr s hs ↦ hbuffer ε hε q hq _ (hphys q hq r hr) s hs
  have he (F : X × E → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :=
    modulationChart_eqOn_phaseChartKernelIntegral hT hΩ hW hIW hF
      (fun q hq r hr ↦ hphys q hq r (hIW hr)) (hbuffer ε hε)
  have hc (F : X × E → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :
      ContDiffOn ℝ ∞ (fun q : P × (X × X) × (ℝ × E) ↦
        modulationChart F ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U :=
    (contDiffOn_phaseChartKernelIntegral hU hV hΩ hW hIW hF hζ hproj hm).congr
      (he F hF)
  refine ⟨hc S hS, hc S₀ hS₀, ?_⟩
  intro q hq
  have hqU := hQU hq
  have hcompact : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      phaseChartPoint ζ ε q r s ∈ K := fun r hr s hs ↦
    phaseChartPoint_mem_of_convex hBc hq.2.1.1 hq.2.1.2
      (fun x hx s hs ↦ hshift ε hε q.1 hq.1 x hx q.2.2.1 hq.2.2.1
        q.2.2.2 hq.2.2.2 s hs) hr hs
  have herr : (fun a : P × (X × X) × (ℝ × E) ↦
      modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2 -
      modulationChart S₀ ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) =ᶠ[𝓝 q]
        phaseChartKernelIntegral (S - S₀) ζ ε := by
    filter_upwards [hU.mem_nhds hqU] with a ha
    exact (congrArg₂ (· - ·) (he S hS ha) (he S₀ hS₀ ha)).trans
      (phaseChartKernelIntegral_sub hΩ hW hIW hS hS₀ a (hm a ha)).symm
  constructor
  · rw [herr.eq_of_nhds]
    exact (norm_phaseChartKernelIntegral_le_cNorm_four (S := S - S₀) hK
      (fun a ha ↦ ((hS.sub hS₀).contDiffAt (hΩ.mem_nhds (hKΩ ha))).of_le (by simp))
      ζ ε q hcompact).trans (by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb ε hε q hq).1
          (cNorm_nonneg K 4 (S - S₀)))
  · rw [← fderiv_sub ((hc S hS).contDiffAt (hU.mem_nhds hqU) |>.differentiableAt (by simp))
      ((hc S₀ hS₀).contDiffAt (hU.mem_nhds hqU) |>.differentiableAt (by simp))]
    rw [show fderiv ℝ ((fun a : P × (X × X) × (ℝ × E) ↦
        modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) -
        (fun a ↦ modulationChart S₀ ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2)) q =
      fderiv ℝ (phaseChartKernelIntegral (S - S₀) ζ ε) q from herr.fderiv_eq]
    simpa [mul_comm] using norm_fderiv_phaseChartKernelIntegral_le_cNorm_four (S := S - S₀)
      hK hKΩ hU hV hΩ hW hIW (hS.sub hS₀) hζ hproj hm hqU hcompact (hb ε hε q hq).2

end JanetCartan.FullPhaseCharts.Comparison
