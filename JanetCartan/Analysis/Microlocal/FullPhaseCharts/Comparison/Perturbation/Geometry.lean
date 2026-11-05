module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.IntegralModel
public import Mathlib.Analysis.Convex.Basic

/-!
# The geometric budget for the phase chart perturbation

The comparison after `app:ch_seed:eq:seed-quotient-integral` requires a
constant uniform in both physical endpoints, all spectator/data coordinates,
epsilon, and the two segment parameters. Compactness and local carrier
smoothness supply this constant without any phase or chart assumptions.

`exists_phaseChartPoint_geometric_bound` supplies the direction bound for
`norm_phaseChartKernelIntegral_le_cNorm_four` and the `hgeom` premise of
`norm_fderiv_phaseChartKernelIntegral_le_cNorm_four`. The parent literal-chart
comparison must still supply the phase hypotheses and identify the integral.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance phaseChartGeometryNormedSpace : NormedSpace ℝ X :=
  InnerProductSpace.toNormedSpace

variable {ζ : P × ℝ → E}

/-- The geometric phase point is locally smooth jointly in `(q, ε, r, s)`.
Only the carrier needs a smoothness hypothesis
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem contDiffAt_phaseChartPoint_joint
    {a : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ)}
    (hζ : ContDiffAt ℝ ∞ ζ (a.1.1, a.1.2.2.1)) :
    ContDiffAt ℝ ∞ (fun b : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
      phaseChartPoint ζ b.2.1 b.1 b.2.2.1 b.2.2.2) a := by
  have hz : ContDiffAt ℝ ∞
      (fun b : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
        ζ (b.1.1, b.1.2.2.1)) a := hζ.comp a (by fun_prop)
  unfold phaseChartPoint
  apply ContDiffAt.prodMk
  · fun_prop
  · exact hz.add (by fun_prop)

/-- The actual full data derivative of the geometric phase point is smooth
jointly in `(q, ε, r, s)`. This gives the continuity needed to choose the
uniform first-jet budget in `app:ch_seed:prop:seed-phase-charts`. -/
theorem contDiffAt_fderiv_phaseChartPoint
    {a : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ)}
    (hζ : ContDiffAt ℝ ∞ ζ (a.1.1, a.1.2.2.1)) :
    ContDiffAt ℝ ∞ (fun b : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
      fderiv ℝ (fun q ↦ phaseChartPoint ζ b.2.1 q b.2.2.1 b.2.2.2) b.1) a := by
  have hf : ContDiffAt ℝ ∞
      (fun b : ((P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ)) ×
          (P × (X × X) × (ℝ × E)) ↦
        phaseChartPoint ζ b.1.2.1 b.2 b.1.2.2.1 b.1.2.2.2) (a, a.1) :=
    (contDiffAt_phaseChartPoint_joint hζ).comp (a, a.1)
      (f := fun b : ((P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ)) ×
          (P × (X × X) × (ℝ × E)) ↦ (b.2, b.1.2)) (by fun_prop)
  exact hf.fderiv contDiffAt_fst (by simp)

/-- One positive constant, chosen solely from the compact geometry and the
locally smooth carrier, bounds the direction and the exact geometric budget
used by `norm_fderiv_phaseChartKernelIntegral_le_cNorm_four`. This is the
phase-independent constant in the comparison following
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_phaseChartPoint_geometric_bound
    {P₀ : Set P} {B : Set X} {I : Set ℝ} {J : Set E} {V : Set (P × ℝ)}
    (hP : IsCompact P₀) (hB : IsCompact B) (hI : IsCompact I) (hJ : IsCompact J)
    (hV : IsOpen V) (hPV : P₀ ×ˢ I ⊆ V) (hζ : ContDiffOn ℝ ∞ ζ V)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C > 0, ∀ ε, |ε| ≤ ε₀ → ∀ q ∈ P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)),
      ‖q.2.2.2‖ ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (fun a : P × (X × X) × (ℝ × E) ↦ a.2.2.2) q‖ +
          ‖fderiv ℝ (fun a ↦ phaseChartPoint ζ ε a r s) q‖ * ‖q.2.2.2‖ ≤ C := by
  let T := (P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J))) ×ˢ
    (Icc (-ε₀) ε₀ ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  have hT : IsCompact T :=
    (hP.prod ((hB.prod hB).prod (hI.prod hJ))).prod
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  let F := fun a : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
    max ‖a.1.2.2.2‖
      (‖fderiv ℝ (fun q : P × (X × X) × (ℝ × E) ↦ q.2.2.2) a.1‖ +
        ‖fderiv ℝ (fun q ↦ phaseChartPoint ζ a.2.1 q a.2.2.1 a.2.2.2) a.1‖ *
          ‖a.1.2.2.2‖)
  have hdir : Continuous (fun a : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
      a.1.2.2.2) := by fun_prop
  have hη : ContDiff ℝ ∞ (fun q : P × (X × X) × (ℝ × E) ↦ q.2.2.2) := by
    fun_prop
  have hDη : Continuous (fun a : (P × (X × X) × (ℝ × E)) × (ℝ × ℝ × ℝ) ↦
      fderiv ℝ (fun q : P × (X × X) × (ℝ × E) ↦ q.2.2.2) a.1) :=
    (hη.continuous_fderiv (by simp)).comp continuous_fst
  have hF : ContinuousOn F T := by
    intro a ha
    have hz : ContDiffAt ℝ ∞ ζ (a.1.1, a.1.2.2.1) :=
      hζ.contDiffAt (hV.mem_nhds (hPV ⟨ha.1.1, ha.1.2.2.1⟩))
    have hf : ContinuousAt F a := hdir.continuousAt.norm.max (hDη.continuousAt.norm.add
      ((contDiffAt_fderiv_phaseChartPoint hz).continuousAt.norm.mul
        hdir.continuousAt.norm))
    exact hf.continuousWithinAt
  obtain ⟨C, hC⟩ := hT.bddAbove_image hF
  refine ⟨max ε₀ C, hε₀.trans_le (le_max_left _ _), ?_⟩
  intro ε hε q hq
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      F (q, ε, r, s) ≤ max ε₀ C :=
    (hC (mem_image_of_mem F ⟨hq, abs_le.mp hε, hr, hs⟩)).trans (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans (hb 0 (by simp) 0 (by simp)),
    fun r hr s hs ↦ (le_max_right _ _).trans (hb r hr s hs)⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Convexity of the physical box upgrades the original shifted-segment
containment to the points under both integrals. This supplies the `hcompact`
premise in the perturbation estimate of `app:ch_seed:prop:seed-phase-charts`. -/
theorem phaseChartPoint_mem_of_convex
    {B : Set X} {K : Set (X × E)} (hB : Convex ℝ B)
    {ε : ℝ} {q : P × (X × X) × (ℝ × E)}
    (hx : q.2.1.1 ∈ B) (hx' : q.2.1.2 ∈ B)
    (hshift : ∀ x ∈ B, ∀ s ∈ Icc (0 : ℝ) 1,
      (x, ζ (q.1, q.2.2.1) + (s * ε) • q.2.2.2) ∈ K)
    {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    phaseChartPoint ζ ε q r s ∈ K :=
  hshift _ (hB.add_smul_sub_mem hx' hx hr) s hs

end JanetCartan.FullPhaseCharts.Comparison
