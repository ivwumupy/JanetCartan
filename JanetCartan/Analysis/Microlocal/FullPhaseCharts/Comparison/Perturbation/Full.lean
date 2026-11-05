module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Restrictions

/-! # Uniform full-chart perturbation

The constant in `app:ch_seed:prop:seed-phase-charts` is selected from geometry
before the two phases. The theorem controls the actual full joint derivative
and its data restriction, using the literal quotient at every epsilon.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The quantitative full-chart comparison after
`app:ch_seed:eq:seed-quotient-integral`, with joint spectators, both endpoints,
and data retained. Open buffers and compact shifted-segment containment are
explicit geometric inputs. The constant is independent of both phases. -/
theorem exists_fullChart_perturbation_bound
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
    ∃ C > 0, ∀ S S₀ : (WithLp 2 (ℝ × E)) × E → ℝ,
      ContDiffOn ℝ ∞ S Ω → ContDiffOn ℝ ∞ S₀ Ω →
      ∀ ε, |ε| ≤ ε₀ →
      ContDiffOn ℝ ∞ (fun q : P × ((WithLp 2 (ℝ × E)) × (WithLp 2 (ℝ × E))) × (ℝ × E) ↦
        fullChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U ∧
      ContDiffOn ℝ ∞ (fun q : P × ((WithLp 2 (ℝ × E)) × (WithLp 2 (ℝ × E))) × (ℝ × E) ↦
        fullChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U ∧
      ∀ q ∈ P₀ ×ˢ ((B ×ˢ B) ×ˢ (I ×ˢ J)),
        ‖fullChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2 -
          fullChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2‖ ≤ C * cNorm K 4 (S - S₀) ∧
        ‖fderiv ℝ (fun a : P × ((WithLp 2 (ℝ × E)) × (WithLp 2 (ℝ × E))) × (ℝ × E) ↦
            fullChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q -
          fderiv ℝ (fun a : P × ((WithLp 2 (ℝ × E)) × (WithLp 2 (ℝ × E))) × (ℝ × E) ↦
            fullChart S₀ ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q‖ ≤
          C * cNorm K 4 (S - S₀) ∧
        ‖fderiv ℝ (fullChart S ζ ε q.1 q.2.1.1 q.2.1.2) q.2.2 -
          fderiv ℝ (fullChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2) q.2.2‖ ≤
          C * cNorm K 4 (S - S₀) := by
  obtain ⟨C, hC, hb⟩ := exists_modulationChart_perturbation_bound
    hP hB hBc hI hJ hV hPV hζ hK hKΩ hΩ hU hT hW hIW hQU hproj hphys hε₀ hbuffer hshift
  refine ⟨C, hC, ?_⟩
  intro S S₀ hS hS₀ ε hε
  obtain ⟨hc, hc₀, hb⟩ := hb S S₀ hS hS₀ ε hε
  let L := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := norm_fullChart_coordinates_le_one
  have hfc : ContDiffOn ℝ ∞ (fun q : P ×
      (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
      fullChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U :=
    L.contDiff.comp_contDiffOn hc
  have hfc₀ : ContDiffOn ℝ ∞ (fun q : P ×
      (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
      fullChart S₀ ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2) U :=
    L.contDiff.comp_contDiffOn hc₀
  refine ⟨hfc, hfc₀, ?_⟩
  intro q hq
  have hd := (hc.contDiffAt (hU.mem_nhds (hQU hq))).differentiableAt (by simp)
  have hd₀ := (hc₀.contDiffAt (hU.mem_nhds (hQU hq))).differentiableAt (by simp)
  refine ⟨?_, ?_, ?_⟩
  · change ‖L _ - L _‖ ≤ _
    rw [← map_sub]
    exact (L.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hb q hq).1)
  · exact (norm_fderiv_chart_restriction_sub_le (ι := id) hd hd₀
      differentiableAt_id (by simp [fderiv_id]) L hL).trans (hb q hq).2
  · let ι := fun u : ℝ × E ↦ (q.1, q.2.1, u)
    have hi : HasFDerivAt ι
        ((ContinuousLinearMap.inr ℝ P _).comp (ContinuousLinearMap.inr ℝ _ (ℝ × E))) q.2.2 := by
      convert (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2.2).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) q.2.1 q.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2.2)) using 1 <;> rfl
    have hni : ‖fderiv ℝ ι q.2.2‖ ≤ 1 := by
      rw [hi.fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro v
      simp
    exact (norm_fderiv_chart_restriction_sub_le (ι := ι) (a := q.2.2)
      (f := fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
        modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2)
      (g := fun a ↦ modulationChart S₀ ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2)
      hd hd₀ hi.differentiableAt hni L hL).trans
      (hb q hq).2

end JanetCartan.FullPhaseCharts.Comparison
