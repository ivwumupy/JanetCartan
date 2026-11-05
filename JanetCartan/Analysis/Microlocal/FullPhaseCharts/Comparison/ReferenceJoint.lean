module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.ReferenceLimit
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Restrictions

/-!
# Reference comparison with physical endpoints retained

The reference chart is locally independent of both physical endpoints. The
projection onto spectator/data variables is a contraction, so the joint
reference derivative error in `app:ch_seed:prop:seed-phase-charts` is bounded
by the spectator/data derivative error proved in `ReferenceLimit`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Local smoothness of the exact reference phase used in the comparison after
`app:ch_seed:eq:seed-quotient-integral`. Only its covector projection must lie
in the smoothness domain of the fixed Hamiltonian. -/
theorem contDiffOn_referencePhase {H : E → ℝ}
    {Ω : Set (WithLp 2 (ℝ × E) × E)} {Ωξ : Set E}
    (hH : ContDiffOn ℝ ∞ H Ωξ) (hproj : ∀ q ∈ Ω, q.2 ∈ Ωξ) :
    ContDiffOn ℝ ∞ (referencePhase H) Ω := by
  have hc : ContDiff ℝ ∞ (fun q : WithLp 2 (ℝ × E) × E ↦ q.1.ofLp) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff.comp contDiff_fst
  exact (hc.fst.contDiffOn.mul (hH.comp contDiffOn_snd hproj)).add
    (hc.snd.contDiffOn.inner ℝ contDiffOn_snd)

/-- Physical endpoints contribute no reference derivative error. This estimate
lifts `exists_fullChart_reference_c1_radius` to all variables used by the
perturbation theorem in `app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_fderiv_reference_joint_sub_le
    {H : E → ℝ} {ζ : P × ℝ → E}
    {R : Set (P × (ℝ × E))} {V : Set (P × ℝ)} {Ωξ : Set E} {L W : Set ℝ}
    (hR : IsOpen R) (hΩξ : IsOpen Ωξ) (hL : IsOpen L)
    (h0 : (0 : ℝ) ∈ L) (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hH : ContDiffOn ℝ ∞ H Ωξ) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ a ∈ R, (a.1, a.2.1) ∈ V)
    (hshift : ∀ a ∈ R, ∀ e ∈ L, ∀ s ∈ W,
      ζ (a.1, a.2.1) + (s * e) • a.2.2 ∈ Ωξ)
    {ε : ℝ} (hε : ε ∈ L)
    (q : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E))
    (hq : (q.1, q.2.2) ∈ R) :
    ‖fderiv ℝ (fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
        fullChart (referencePhase H) ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q -
      fderiv ℝ (fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
        frozenChart (fun z ↦ gradient H (ζ (a.1, z))) a.2.2) q‖ ≤
    ‖fderiv ℝ (fun a : P × (ℝ × E) ↦
        fullChart (referencePhase H) ζ ε a.1 0 0 a.2) (q.1, q.2.2) -
      fderiv ℝ (fun a : P × (ℝ × E) ↦
        frozenChart (fun z ↦ gradient H (ζ (a.1, z))) a.2) (q.1, q.2.2)‖ := by
  let F := fun e (a : P × (ℝ × E)) ↦ fullChart (referencePhase H) ζ e a.1 0 0 a.2
  let G := fun a : P × (ℝ × E) ↦ frozenChart (fun z ↦ gradient H (ζ (a.1,z))) a.2
  let π : (P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E)) →L[ℝ]
      P × (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ P _).prod
      ((ContinuousLinearMap.snd ℝ _ (ℝ × E)).comp (ContinuousLinearMap.snd ℝ P _))
  have hπ : ‖fderiv ℝ π q‖ ≤ 1 := by
    rw [π.fderiv]
    refine π.opNorm_le_bound zero_le_one ?_
    intro a
    change max ‖a.1‖ ‖a.2.2‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact max_le (norm_fst_le a) ((norm_snd_le a.2).trans (norm_snd_le a))
  have hreg (a : P × (ℝ × E)) (ha : a ∈ R) (e : ℝ) (he : e ∈ L)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 H (ζ (a.1, a.2.1) + (s * e) • a.2.2) :=
    (hH.contDiffAt (hΩξ.mem_nhds (hshift a ha e he s (hIW hs)))).of_le (by simp)
  have hzero : F 0 =ᶠ[𝓝 (π q)] G := by
    filter_upwards [hR.mem_nhds hq] with a ha
    apply fullChart_reference_zero
    simpa using (hreg a ha 0 h0 0 (by simp)).differentiableAt one_ne_zero
  have hd (e : ℝ) (he : e ∈ L) : DifferentiableAt ℝ (F e) (π q) := by
    have hc := (contDiffOn_fullChart_reference hR hΩξ hL hW hIW hH hζ hproj hshift 0 0).contDiffAt
      (x := (π q, e)) ((hR.prod hL).mem_nhds ⟨hq, he⟩)
    exact (hc.comp (π q) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have heq : (fun a : P × (WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
      fullChart (referencePhase H) ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2)
      =ᶠ[𝓝 q] (fun a ↦ F ε (π a)) := by
    filter_upwards [π.continuous.continuousAt.eventually (hR.mem_nhds hq)] with a ha
    exact (fullChart_reference_shift ζ a.1 a.2.2 ε (hreg (π a) ha ε hε) _ _).trans
      (fullChart_reference_shift ζ a.1 a.2.2 ε (hreg (π a) ha ε hε) 0 0).symm
  rw [heq.fderiv_eq]
  exact norm_fderiv_chart_restriction_sub_le (hd ε hε)
    (hzero.differentiableAt_iff.mp (hd 0 h0)) π.differentiableAt hπ
    (ContinuousLinearMap.id ℝ (ℝ × E)) (by simp)

end JanetCartan.FullPhaseCharts.Comparison
