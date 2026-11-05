module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Reference
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness.Calculus

/-!
# Local smoothness of the literal reference chart

These are inputs to the compact uniform limit in `Comparison.ReferenceLimit`,
for the comparison following `app:ch_seed:eq:seed-quotient-integral`.
`U` is an open set of joint spectator/data variables `(p,z,η)`; `V` is the
carrier domain. `L` and `W` are open buffers for epsilon and the unit interval.
Only local smoothness on the displayed domains is required.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P E : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E → ℝ} {ζ : P × ℝ → E}
  {U : Set (P × (ℝ × E))} {V : Set (P × ℝ)} {Ω : Set E} {L W : Set ℝ}

/-- Local smoothness of the actual reference full chart, jointly in
`(p,z,η,ε)`, obtained by integrating the smooth shifted covector derivative
(`app:ch_seed:eq:seed-quotient-integral`). Physical endpoints are arbitrary. -/
theorem contDiffOn_fullChart_reference
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hL : IsOpen L) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hH : ContDiffOn ℝ ∞ H Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1, q.2.1) ∈ V)
    (hshift : ∀ q ∈ U, ∀ ε ∈ L, ∀ s ∈ W,
      ζ (q.1, q.2.1) + (s * ε) • q.2.2 ∈ Ω)
    (x x' : WithLp 2 (ℝ × E)) :
    ContDiffOn ℝ ∞ (fun a : (P × (ℝ × E)) × ℝ ↦
      fullChart (referencePhase H) ζ a.2 a.1.1 x x' a.1.2) (U ×ˢ L) := by
  have hQ : ContDiffOn ℝ ∞ (fun a : (P × (ℝ × E)) × ℝ ↦
      phaseShiftQuotient (fun _ : ℝ ↦ H) 0 (ζ (a.1.1, a.1.2.1)) a.1.2.2 a.2)
      (U ×ˢ L) := by
    apply contDiffOn_phaseShiftQuotient_comp (S := fun _ : ℝ ↦ H)
      (V := univ) isOpen_univ hΩ
      (hU.prod hL) hW hIW
      (hH.comp contDiffOn_snd (fun _ h ↦ h.2)) contDiffOn_const
      (hζ.comp (contDiffOn_fst.fst.prodMk contDiffOn_fst.snd.fst)
        (fun a ha ↦ hproj a.1 ha.1)) contDiffOn_fst.snd.snd contDiffOn_snd
    intro a ha s hs
    exact ⟨mem_univ _, hshift a.1 ha.1 a.2 ha.2 s hs⟩
  apply (hQ.prodMk (contDiffOn_fst.snd.snd)).congr
  intro a ha
  exact fullChart_reference_shift ζ a.1.1 a.1.2 a.2
    (fun s hs ↦ (hH.contDiffAt (hΩ.mem_nhds
      (hshift a.1 ha.1 a.2 ha.2 s (hIW hs)))).of_le (by simp)) x x'

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- On an open direction box, the actual reference transverse differential
is the identity for every admissible shift, by the literal reference formula
(`app:ch_seed:prop:seed-phase-charts`). No epsilon derivative is asserted. -/
theorem fderiv_transverseChart_reference_shift
    {J : Set E} (hJ : IsOpen J) {η : E} (hη : η ∈ J)
    (p : P) (z ε : ℝ)
    (hH : ∀ v ∈ J, ∀ s ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 1 H (ζ (p, z) + (s * ε) • v))
    (t : ℝ) (y y' : E) :
    fderiv ℝ (fun v ↦ transverseChart (referencePhase H) ζ ε p t y y' (z, v)) η =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun v ↦ transverseChart (referencePhase H) ζ ε p t y y' (z, v))
      =ᶠ[𝓝 η] id := by
    filter_upwards [hJ.mem_nhds hη] with v hv
    exact transverseChart_reference_shift ζ p (z, v) ε (hH v hv) t y y'
  rw [he.fderiv_eq, fderiv_id]

end JanetCartan.FullPhaseCharts.Comparison
