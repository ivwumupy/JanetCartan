module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.GraphBounds

/-!
# Compact frequency images of the regularized modified normal

For `app:ch_background:prop:bg-adjoint`, a compact support of the original
regularized density is pushed through the actual conic map. This discharges
the compact source/frequency support needed by `PDONormal`, without assuming
support or integrability of the final normal amplitude.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
open ContinuumRow ContinuumRow.TransportKernel ContinuumNormal AmplitudeBound
variable {n : ℕ}

/-- The original variables at a fixed output position for the compact-image
argument in `app:ch_background:eq:bg-full-complex-amplitude`: source position,
spectator, and the original slice coordinate. -/
abbrev SourceChartVariables (n : ℕ) := Euclidean n × (Euclidean 2 × Euclidean n)

/-- The normalized normal has compact source/frequency support, derived from
a compact support of its original density and a continuous forward chart.
The map includes division by `2π`, preserving physical-frequency normalization
(`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_cyclesAmplitude_source_frequency
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x : Euclidean n) (C : Set (SourceChartVariables n)) (hC : IsCompact C)
    (hΨ : ContinuousOn (fun p : SourceChartVariables n ↦
      g.forward x p.1 p.2.1 p.2.2) C)
    (hU : ∀ y v t, t ∈ g.domain x y v →
      g.inverse x y v (g.forward x y v t) = t)
    (hs : ∀ p : SourceChartVariables n, p ∉ C →
      modifiedNormalDensity a m x p.1
        (chartCarrierVariable g.coordinates p.2.1 p.2.2) = 0) :
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      cyclesAmplitude g a m (x, p.1, p.2)) := by
  let F : SourceChartVariables n → Euclidean n × Euclidean n := fun p ↦
    (p.1, (2 * Real.pi)⁻¹ • g.forward x p.1 p.2.1 p.2.2)
  have hF : ContinuousOn F C := continuous_fst.continuousOn.prodMk
    ((continuousOn_const (c := (2 * Real.pi)⁻¹)).smul hΨ)
  apply HasCompactSupport.intro (hC.image_of_continuousOn hF)
  intro p hp
  have hz : ∀ v, inverseDensity g a m ((x, p.1, (2 * Real.pi) • p.2), v) = 0 := by
    intro v
    by_cases ht : (2 * Real.pi) • p.2 ∈ g.forward x p.1 v '' g.domain x p.1 v
    · obtain ⟨t, htd, he⟩ := ht
      have hnot : (p.1, v, t) ∉ C := by
        intro hc
        apply hp
        refine ⟨(p.1, v, t), hc, ?_⟩
        simp only [F, he, smul_smul,
          inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < 2 * Real.pi)), one_smul]
      change modifiedInverseDensity a m x p.1 g.coordinates
        (g.domain x p.1) (g.forward x p.1) (g.inverse x p.1) (g.jacobian x p.1)
        v ((2 * Real.pi) • p.2) = 0
      rw [← he]
      simp [modifiedInverseDensity, mem_image_of_mem _ htd, hU p.1 v t htd,
        hs (p.1, v, t) hnot]
    · simp [inverseDensity, modifiedInverseDensity, ht]
  have hi : physicalAmplitude g a m (x, p.1, (2 * Real.pi) • p.2) = 0 := by
    change (∫ v, inverseDensity g a m ((x, p.1, (2 * Real.pi) • p.2), v)) = 0
    simp only [hz, integral_zero]
  simp [cyclesAmplitude, hi]

/-- The same compact image in the paired coordinates used by the scalar entry
of the matrix PDO (`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_matrixAmplitude_source_frequency
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x : Euclidean n) (C : Set (SourceChartVariables n)) (hC : IsCompact C)
    (hΨ : ContinuousOn (fun p : SourceChartVariables n ↦
      g.forward x p.1 p.2.1 p.2.2) C)
    (hU : ∀ y v t, t ∈ g.domain x y v →
      g.inverse x y v (g.forward x y v t) = t)
    (hs : ∀ p : SourceChartVariables n, p ∉ C →
      modifiedNormalDensity a m x p.1
        (chartCarrierVariable g.coordinates p.2.1 p.2.2) = 0) :
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      matrixAmplitude g a m p.2 (pairedPosition x p.1) 0 0) := by
  simpa only [matrixAmplitude, positionAmplitude,
    freezingOutputProjection_pairedPosition, freezingSourceProjection_pairedPosition] using
    hasCompactSupport_cyclesAmplitude_source_frequency g a m x C hC hΨ hU hs

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
