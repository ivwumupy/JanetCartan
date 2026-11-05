module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.CompactKernels

/-!
# Literal compact-frequency elapsed kernels

The masks in `app:ch_regular_base:eq:fixed-time-representation` are retained in
`elapsedAmplitude`. A compact covector cutoff multiplies this full amplitude.
Joint continuity and compact physical masks suffice for the finite integrals;
no quantitative Sobolev bound is used.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Continuity of the spatial projection in the fixed-time representation
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_spatialPart : Continuous (spatialPart (d := d)) := by
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i ↦ (PiLp.continuous_apply 2 _ i.succ)))

/-- The literal elapsed phase is jointly continuous whenever the original
two-time phase is. Smooth phase extensions used by the primitive graph
constructor supply this input. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_elapsedPhase (Ψ : TwoTimePhase d)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2)) :
    Continuous (fun p : (ℝ × E) × E ↦ elapsedPhase Ψ p.1.1 p.1.2 p.2) := by
  have ht : Continuous (fun p : (ℝ × E) × E ↦ p.1.2 0) := by fun_prop
  have hτ : Continuous (fun p : (ℝ × E) × E ↦ p.2 0) := by fun_prop
  exact ((ht.sub continuous_fst.fst).mul hτ).add (hΨ.comp
    ((ht.prodMk (ht.sub continuous_fst.fst)).prodMk
      ((continuous_spatialPart.comp continuous_fst.snd).prodMk
        (continuous_spatialPart.comp continuous_snd))))

/-- Joint continuity of the actual compact-frequency amplitude, including
both masks and the Fourier multiplier in their original positions.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_cut_elapsedAmplitude (b : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ)
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : Continuous χsource)
    (hβ : Continuous β) (hθ : Continuous θ) :
    Continuous (fun p : ((ℝ × E) × E) × E ↦
      frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β p.1.1.1)
        p.1.1.2 p.1.2 p.2) := by
  have ht : Continuous (fun p : ((ℝ × E) × E) × E ↦ p.1.1.2 0) := by fun_prop
  have ha : Continuous (fun p : ((ℝ × E) × E) × E ↦
      b (p.1.1.2 0) (p.1.1.2 0 - p.1.1.1)
        (spatialPart p.1.1.2) (spatialPart p.2)) :=
    hb.comp ((ht.prodMk (ht.sub continuous_fst.fst.fst)).prodMk
      ((continuous_spatialPart.comp continuous_fst.fst.snd).prodMk
        (continuous_spatialPart.comp continuous_snd)))
  exact (hθ.comp continuous_snd).smul
    ((((ho.comp continuous_fst.fst.snd).mul (hs.comp continuous_fst.snd)).mul
      (hβ.comp continuous_snd)).smul ha)

/-- The finite regularizations have the fixed compact physical and frequency
carriers needed by Fubini. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cut_elapsedAmplitude_eq_zero_off_support (b : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ) (r : ℝ) (x z ξ : E)
    (h : x ∉ tsupport χout ∨ z ∉ tsupport χsource ∨ ξ ∉ tsupport θ) :
    frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r) x z ξ = 0 := by
  rcases h with h | h | h <;>
    simp [frequencyCutFullAmplitude, elapsedAmplitude, image_eq_zero_of_notMem_tsupport h]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
