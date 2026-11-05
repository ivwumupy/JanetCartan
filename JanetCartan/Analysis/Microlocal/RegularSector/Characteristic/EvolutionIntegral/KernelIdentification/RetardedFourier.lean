module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.FixedTime

/-!
# The lower-buffer retarded triangle for the finite Fourier kernels

The fixed slab integral equals the original lower-end retarded triangle,
including endpoints, by `Basic.integral_fixed_slab_eq_retarded`. All finite
integrability is obtained from the continuous compact kernels. Identifying the
spectral slices with the original physical Fourier multiplier remains a separate
Fourier-inversion obligation.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The literal finite-cutoff fixed slab equals the retarded spectral time
triangle. The amplitude's lower buffer, rather than a changed integration
region, kills the excess interval. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_cut_elapsedGraph_eq_retardedFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : Continuous β) (hθ : Continuous θ)
    (hscs : HasCompactSupport χsource) (hθcs : HasCompactSupport θ)
    (a Δ : ℝ) (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : graphTestSpace (d + 1) q) (x : E) (hat : a ≤ x 0) (htΔ : x 0 - a ≤ Δ) :
    (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x) =
      ∫ s in a..x 0, χout x • cutFixedTimeFourier Ψ b β θ
        (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
        (x 0) s (spatialPart x) := by
  let g : ℝ → Fin q → ℂ := fun r ↦ graphOperator (elapsedPhase Ψ r)
    (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
    (fun z ↦ (u.val z).ofLp) x
  let f : ℝ → Fin q → ℂ := fun s ↦ χout x • cutFixedTimeFourier Ψ b β θ
    (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
    (x 0) s (spatialPart x)
  have he (r : ℝ) : g r = f (x 0 - r) := by
    apply cut_elapsedGraph_eq_fixedTimeFourier Ψ b χout χsource β θ hs r u x
    · exact hΨ.comp (f := fun η ↦ ((x 0, x 0 - r), (spatialPart x, η)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    · exact hb.comp (f := fun η ↦ ((x 0, x 0 - r), (spatialPart x, η)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    · exact hβ
    · exact hθ
    · exact hθcs
  have hc : Continuous g := by
    have hc := continuous_compact_graphTestOutput (elapsedPhase Ψ)
      (fun r ↦ frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (continuous_elapsedPhase Ψ hΨ)
      (continuous_cut_elapsedAmplitude b χout χsource β θ hb ho hs.continuous hβ hθ)
      hscs hθcs
      (fun r x z ξ h ↦ cut_elapsedAmplitude_eq_zero_off_support b χout χsource β θ
        r x z ξ (Or.inr h)) u
    exact (PiLp.continuous_ofLp 2 _).comp
      (hc.comp (continuous_id.prodMk (continuous_const (y := x))))
  have hi : IntervalIntegrable (fun r ↦ f (x 0 - r)) volume 0 Δ := by
    simpa only [← funext he] using hc.intervalIntegrable 0 Δ
  have hz (s : ℝ) (hsa : s ≤ a) : f s = 0 := by
    simp [f, cutFixedTimeFourier, hzero _ _ _ _ hsa]
  change (∫ r in Icc 0 Δ, g r) = ∫ s in a..x 0, f s
  simp_rw [he]
  exact integral_fixed_slab_eq_retarded hat htΔ f hi hz

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
