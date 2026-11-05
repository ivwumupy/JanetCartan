module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedFixedTime
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedRepresentatives
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.RetardedPhysical
/-!
# The supported physical retarded triangle

The primitive phase and amplitude need be continuous only near their actual
physical and conic supports. Compact kernels provide time integrability, the
proved multiplier inversion gives the fixed-time action, and the original
lower buffer removes the excess elapsed interval.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 300000
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ
/-- The literal forward compact kernel integral is `Mχout E_b B_(θβ)
Mχsource` under supported primitive regularity. The interval and lower buffer
are exactly those of `app:ch_regular_base:eq:fixed-time-representation`.
Consumer: the strong-limit uncut retarded construction. -/
theorem integral_cut_elapsedGraph_eq_retardedPhysical_of_support
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0)
    (u : graphTestSpace (d + 1) q) (x : E) :
    (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x) =
      cutRetardedPhysical Ψ b χout χsource β θ hs hβ hθ hθcs a u x := by
  by_cases hx : χout x = 0
  · simp [graphOperator, frequencyCutFullAmplitude, elapsedAmplitude, hx, cutRetardedPhysical]
  let f : ℝ → V := fun s ↦ χout x • graphOperator (Ψ (x 0) s)
    (fun y _ η ↦ b (x 0) s y η)
    (cutPhysicalMultiplierSlice β θ (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
      hβ hθ hθcs s) (spatialPart x)
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      graphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
        (fun z ↦ (u.val z).ofLp) x = f (x 0 - r) := by
    apply cut_elapsedGraph_eq_spatialGraph_of_support Ψ b χout χsource β θ hs r u x
      _ _ hβ hθ hθcs
    · intro hx ξ hξ
      exact (hΨ r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
    · intro hx ξ hξ
      exact (hb r hr x hx ξ hξ).comp (f := fun ξ : E ↦
        ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart)).continuousAt
  have hc := (continuous_supported_elapsed_cut_outputs Ψ b χout χsource β Δ hΔ
    hΨ hb ho hs.continuous hβ.continuous hocs hscs θ hθ.continuous hθcs u).1
  have hc₀ := hc.comp
    (show Continuous (fun r : ℝ ↦ (r, x)) from continuous_id.prodMk continuous_const)
  have hc₁ := (PiLp.continuous_ofLp 2 (fun _ : Fin q ↦ ℂ)).comp hc₀
  have hg : Continuous (fun r ↦ graphOperator (elapsedPhase Ψ (max 0 (min Δ r)))
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β (max 0 (min Δ r))))
      (fun z ↦ (u.val z).ofLp) x) := hc₁
  have hfc : ContinuousOn (fun r ↦ f (x 0 - r)) (Icc 0 Δ) := by
    apply hg.continuousOn.congr
    intro r hr
    simpa only [min_eq_right hr.2, max_eq_right hr.1] using (he r hr).symm
  have hi : IntervalIntegrable (fun r ↦ f (x 0 - r)) volume 0 Δ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hΔ]
    exact hfc.integrableOn_Icc
  calc
    _ = ∫ r in Icc 0 Δ, f (x 0 - r) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact he r hr
    _ = ∫ s in a..x 0, f s := integral_fixed_slab_eq_retarded (hout x hx).1
      (by linarith [(hout x hx).2]) f hi (fun s hs ↦ by
        simp only [f, graphOperator, hzero _ _ _ _ hs, Matrix.zero_mulVec, smul_zero, integral_zero])
    _ = _ := intervalIntegral.integral_smul _ _

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
