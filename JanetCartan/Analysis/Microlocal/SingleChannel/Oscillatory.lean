module

public import JanetCartan.Analysis.Microlocal.SingleChannel.Assembly

/-!
# The original phase–amplitude single channel

Constructs the actual integral in `app:ch_osc:prop:osc-channel`. Only continuity
of the phase near the amplitude support is used for this construction. The
buffered slice data carry the manuscript's smoothness and finite jet assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace JanetCartan.SingleChannel
open NormalComparison
variable {d r : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "X" => ℝ × EuclideanSpace ℝ (Fin d)

/-- The literal kernel with the physical dimension's normalization
(`app:ch_osc:prop:osc-channel`). -/
def oscillatoryChannelKernel (K : ℝ) (φ : X → Y → ℝ) (a : X → Y → V)
    (x : X) (u : Y) : V :=
  ((normalOperatorScale (d + 1) K : ℂ) * oscillatoryFactor K (φ x u)) • a x u

/-- Continuity is needed only near the compact amplitude support; no global
extension of the phase is assumed (`app:ch_osc:prop:osc-channel`). -/
theorem continuous_oscillatoryChannelKernel
    (K : ℝ) (φ : X → Y → ℝ) (a : X → Y → V)
    (ha : Continuous (Function.uncurry a))
    (hφ : ∀ p ∈ tsupport (Function.uncurry a), ContinuousAt (Function.uncurry φ) p) :
    Continuous (Function.uncurry (oscillatoryChannelKernel K φ a)) := by
  apply continuous_of_tsupport
  intro p hp
  have hsub : tsupport (Function.uncurry (oscillatoryChannelKernel K φ a)) ⊆
      tsupport (Function.uncurry a) := tsupport_smul_subset_right _ _
  have hc := hφ p (hsub hp)
  have he : ContinuousAt (fun q : X × Y ↦
      (normalOperatorScale (d + 1) K : ℂ) * oscillatoryFactor K (φ q.1 q.2)) p := by
    unfold oscillatoryFactor
    fun_prop
  exact he.smul ha.continuousAt

/-- Oscillation and normalization preserve the compact amplitude support
(`app:ch_osc:prop:osc-channel`). -/
theorem hasCompactSupport_oscillatoryChannelKernel
    (K : ℝ) (φ : X → Y → ℝ) (a : X → Y → V)
    (ha : HasCompactSupport (Function.uncurry a)) :
    HasCompactSupport (Function.uncurry (oscillatoryChannelKernel K φ a)) := by
  apply HasCompactSupport.of_support_subset_isCompact ha
  intro p hp
  by_contra hn
  have hz : a p.1 p.2 = 0 := image_eq_zero_of_notMem_tsupport (f := Function.uncurry a) hn
  exact hp (by simp [Function.uncurry, oscillatoryChannelKernel, hz])

/-- The constructed integral has exactly the displayed prefactor and original
phase and amplitude of `app:ch_osc:prop:osc-channel`, on every L² input. -/
theorem channelIntegral_oscillatoryChannelKernel
    {μ : Measure (EuclideanSpace ℝ (Fin d))}
    (K : ℝ) (φ : X → Y → ℝ) (a : X → Y → V) (f : Lp ℂ 2 μ) (x : X) :
    channelIntegral (oscillatoryChannelKernel K φ a) f x =
      (normalOperatorScale (d + 1) K : ℂ) •
        ∫ u, (oscillatoryFactor K (φ x u) * f u) • a x u ∂μ := by
  rw [channelIntegral, ← integral_smul]
  congr 1
  funext u
  simp only [oscillatoryChannelKernel, smul_smul]
  congr 1
  ring

/-- Full-space oscillatory single-channel estimate in
`app:ch_osc:prop:osc-channel`, in every positive slice dimension, including
`d = 1`. All analytic operator estimates are discharged. The input hypotheses
concern only the original phase, amplitude and buffered slice charts.
The constant is uniform over all slice families with the same geometry and
finite input jet bounds `C`, hence also over any carrier parameter indexing
such families. No slice or channel norm estimate is assumed. -/
theorem exists_oscillatorySingleChannelOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      ∀ ε ∈ Icc 0 G.ε₀, ∀ K ≥ 1,
      ∀ (φ : X → Y → ℝ) (amp : X → Y → V),
        Continuous (Function.uncurry amp) → HasCompactSupport (Function.uncurry amp) →
        (∀ p ∈ tsupport (Function.uncurry amp), ContinuousAt (Function.uncurry φ) p) →
        (∀ t ∉ Ioo a b, ∀ y u, amp (t, y) u = 0) →
        (∀ t (ht : t ∈ Ioo a b) y u, φ (t, y) u = (F t ht).phase ε y u) →
        (∀ t (ht : t ∈ Ioo a b) y u i, amp (t, y) u i = (F t ht).amplitude ε y u i) →
        ∃ L : Lp ℂ 2 (volume.restrict G.D) →L[ℂ] Lp V 2 (volume : Measure X),
          (∀ f, L f =ᵐ[volume] fun x ↦
            (normalOperatorScale (d + 1) K : ℂ) •
              ∫ u in G.D, (oscillatoryFactor K (φ x u) * f u) • amp x u) ∧
          ‖L‖ ^ 2 ≤ B * K ∧ ‖realQuadratureChannel L‖ ^ 2 ≤ 4 * (B * K) := by
  obtain ⟨B, hB, hchannel⟩ := exists_singleChannelOperator G C a b hab
  refine ⟨B, hB, ?_⟩
  intro F ε hε K hK φ amp ha hs hφ htime hphase hamp
  obtain ⟨L, hL, hb, hr⟩ := hchannel F ε hε K hK
    (oscillatoryChannelKernel K φ amp)
    (continuous_oscillatoryChannelKernel K φ amp ha hφ)
    (hasCompactSupport_oscillatoryChannelKernel K φ amp hs)
    (fun t ht y u ↦ by simp [oscillatoryChannelKernel, htime t ht y u])
    (fun t ht y u i ↦ by
      simp only [oscillatoryChannelKernel, PiLp.smul_apply, smul_eq_mul,
        hphase t ht, hamp t ht])
  refine ⟨L, ?_, hb, hr⟩
  intro f
  exact (hL f).trans (Eventually.of_forall
    (channelIntegral_oscillatoryChannelKernel K φ amp f))

end JanetCartan.SingleChannel
