module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.Regularity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Integration

/-!
# Compact support and spectator differentiation of the modified normal

For `app:ch_background:prop:bg-adjoint`, support in both measurement positions,
joint smoothness, and differentiation of the literal full spectator integral
are consequences of primitive support and regularity. The final estimate still
requires a quantitative primitive symbol-jet calculation.
-/

@[expose] public noncomputable section

open Set Function MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow

variable {n : ℕ}

/-- Common compact measurement and spectator supports of the original
amplitude in `app:ch_background:prop:bg-adjoint`. No support condition is
imposed on the final normal. Compact carrier support implies this spectator
condition by projection. -/
structure CompactSupports (a : AdjointAmplitude n)
    (X : Set (Euclidean n)) (K : Set (Euclidean 2)) : Prop where
  measurement_compact : IsCompact X
  spectator_compact : IsCompact K
  amplitude_support : ∀ z x η, a z x η ≠ 0 → x ∈ X ∧ z.2 ∈ K

/-- Both primitive amplitude factors vanish outside their common measurement
support (`app:ch_background:prop:bg-adjoint`). -/
theorem inverseDensity_eq_zero_of_not_mem_measurement
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (p : JointVariables n) (hp : p.1.1 ∉ X ∨ p.1.2.1 ∉ X) :
    inverseDensity g a m p = 0 := by
  rw [inverseDensity_eq_indicator]
  by_cases hd : p ∈ g.outputDomain
  · rw [indicator_of_mem hd]
    by_contra hn
    obtain ⟨hl, hr⟩ := inputDensity_ne_zero_amplitudes g a m (g.pull p) hn
    rcases hp with hx | hy
    · exact hx (hs.amplitude_support _ _ _ hl).1
    · exact hy (hs.amplitude_support _ _ _ hr).1
  · exact indicator_of_notMem hd _

/-- The literal inverse density vanishes outside the primitive compact
spectator support (`app:ch_background:prop:bg-adjoint`). -/
theorem inverseDensity_eq_zero_of_not_mem_spectator
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (p : JointVariables n) (hp : p.2 ∉ K) : inverseDensity g a m p = 0 := by
  rw [inverseDensity_eq_indicator]
  by_cases hd : p ∈ g.outputDomain
  · rw [indicator_of_mem hd]
    by_contra hn
    obtain ⟨hl, _⟩ := inputDensity_ne_zero_amplitudes g a m (g.pull p) hn
    exact hp (hs.amplitude_support _ _ _ hl).2
  · exact indicator_of_notMem hd _

/-- The actual full Lebesgue integral equals the fixed compact integral,
without an integrability premise (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalAmplitude_eq_compactIntegral
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K) :
    physicalAmplitude g a m = fun p ↦ ∫ v in K, inverseDensity g a m (p, v) := by
  funext p
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun v hv ↦ inverseDensity_eq_zero_of_not_mem_spectator g a m hs (p, v) hv)).symm

/-- Each actual spectator section is integrable; compactness and primitive
smoothness supply this obligation (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_inverseDensity {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) (p : Variables n) :
    Integrable (fun v ↦ inverseDensity g a m (p, v)) := by
  apply ((inverseDensity_contDiff h hb).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact HasCompactSupport.intro hs.spectator_compact
    (fun v hv ↦ inverseDensity_eq_zero_of_not_mem_spectator g a m hs (p, v) hv)

/-- The actual physical normal is smooth in both positions and frequency,
including the inverse-chart boundary (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalAmplitude_contDiff {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) : ContDiff ℝ ∞ (physicalAmplitude g a m) := by
  rw [physicalAmplitude_eq_compactIntegral g a m hs]
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hs.spectator_compact.measure_lt_top.ne
  apply contDiffOn_univ.mp
  exact contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ
    hs.spectator_compact (subset_univ K) (inverseDensity_contDiff h hb).contDiffOn

/-- Every actual joint jet passes through the compact spectator integral.
All domination and integrability follow from primitive inputs; no interchange
assumption is introduced (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedFDeriv_physicalAmplitude {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) (j : ℕ) (p : Variables n) :
    iteratedFDeriv ℝ j (physicalAmplitude g a m) p =
      ∫ v in K, iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p := by
  rw [physicalAmplitude_eq_compactIntegral g a m hs]
  exact ContinuumNormalReduction.TransportSymbol.iteratedFDeriv_spectatorIntegral
    hs.spectator_compact j (inverseDensity_contDiff h hb) p

/-- Transfer of a density-jet estimate through the spectator integral. This
lemma is only the integration step: the quantitative primitive-jet producer
must prove `hjet` before the final bound in `app:ch_background:prop:bg-adjoint`
can use it. -/
theorem norm_iteratedFDeriv_physicalAmplitude_le {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) (j : ℕ) (p : Variables n) {B : ℝ}
    (hjet : ∀ v ∈ K, ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (physicalAmplitude g a m) p‖ ≤ B * volume.real K := by
  rw [iteratedFDeriv_physicalAmplitude h hb hs]
  exact norm_setIntegral_le_of_norm_le_const hs.spectator_compact.measure_lt_top hjet

/-- Both independent measurement positions retain the original common
support after spectator integration (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalAmplitude_eq_zero_of_not_mem_measurement
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (p : Variables n) (hp : p.1 ∉ X ∨ p.2.1 ∉ X) : physicalAmplitude g a m p = 0 := by
  change (∫ v, inverseDensity g a m (p, v)) = 0
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun v ↦
    inverseDensity_eq_zero_of_not_mem_measurement g a m hs (p, v) hp

/-- The physical amplitude has common compact support in the pair of
measurement positions, uniformly in frequency and regularization
(`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_physicalAmplitude_positions
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (k : Euclidean n) :
    HasCompactSupport (fun z : Euclidean n × Euclidean n ↦
      physicalAmplitude g a m (z.1, z.2, k)) := by
  apply HasCompactSupport.intro (hs.measurement_compact.prod hs.measurement_compact)
  intro z hz
  exact physicalAmplitude_eq_zero_of_not_mem_measurement g a m hs _ (not_and_or.mp hz)

/-- Smoothness of the normalized amplitude with the exact frequency
substitution `η_normal = 2π ξ` (`app:ch_background:prop:bg-adjoint`). -/
theorem cyclesAmplitude_contDiff {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)}
    (h : PrimitiveRegularity g a m) (hb : BufferedSupport g a L)
    (hs : CompactSupports a X K) : ContDiff ℝ ∞ (cyclesAmplitude g a m) :=
  contDiff_const.mul ((physicalAmplitude_contDiff h hb hs).comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul (2 * Real.pi)))))

/-- Exact common measurement support for the normalized amplitude
(`app:ch_background:prop:bg-adjoint`). -/
theorem cyclesAmplitude_eq_zero_of_not_mem_measurement
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (p : Variables n) (hp : p.1 ∉ X ∨ p.2.1 ∉ X) : cyclesAmplitude g a m p = 0 := by
  simp only [cyclesAmplitude, physicalAmplitude_eq_zero_of_not_mem_measurement g a m hs
    (p.1, p.2.1, (2 * Real.pi) • p.2.2) hp, mul_zero]

/-- Compact support in both measurement positions survives the full
normalization (`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_cyclesAmplitude_positions
    (g : Chart n) (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (hs : CompactSupports a X K)
    (ξ : Euclidean n) :
    HasCompactSupport (fun z : Euclidean n × Euclidean n ↦
      cyclesAmplitude g a m (z.1, z.2, ξ)) := by
  apply HasCompactSupport.intro (hs.measurement_compact.prod hs.measurement_compact)
  intro z hz
  exact cyclesAmplitude_eq_zero_of_not_mem_measurement g a m hs _ (not_and_or.mp hz)

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
