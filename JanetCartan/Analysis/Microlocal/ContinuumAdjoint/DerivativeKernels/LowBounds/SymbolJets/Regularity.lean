module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.Basic
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Determinant
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Buffered smoothness for arbitrary modified amplitudes

Primitive regularity, the actual inverse identity, and a closed support buffer
give smoothness across chart boundaries in `app:ch_background:prop:bg-adjoint`.
The quantitative finite-jet estimate is a separate obligation.
-/

@[expose] public noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow ContinuumRow.TransportKernel NormalComparison

variable {n : ℕ}

/-- Primitive qualitative inputs for the modified normal in
`app:ch_background:prop:bg-adjoint`. Smoothness of the original amplitude is
joint in carrier, measurement, and frequency. No composed amplitude or
reciprocal-Jacobian product is an input. -/
structure PrimitiveRegularity (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) : Prop where
  coordinates : ContDiff ℝ ∞ g.coordinates
  amplitude : ContDiff ℝ ∞
    (fun q : CarrierParameter × (Euclidean n × Euclidean (n - 1)) ↦ a q.1 q.2.1 q.2.2)
  regularizer : ContDiff ℝ ∞ m
  jacobian : ContDiffOn ℝ ∞
    (fun p : JointVariables n ↦ g.jacobian p.1.1 p.1.2.1 p.2 p.1.2.2) g.inputDomain
  determinant_ne_zero : ∀ p ∈ g.inputDomain,
    (g.jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det ≠ 0
  output_open : IsOpen g.outputDomain
  inverse : ContDiffOn ℝ ∞
    (fun p : JointVariables n ↦ g.inverse p.1.1 p.1.2.1 p.2 p.1.2.2) g.outputDomain
  inverse_mem : MapsTo g.pull g.outputDomain g.inputDomain
  right_inverse : ∀ p ∈ g.outputDomain, g.push (g.pull p) = p

/-- Primitive support and its geometric buffer for
`app:ch_background:prop:bg-adjoint`. `L` can be the product of the fixed compact
measurement/carrier/angular supports with the high-frequency cone. It need
not be compact in frequency. These are support conditions on the original
amplitude and the forward chart, never on the final normal. -/
structure BufferedSupport (g : Chart n) (a : AdjointAmplitude n)
    (L : Set (JointVariables n)) : Prop where
  input_support : ∀ p ∈ g.inputDomain,
    a (g.carrier p).1 p.1.1 (g.carrier p).2 ≠ 0 →
    a (g.carrier p).1 p.1.2.1 (g.carrier p).2 ≠ 0 → p ∈ L
  image_closed : IsClosed (g.push '' L)
  image_subset : g.push '' L ⊆ g.outputDomain

/-- Fixed coordinate identification preserves joint smoothness before the
inverse substitution (`app:ch_background:prop:bg-adjoint`). -/
theorem Chart.carrier_contDiff (g : Chart n) (he : ContDiff ℝ ∞ g.coordinates) :
    ContDiff ℝ ∞ g.carrier :=
  ((he.comp contDiff_fst.snd.snd).fst.prodMk contDiff_snd).prodMk
    (he.comp contDiff_fst.snd.snd).snd

/-- The actual joint inverse substitution is smooth on its open image
(`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.pull_contDiffOn {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ g.pull g.outputDomain :=
  (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.fst.prodMk h.inverse)).prodMk
    contDiffOn_snd

/-- Smoothness of the original full density divided by the absolute
Jacobian is derived from primitives (`app:ch_background:prop:bg-adjoint`). -/
theorem PrimitiveRegularity.inputDensity_contDiffOn {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} (h : PrimitiveRegularity g a m) :
    ContDiffOn ℝ ∞ (inputDensity g a m) g.inputDomain := by
  have hc := g.carrier_contDiff h.coordinates
  have hl := h.amplitude.comp (hc.fst.prodMk (contDiff_fst.fst.prodMk hc.snd))
  have hr := h.amplitude.comp (hc.fst.prodMk (contDiff_fst.snd.fst.prodMk hc.snd))
  have hm := Complex.ofRealCLM.contDiff.comp (h.regularizer.comp hc)
  have hj : ContDiffOn ℝ ∞ (fun p : JointVariables n ↦
      |(g.jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det|⁻¹) g.inputDomain := by
    apply ((contDiff_normalJacobianDet.comp_contDiffOn h.jacobian).abs
      h.determinant_ne_zero).inv
    exact fun p hp ↦ abs_ne_zero.mpr (h.determinant_ne_zero p hp)
  exact hj.smul ((hm.pow 2).mul ((Complex.conjCLE.contDiff.comp hl).mul hr)).contDiffOn

/-- Nonvanishing of the actual density forces nonvanishing of both original
amplitudes (`app:ch_background:prop:bg-adjoint`). -/
theorem inputDensity_ne_zero_amplitudes (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (p : JointVariables n)
    (hp : inputDensity g a m p ≠ 0) :
    a (g.carrier p).1 p.1.1 (g.carrier p).2 ≠ 0 ∧
      a (g.carrier p).1 p.1.2.1 (g.carrier p).2 ≠ 0 := by
  constructor <;> intro hz <;>
    exact hp (by simp [inputDensity, modifiedNormalDensity, hz])

/-- Transport of the primitive support by the actual right inverse in
`app:ch_background:prop:bg-adjoint`. -/
theorem support_inverseDensity_subset {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    (h : PrimitiveRegularity g a m) (hs : BufferedSupport g a L) :
    support (inverseDensity g a m) ⊆ g.push '' L := by
  rw [inverseDensity_eq_indicator]
  intro p hp
  have hpΩ : p ∈ g.outputDomain := by
    by_contra hn
    exact hp (indicator_of_notMem hn _)
  have hi : inputDensity g a m (g.pull p) ≠ 0 := by
    simpa only [mem_support, indicator_of_mem hpΩ, comp_apply] using hp
  obtain ⟨hl, hr⟩ := inputDensity_ne_zero_amplitudes g a m (g.pull p) hi
  exact ⟨g.pull p, hs.input_support _ (h.inverse_mem hpΩ) hl hr, h.right_inverse p hpΩ⟩

/-- The closed primitive image buffer also contains the topological support
(`app:ch_background:prop:bg-adjoint`). -/
theorem tsupport_inverseDensity_subset {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    (h : PrimitiveRegularity g a m) (hs : BufferedSupport g a L) :
    tsupport (inverseDensity g a m) ⊆ g.outputDomain :=
  (closure_minimal (support_inverseDensity_subset h hs) hs.image_closed).trans hs.image_subset

/-- Smooth zero extension of the actual full density, including every
chart boundary, from primitive inputs (`app:ch_background:prop:bg-adjoint`). -/
theorem inverseDensity_contDiff {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    (h : PrimitiveRegularity g a m) (hs : BufferedSupport g a L) :
    ContDiff ℝ ∞ (inverseDensity g a m) := by
  apply Localization.contDiff_of_contDiffOn_support_neighborhood h.output_open
  · apply (h.inputDensity_contDiffOn.comp h.pull_contDiffOn h.inverse_mem).congr
    intro p hp
    rw [inverseDensity_eq_indicator, indicator_of_mem hp]
  · exact tsupport_inverseDensity_subset h hs

/-- All jets vanish off the chart by the primitive support buffer, as used
to globalize the finite symbol bound (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedFDeriv_inverseDensity_eq_zero {g : Chart n} {a : AdjointAmplitude n}
    {m : CarrierVariable n → ℝ} {L : Set (JointVariables n)}
    (h : PrimitiveRegularity g a m) (hs : BufferedSupport g a L)
    {p : JointVariables n} (hp : p ∉ g.outputDomain) (j : ℕ) :
    iteratedFDeriv ℝ j (inverseDensity g a m) p = 0 := by
  have he := notMem_tsupport_iff_eventuallyEq.mp
    (fun hm ↦ hp (tsupport_inverseDensity_subset h hs hm))
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
