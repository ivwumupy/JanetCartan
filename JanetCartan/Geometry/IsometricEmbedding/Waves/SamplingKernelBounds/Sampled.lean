module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Dyadic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Expectation

/-!
# Literal sampled expectations of the constructed kernels

Final assembly of the trace and compactness parts of
`app:ch_waves:eq:sampling-operator-bounds`. The intermediate operator continuity,
Hilbert–Schmidt summability and trace continuity hypotheses of `blockFamily`
are all proved from `BandKernelData`. Sampling weights, colors and nodes are
exactly those of `Sampling.ShiftLaw.Expectation`.

The stronger order-one expectation norm bound still requires the separate
normal-amplitude comparison. No such bound is inferred here from trace.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.SamplingKernelBounds.BandKernelData
open RawInputRealization SeparatedSampling Sampling Expectation

variable {n J p : ℕ}
  (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
  {ι δ : Type*} [Countable ι] (a : HilbertBasis ι ℂ (Output n))
  (b : HilbertBasis δ ℂ (Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)))
  (s : Finset (Fin J)) {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}
  (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
  (hψc : Continuous ψ) (hwc : Continuous w)

/-- The actual kernel rows with the literal separated-sampling weights; all
operator premises of the expectation helper are discharged
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def samplingFamily : WeightedFamily (F := Output n) b (ShiftIndex p B h) :=
  blockFamily b hw hψ hψc hwc (fun c z ↦ D.dyadicPrefix s (c, z))
    (fun _ ↦ (D.continuous_dyadicPrefix s).comp (continuous_const.prodMk continuous_id))
    (fun c z ↦ (D.dyadicPrefix_hilbertSchmidt a b s (c, z)).1)
    (fun _ ↦ (D.continuous_hilbertSchmidtSq_dyadicPrefix a b s).comp
      (continuous_const.prodMk continuous_id))

/-- The constructed expectation is exactly the manuscript's colored integral
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingFamily_expectation_eq_colors :
    (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation =
      ∑ c, ∫ z, (ψ z * colorMass p B h w c z) • atomNormal (D.dyadicPrefix s (c, z)) :=
  blockFamily_expectation_eq_colors ..

/-- The expectation uses the original samples, with no replacement of colors,
nodes, weights or row input (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingFamily_eq_sample_expectation (hh : 0 < h) :
    (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation =
      ∫ ω, ∑ t ∈ samples p B ψ w h (extendedShift ω),
        weight ψ w h (extendedShift ω) t •
          atomNormal (D.dyadicPrefix s (color p t.1, node h (extendedShift ω) t))
            ∂shiftLaw p B h :=
  blockFamily_eq_sample_expectation _ _ _ _ _ _ _ _ _ hh

/-- Literal Tonelli formula in terms of the actual band kernels
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_trace_eq :
    positiveTrace a (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation =
      ∑ q : ShiftIndex p B h, ∫ z, (ψ z * blockWeight w h q z) *
        (∑ i ∈ s, ∫ η, ‖D.column (i, (color p q, z)) η‖ ^ 2
          ∂annularMeasure n ((2 : ℝ) ^ i.val)) := by
  rw [WeightedFamily.trace_eq]
  simp only [samplingFamily, blockFamily, (D.dyadicPrefix_hilbertSchmidt a b s _).2]

/-- Uniform whole-output expectation trace, including the actual scalar mass
bound; the constant is independent of the mesh and prefix
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_trace_le (hn : 1 ≤ n) (hh : 0 < h) (hh₁ : h ≤ 1)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    positiveTrace a (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation ≤
      ((D.squaredKernelConstant * C_ceiling ^ n) *
        (countConstant p B * (P * W ^ 3))) * Λ ^ n :=
  blockFamily_trace_le_scale _ _ _ _ _ _ _ _ _ a hh hh₁ n Λ _
    (fun c z ↦ D.hilbertSchmidtSq_dyadicPrefix_le a b hn s (c, z) hceil)

/-- Positivity and compactness are consequences of the actual kernels and
weights, with no expectation-compactness premise
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_positive_compact :
    0 ≤ (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation ∧
      IsCompactOperator (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation :=
  ⟨WeightedFamily.expectation_nonneg _, WeightedFamily.expectation_compact _⟩

/-- All finite output compressions obey the same uniform trace estimate
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem samplingFamily_compression_trace_le (hn : 1 ≤ n) (hh : 0 < h) (hh₁ : h ≤ 1)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ)
    (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U] :
    Complex.re (LinearMap.trace ℂ U (finiteCompression U
      (D.samplingFamily a b s hw hψ hψc hwc (h := h)).expectation).toLinearMap) ≤
      ((D.squaredKernelConstant * C_ceiling ^ n) *
        (countConstant p B * (P * W ^ 3))) * Λ ^ n :=
  (WeightedFamily.trace_finiteCompression_le_trace _ a U).trans
    (D.samplingFamily_trace_le a b s hw hψ hψc hwc hn hh hh₁ hceil)

include a in
omit b hw hψ hψc hwc in
/-- Each literal positive sampling block is compact on the full output, as
required before centering for `HilbertOperatorBernstein`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_samplingBlock (q : Lattice) (u : Point) :
    IsCompactOperator (atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q u) := by
  change (∑ m ∈ integerCube (p + 2), _) ∈ compactOperator (RingHom.id ℂ) (Output n) (Output n)
  apply Submodule.sum_mem
  intro m _
  exact ((D.isCompactOperator_dyadicPrefix a s
    (color p q, node h (fun _ ↦ u) (q, m))).comp_clm
      (D.dyadicPrefix s (color p q, node h (fun _ ↦ u) (q, m))).adjoint).smul
        (weight ψ w h (fun _ ↦ u) (q, m))

include hw hψ in
omit a b [Countable ι] hψc hwc in
/-- The atomic-block norm bound with all row hypotheses discharged by the
single-band oscillatory input (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_samplingBlock_le {C_op C_ceiling Λ : ℝ} (hC : 0 ≤ C_op)
    (hband : ∀ i c z, ‖D.operator ((2 : ℝ) ^ i.val) (i, (c, z))‖ ^ 2 ≤
      C_op * (2 : ℝ) ^ i.val)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) (hh : 0 ≤ h) (q : Lattice) (u : Point) :
    ‖atomicBlock p ψ w h (fun c z ↦ D.dyadicPrefix s (c, z)) q u‖ ≤
      (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * ((C_op * C_ceiling) * Λ) :=
  norm_atomicBlock_le hw hψ hh _
    (fun c z ↦ D.norm_dyadicPrefix_sq_le s (c, z) hC (fun i ↦ hband i c z) hceil) q u

end JanetCartan.SamplingKernelBounds.BandKernelData
