module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.Pointwise
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.IntegralAlgebra

/-!
# The compact-frequency two-term conjugation identity

This assembles the actual normalized adjugate, the pointwise cancellation,
output differentiation and source integration by parts in
`app:ch_regular_base:eq:direct-graph-identity`. The phase and transport equations
and local regularity are explicit inputs of the phase/transport producers.
The smooth masked amplitude is an input of `jc-finite-fio-calculus`; it allows
symbols defined only on the nonzero covector chart. No inverse of `c` is used.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The two actual graph amplitudes of
`app:ch_regular_base:eq:direct-graph-amplitudes`, added in their original order. -/
def twoTermGraphAmplitude
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  leadingAmplitude (c (x, gradient (fun z ↦ S z η) x)) (U x η) +
    phaseCorrectionAmplitude c (fun z ↦ S z η) (fun z ↦ U z η) x

/-- The remainder in `app:ch_regular_base:eq:direct-graph-identity` uses the
actual output derivatives of the actual correction amplitude. -/
def twoTermGraphRemainder
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  transportRemainder (A x)
    (partialDeriv (phaseCorrectionAmplitude c (fun z ↦ S z η) (fun z ↦ U z η)) x)
    (B x) (phaseCorrectionAmplitude c (fun z ↦ S z η) (fun z ↦ U z η) x)

/-- Primitive inputs for one literal compact frequency regularization of
`app:ch_regular_base:eq:direct-graph-identity`. `H` is the real principal pencil;
its normalized adjugate is fixed, not an independently chosen matrix.
The phase and transport producers supply the eikonal/transport equations.
The finite FIO construction supplies smoothness after the frequency mask,
compact support, and regularity on each active covector chart. No field asserts
an operator identity or a differentiated symbol identity. -/
structure TwoTermGraphRegularization
    (H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : Euclidean n → ℂ) (O : Set (Euclidean n)) (t : Fin n) : Prop where
  output_open : IsOpen O
  cutoff_smooth : ContDiff ℝ ∞ χ
  cutoff_compact : HasCompactSupport χ
  phase_smooth : ContDiffOn ℝ ∞ (Function.uncurry S) (O ×ˢ univ)
  transport_smooth : ContDiffOn ℝ ∞ (Function.uncurry U) (O ×ˢ univ)
  amplitude_smooth : ContDiffOn ℝ ∞
    (fun p : Euclidean n × Euclidean n ↦ χ p.2 • twoTermGraphAmplitude
      (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U p.1 p.2)
    (O ×ˢ univ)
  symbol_differentiable : ∀ x ∈ O, ∀ η, χ η ≠ 0 → DifferentiableAt ℝ
    (fun q : Euclidean n × Euclidean n ↦
      (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal)
    (x, gradient (fun z ↦ S z η) x)
  symbol_chart : ∀ x ∈ O, ∀ η, χ η ≠ 0 → ∃ Ω : Set (Euclidean n),
    IsOpen Ω ∧ gradient (fun z ↦ S z η) x ∈ Ω ∧
    ContDiffOn ℝ 2 (fun ξ ↦ (normalizedAdjugateSymbol (H x) ξ).map Complex.ofReal) Ω ∧
    ContDiffOn ℝ 2 (fun ξ ↦ (normalizedDeterminantSymbol (H x) ξ : ℂ)) Ω
  eikonal : ∀ x ∈ O, ∀ η, χ η ≠ 0 →
    (normalizedDeterminantSymbol (H x) (gradient (fun z ↦ S z η) x) : ℂ) = (η t : ℂ)
  transport : ∀ x ∈ O, ∀ η, χ η ≠ 0 →
    (∑ j, partialDeriv (fun ξ ↦ (normalizedDeterminantSymbol (H x) ξ : ℂ))
      (gradient (fun z ↦ S z η) x) j • partialDeriv (fun z ↦ U z η) x j) +
    phaseTransportCoefficient (fun j ↦ complexifiedPencil (H x) (EuclideanSpace.single j 1))
      (B x) (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal)
      (fun ξ ↦ (normalizedDeterminantSymbol (H x) ξ : ℂ)) (fun z ↦ S z η) x * U x η = 0

/-- The actual correction is differentiable wherever the frequency mask is
nonzero. This discharges the correction-derivative input to the pointwise
cancellation from masked smoothness, without inverting the normalized symbol.
Source: `app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem TwoTermGraphRegularization.correction_differentiable
    {H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ}
    {B : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {S : Euclidean n → Euclidean n → ℝ}
    {U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {χ : Euclidean n → ℂ} {O : Set (Euclidean n)} {t : Fin n}
    (h : TwoTermGraphRegularization H B S U χ O t)
    (x : Euclidean n) (hx : x ∈ O) (η : Euclidean n) (hχ : χ η ≠ 0) :
    DifferentiableAt ℝ (phaseCorrectionAmplitude
      (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal)
      (fun z ↦ S z η) (fun z ↦ U z η)) x := by
  let c := fun q : Euclidean n × Euclidean n ↦
    (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal
  have hS : ContDiffAt ℝ 2 (fun z ↦ S z η) x :=
    ((h.phase_smooth.contDiffAt
      ((h.output_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hU : DifferentiableAt ℝ (fun z ↦ U z η) x :=
    ((h.transport_smooth.contDiffAt
      ((h.output_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hm : DifferentiableAt ℝ (fun z ↦ χ η • twoTermGraphAmplitude c S U z η) x :=
    ((h.amplitude_smooth.contDiffAt
      ((h.output_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ (fun z ↦ twoTermGraphAmplitude c S U z η) x := by
    have hi : DifferentiableAt ℝ
        (fun z ↦ (χ η)⁻¹ • (χ η • twoTermGraphAmplitude c S U z η)) x :=
      hm.const_smul (χ η)⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hχ, one_smul] using hi
  have hl : DifferentiableAt ℝ
      (fun z ↦ leadingAmplitude (c (z, gradient (fun w ↦ S w η) z)) (U z η)) x :=
    (((h.symbol_differentiable x hx η hχ).comp x
      ((differentiableAt_id (𝕜 := ℝ)).prodMk (differentiableAt_phase_gradient _ hS))).mul hU)
  have hd : DifferentiableAt ℝ (fun z ↦ twoTermGraphAmplitude c S U z η -
      leadingAmplitude (c (z, gradient (fun w ↦ S w η) z)) (U z η)) x := hb.sub hl
  simpa only [twoTermGraphAmplitude, add_sub_cancel_left] using hd

private theorem pencil_gradient_eq_sum
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → ℝ) (x : Euclidean n) :
    H (gradient S x) = ∑ j, ((partialDeriv S x j : ℝ) : ℂ) • H (EuclideanSpace.single j 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (gradient S x)]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    phase_gradient_apply, Complex.coe_smul]

/-- Pointwise cancellation with the actual frequency mask; the mask has no
output derivative. Consumed by `TwoTermGraphRegularization.conjugation`.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem TwoTermGraphRegularization.masked_amplitude_identity
    {H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ}
    {B : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {S : Euclidean n → Euclidean n → ℝ}
    {U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {χ : Euclidean n → ℂ} {O : Set (Euclidean n)} {t : Fin n}
    (h : TwoTermGraphRegularization H B S U χ O t) {x : Euclidean n} (hx : x ∈ O)
    (η : Euclidean n) :
    let c := fun q : Euclidean n × Euclidean n ↦
      (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal
    let A := fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)
    (∑ j, ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ) • A x j) *
        (χ η • twoTermGraphAmplitude c S U x η) +
      transportRemainder (A x)
        (fun j ↦ partialDeriv (fun z ↦ χ η • twoTermGraphAmplitude c S U z η) x j)
        (B x) (χ η • twoTermGraphAmplitude c S U x η) -
      (η t : ℂ) • (χ η • U x η) = χ η • twoTermGraphRemainder A B c S U x η := by
  dsimp only
  by_cases hχ : χ η = 0
  · simp [hχ, partialDeriv, transportRemainder]
  obtain ⟨Ω, hΩ, hξ, hcξ, hh⟩ := h.symbol_chart x hx η hχ
  have hS : ContDiffAt ℝ 2 (fun z ↦ S z η) x :=
    (((h.phase_smooth.contDiffAt
      ((h.output_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp))
  have hU : DifferentiableAt ℝ (fun z ↦ U z η) x :=
    ((h.transport_smooth.contDiffAt
      ((h.output_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have he := normalized_two_term_phase_amplitude_identity H (B x) (fun z ↦ S z η)
    (fun z ↦ U z η) x hΩ (η t : ℂ) (h.symbol_differentiable x hx η hχ)
    hcξ hh hS hU (h.correction_differentiable x hx η hχ) hξ
    (h.eikonal x hx η hχ) (h.transport x hx η hχ)
  have hb : DifferentiableAt ℝ (fun z ↦ twoTermGraphAmplitude
      (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) x :=
    (((h.symbol_differentiable x hx η hχ).comp x
      ((differentiableAt_id (𝕜 := ℝ)).prodMk (differentiableAt_phase_gradient _ hS))).mul hU).add
      (h.correction_differentiable x hx η hχ)
  have hd (j : Fin n) : partialDeriv (fun z ↦ χ η • twoTermGraphAmplitude
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) x j =
      χ η • partialDeriv (fun z ↦ twoTermGraphAmplitude
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) x j := by
    exact congrArg (fun L : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
      L (EuclideanSpace.single j 1)) (hb.hasFDerivAt.const_smul (χ η)).fderiv
  rw [← pencil_gradient_eq_sum]
  simp_rw [hd]
  have he' := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ ↦
    χ η • (M - (η t : ℂ) • U x η)) he
  simp only [add_sub_cancel_left] at he'
  simp only [twoTermGraphAmplitude, twoTermGraphRemainder, transportRemainder,
    Matrix.mul_smul, ← Finset.smul_sum, smul_sub, smul_add, neg_smul] at *
  simp only [smul_comm (η t : ℂ) (χ η), smul_comm (χ η) Complex.I,
    smul_neg, sub_eq_add_neg] at *
  simp only [Matrix.mul_add, Matrix.mul_smul, smul_add] at *
  convert he' using 1
  module

/-- The exact two-term graph conjugation for a compact frequency mask and a
smooth compactly supported source. All integral and symbol differentiations are
proved from the primitive inputs, with literal Euclidean measures and `(2π)⁻ⁿ`.
Source: `app:ch_regular_base:eq:direct-graph-identity`.
The consumers `jc-finite-fio-calculus` and `jc-regular-sector` must supply the
phase/transport solution and the regularity fields of the regularization. -/
theorem TwoTermGraphRegularization.conjugation
    {H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ}
    {B : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {S : Euclidean n → Euclidean n → ℝ}
    {U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {χ : Euclidean n → ℂ} {O : Set (Euclidean n)} {t : Fin n}
    (h : TwoTermGraphRegularization H B S U χ O t)
    {v : Euclidean n → Fin r → ℂ} (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    {x : Euclidean n} (hx : x ∈ O) :
    let c := fun q : Euclidean n × Euclidean n ↦
      (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal
    let A := fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)
    physicalOperator A B
        (graphOperator S (fun z _ η ↦ χ η • twoTermGraphAmplitude c S U z η) v) x -
      graphOperator S (fun z _ η ↦ χ η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x =
      graphOperator S (fun z _ η ↦ χ η • twoTermGraphRemainder A B c S U z η) v x := by
  dsimp only
  let c := fun q : Euclidean n × Euclidean n ↦
    (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal
  let A := fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)
  let b := fun z η ↦ χ η • twoTermGraphAmplitude c S U z η
  have hbK : ∀ z ∈ O, ∀ η ∉ tsupport χ, b z η = 0 := by
    intro z _ η hη
    simp [b, image_eq_zero_of_notMem_tsupport hη]
  have heK : ∀ z ∈ O, ∀ η ∉ tsupport χ, (η t : ℂ) • (χ η • U z η) = 0 := by
    intro z _ η hη
    simp [image_eq_zero_of_notMem_tsupport hη]
  have he : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean n ↦ (p.2 t : ℂ) • (χ p.2 • U p.1 p.2))
      (O ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj t : Euclidean n →L[ℝ] ℝ).contDiff.comp_contDiffOn contDiffOn_snd)).smul
      ((h.cutoff_smooth.comp_contDiffOn contDiffOn_snd).smul h.transport_smooth)
  rw [physicalOperator_graphOperator A B S b v h.output_open h.cutoff_compact
    h.phase_smooth h.amplitude_smooth hbK hv hvK hx,
    graphOperator_source_partialDeriv S (fun z η ↦ χ η • U z η) hv hvK x t]
  rw [← graphOperator_sub_of_integrable S
    (fun z _ η ↦ (∑ j, ((partialDeriv (fun w ↦ S w η) z j : ℝ) : ℂ) • A z j) * b z η +
      transportRemainder (A z) (fun j ↦ partialDeriv (fun w ↦ b w η) z j) (B z) (b z η))
    (fun z _ η ↦ (η t : ℂ) • (χ η • U z η)) v x
    (integrable_differentiated_graph_integrand A B (b := b) h.output_open h.cutoff_compact
      h.phase_smooth h.amplitude_smooth hbK hv hvK hx)
    (integrable_graph_integrand_of_compact (b := fun z η ↦ (η t : ℂ) • (χ η • U z η)) h.cutoff_compact h.phase_smooth he heK hv hvK hx)]
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards with η
  apply integral_congr_ae
  filter_upwards with y
  exact congrArg (fun M : Matrix (Fin r) (Fin r) ℂ ↦
    graphOscillation S x y η • M.mulVec (v y)) (h.masked_amplitude_identity hx η)


end JanetCartan.FourierIntegral
