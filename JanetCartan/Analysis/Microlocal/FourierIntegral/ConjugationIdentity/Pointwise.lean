module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.PhaseAmplitude
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.ComplexNormalization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Differential
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel

/-!
# Realizing the two-term graph transport cancellation

The pointwise identity below realizes the derivative arrays in `Transport` by
actual derivatives of a supplied phase, symbol and transport matrix. Its inputs
are the symbol identity, eikonal equation, transport equation and local
regularity. These are inputs of the Hamilton phase and transport constructions,
not conclusions of this module.

The `Compact` module combines this pointwise identity with the checked graph
differentiation and source integration-by-parts leaves to obtain the literal
compact-frequency operator identity. Passage to an unregularized distributional
identity remains a separate obligation.
-/

@[expose] public noncomputable section

open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

/-- The actual correction amplitude in
`app:ch_regular_base:eq:direct-graph-amplitudes`, with all covector derivatives
evaluated at the gradient of the supplied phase. -/
def phaseCorrectionAmplitude
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → ℝ) (U : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  correctionAmplitude
    (partialDeriv (fun ξ ↦ c (x, ξ)) (gradient S x)) (partialDeriv U x)
    (fun j l ↦ partialDeriv (fun ξ ↦ partialDeriv (fun ζ ↦ c (x, ζ)) ξ l)
      (gradient S x) j)
    (fun j l ↦ ((partialDeriv (fun z ↦ partialDeriv S z l) x j : ℝ) : ℂ)) (U x)

/-- The effective coefficient evaluated at the actual phase covector.
Spatial derivatives of `c` hold that covector fixed, as required in
`app:ch_regular_base:eq:actual-effective-transport`. -/
def phaseTransportCoefficient
    (A : Fin n → Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin r) ℂ)
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (h : Euclidean n → ℂ) (S : Euclidean n → ℝ) (x : Euclidean n) :
    Matrix (Fin r) (Fin r) ℂ :=
  transportCoefficient A (partialDeriv (fun z ↦ c (z, gradient S x)) x) B
    (c (x, gradient S x))
    (fun j l ↦ ((partialDeriv (fun z ↦ partialDeriv S z l) x j : ℝ) : ℂ))
    (fun j l ↦ partialDeriv (fun ξ ↦ partialDeriv h ξ l) (gradient S x) j)

/-- Pointwise realization of the two-term cancellation in
`app:ch_regular_base:eq:direct-graph-identity`. The first two differentiated
symbol identities and Hessian symmetry are proved from the supplied functions;
the remainder uses the actual derivative of `phaseCorrectionAmplitude`.
The graph integral and its limiting construction are not asserted here. -/
theorem two_term_phase_amplitude_identity
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin r) (Fin r) ℂ)
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (h : Euclidean n → ℂ) (S : Euclidean n → ℝ)
    (U : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) {x : Euclidean n}
    (hc : DifferentiableAt ℝ c (x, gradient S x))
    (hcξ : ContDiffOn ℝ 2 (fun ξ ↦ c (x, ξ)) Ω) (hh : ContDiffOn ℝ 2 h Ω)
    (hS : ContDiffAt ℝ 2 S x) (hU : DifferentiableAt ℝ U x)
    (hb : DifferentiableAt ℝ (phaseCorrectionAmplitude c S U) x)
    (hchart : gradient S x ∈ Ω)
    (hsymbol : ∀ ξ ∈ Ω, H ξ * c (x, ξ) = h ξ • 1)
    (e : ℂ) (heikonal : h (gradient S x) = e)
    (htransport : (∑ j, partialDeriv h (gradient S x) j • partialDeriv U x j) +
      phaseTransportCoefficient (fun j ↦ H (EuclideanSpace.single j 1)) B c h S x * U x = 0) :
    H (gradient S x) *
        (leadingAmplitude (c (x, gradient S x)) (U x) + phaseCorrectionAmplitude c S U x) -
      Complex.I • ((∑ j, H (EuclideanSpace.single j 1) *
        partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z) +
          phaseCorrectionAmplitude c S U z) x j) +
        B * (leadingAmplitude (c (x, gradient S x)) (U x) + phaseCorrectionAmplitude c S U x)) =
      e • U x + transportRemainder (fun j ↦ H (EuclideanSpace.single j 1))
        (partialDeriv (phaseCorrectionAmplitude c S U) x) B (phaseCorrectionAmplitude c S U x) := by
  have hlead : DifferentiableAt ℝ
      (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z)) x :=
    (hc.comp x ((differentiableAt_id (𝕜 := ℝ) (x := x)).prodMk (differentiableAt_phase_gradient S hS))).mul hU
  have hadd (j : Fin n) :
      partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z) +
        phaseCorrectionAmplitude c S U z) x j =
      leadingAmplitudeDerivative (c (x, gradient S x)) (U x)
        (partialDeriv (fun z ↦ c (z, gradient S x)) x)
        (partialDeriv (fun ξ ↦ c (x, ξ)) (gradient S x)) (partialDeriv U x)
        (fun k l ↦ ((partialDeriv (fun z ↦ partialDeriv S z l) x k : ℝ) : ℂ)) j +
        partialDeriv (phaseCorrectionAmplitude c S U) x j := by
    have hd := congrArg (fun L : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
      L (EuclideanSpace.single j 1))
      (hlead.hasFDerivAt.add hb.hasFDerivAt).fderiv
    change partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z) +
        phaseCorrectionAmplitude c S U z) x j =
      partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z)) x j +
        partialDeriv (phaseCorrectionAmplitude c S U) x j at hd
    rw [partialDeriv_leadingAmplitude_phase c S U hc hS hU] at hd
    exact hd
  simp only [hadd]
  apply two_term_transport_identity
  · intro j l
    exact congrArg Complex.ofReal (phase_secondPartialDeriv_symm S hS j l)
  · rw [hsymbol _ hchart, heikonal]
  · intro j
    apply pencil_mul_partialDeriv
    · exact (hcξ.contDiffAt (hΩ.mem_nhds hchart)).differentiableAt (by norm_num)
    · exact (hh.contDiffAt (hΩ.mem_nhds hchart)).differentiableAt (by norm_num)
    · filter_upwards [hΩ.mem_nhds hchart] with ξ hξ using hsymbol ξ hξ
  · exact pencil_mul_secondPartialDeriv H _ h hΩ hcξ hh hsymbol hchart
  · exact htransport

/-- The pointwise two-term identity for the actual normalized adjugate of a
real principal pencil. The symbol identity is discharged by normalization,
not assumed. Only local regularity, the eikonal and the full transport equation
remain inputs from the actual phase and transport producers.
Source: `app:ch_regular_base:eq:direct-graph-amplitudes` and
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem normalized_two_term_phase_amplitude_identity
    (H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin r) ℂ) (S : Euclidean n → ℝ)
    (U : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x : Euclidean n) {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (e : ℂ) :
    let c := fun p : Euclidean n × Euclidean n ↦
      (normalizedAdjugateSymbol (H p.1) p.2).map Complex.ofReal
    let h := fun ξ ↦ (normalizedDeterminantSymbol (H x) ξ : ℂ)
    let A := fun j ↦ complexifiedPencil (H x) (EuclideanSpace.single j 1)
    DifferentiableAt ℝ c (x, gradient S x) →
    ContDiffOn ℝ 2 (fun ξ ↦ c (x, ξ)) Ω → ContDiffOn ℝ 2 h Ω →
    ContDiffAt ℝ 2 S x → DifferentiableAt ℝ U x →
    DifferentiableAt ℝ (phaseCorrectionAmplitude c S U) x →
    gradient S x ∈ Ω → h (gradient S x) = e →
    (∑ j, partialDeriv h (gradient S x) j • partialDeriv U x j) +
      phaseTransportCoefficient A B c h S x * U x = 0 →
    complexifiedPencil (H x) (gradient S x) *
        (leadingAmplitude (c (x, gradient S x)) (U x) + phaseCorrectionAmplitude c S U x) -
      Complex.I • ((∑ j, A j *
        partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z) +
          phaseCorrectionAmplitude c S U z) x j) +
        B * (leadingAmplitude (c (x, gradient S x)) (U x) + phaseCorrectionAmplitude c S U x)) =
      e • U x + transportRemainder A (partialDeriv (phaseCorrectionAmplitude c S U) x)
        B (phaseCorrectionAmplitude c S U x) := by
  dsimp only
  intro hc hcξ hh hS hU hb hchart heikonal htransport
  exact two_term_phase_amplitude_identity (complexifiedPencil (H x)) B _ _ S U hΩ
    hc hcξ hh hS hU hb hchart
    (fun ξ _ ↦ complexifiedPencil_mul_normalizedAdjugateSymbol (H x) ξ)
    e heikonal htransport

end JanetCartan.FourierIntegral

