module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity.Integrand

/-!
# Fixed physical support of every mixed annular kernel derivative

The original masks supply this support without any differentiability premise.
Source: `app:ch_response:lem:energy-carrier-jets`. Consumer: the independent
annular kernel Sobolev deduction, after quantitative source integration.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Both observations vanish wherever the corresponding physical amplitude
vanishes, with the adjoint's two positions exchanged
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceKernelObservation_eq_zero_of_amplitude
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E)
    (hs : ∀ z, (if adj then A z x ξ else A x z ξ) = 0) :
    annularSourceKernelObservation adj demod Θ A π φ lam a x ξ = 0 := by
  cases adj <;> cases demod <;>
    simp_all [annularSourceKernelObservation, demodulatedForwardAnnularSourceKernel,
      demodulatedAdjointAnnularSourceKernel, forwardAnnularSourceKernel,
      adjointAnnularSourceKernel, forwardAnnularSourceAmplitude,
      adjointAnnularSourceAmplitude, annularComplementAmplitude, frequencyCutFullAmplitude]

/-- All evaluated external derivatives retain the same closed physical support,
uniformly in the parameter and unrestricted frequency. Directions in `P × E`
include all mixed carrier-parameter and output directions. No derivative support
is assumed (`app:ch_response:lem:energy-carrier-jets`). -/
theorem tsupport_iteratedFDeriv_annularSourceKernelObservation_subset
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    {X : Set E} (hX : IsClosed X)
    (hs : ∀ x ∉ X, ∀ z ξ, (if adj then A z x ξ else A x z ξ) = 0)
    (k : ℕ) (v : Fin k → P × E) (c : P) (ξ : E) :
    tsupport (fun x => iteratedFDeriv ℝ k (fun p : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v) ⊆ X := by
  apply closure_minimal _ hX
  intro x hx
  by_contra hxX
  have he : (fun p : P × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
      =ᶠ[𝓝 (c, x)] fun _ => (0 : F) := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hX.isOpen_compl.mem_nhds hxX)]
      with p hp
    exact annularSourceKernelObservation_eq_zero_of_amplitude adj demod Θ A π
      (φ p.1) lam (a p.1) p.2 ξ (fun z => hs p.2 hp z ξ)
  apply hx
  dsimp only
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  simp

/-- The elapsed kernels' actual mixed derivatives have fixed compact output
support from the original physical masks: `χout` forward and `χsource` adjoint.
The graph, masks, beta and selector stay fixed, while both `φ` and `a` vary.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem tsupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation_subset {d : ℕ}
    (adj demod : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : P → Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : P → Euclidean (d + 1) → F)
    (k : ℕ) (v : Fin k → P × Euclidean (d + 1)) (c : P) (ξ : Euclidean (d + 1)) :
    tsupport (fun x => iteratedFDeriv ℝ k (fun p : P × Euclidean (d + 1) =>
      annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v) ⊆ tsupport (if adj then χsource else χout) := by
  apply tsupport_iteratedFDeriv_annularSourceKernelObservation_subset
    adj demod _ _ π φ lam a (isClosed_tsupport _)
  intro x hx z η
  cases adj
  · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z η
      (Or.inl (image_eq_zero_of_notMem_tsupport hx))
  · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t z x η
      (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hx)))

/-- Compact support for every evaluated mixed derivative, for all four literal
elapsed kernels (`app:ch_response:lem:energy-carrier-jets`). -/
theorem hasCompactSupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation {d : ℕ}
    (adj demod : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : P → Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : P → Euclidean (d + 1) → F)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (k : ℕ) (v : Fin k → P × Euclidean (d + 1)) (c : P) (ξ : Euclidean (d + 1)) :
    HasCompactSupport (fun x => iteratedFDeriv ℝ k (fun p : P × Euclidean (d + 1) =>
      annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π (φ p.1) lam (a p.1) p.2 ξ)
        (c, x) v) := by
  have hmask : HasCompactSupport (if adj then χsource else χout) := by
    cases adj <;> assumption
  exact hmask.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation_subset
      adj demod Ψ b χout χsource β π φ t lam a k v c ξ)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
