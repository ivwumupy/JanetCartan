module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity.Differentiation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity.OutputSupport
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Geometry.Locality
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support

/-!
# Primitive regularity of the actual elapsed annular kernels

This closes the qualitative inputs to the annular kernel-jet assembly in
`app:ch_response:lem:energy-carrier-jets`, for the literal elapsed graph of
`app:ch_response:eq:direct-envelope-profile`. The graph phase is smooth only on
the supported chart. The carrier phase is smooth only near the fixed source and
observation supports. Every input to source differentiation is derived below
from those primitive smoothness statements, the original masks, and the fixed
compact envelope support. No quantitative jet bound or frequency integrability
is assumed or asserted here.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open SymbolBudgets
variable {d r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)

omit [FiniteDimensional ℝ P] in
private theorem contDiff_elapsedAnnularAmplitude_entries
    (b : TwoTimeAmplitude d r) (χout χsource β : E → ℂ)
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (t : ℝ) (i j : Fin r) :
    ContDiff ℝ ∞ (fun q : E × E × E =>
      elapsedAmplitude b χout χsource β t q.1 q.2.1 q.2.2 i j) := by
  have h := (contDiff_uncurry_elapsedAmplitude b χout χsource β hb ho hs hβ t).comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  let L : Matrix (Fin r) (Fin r) ℂ →L[ℝ] ℂ :=
    ((LinearMap.proj j : (Fin r → ℂ) →ₗ[ℝ] ℂ).comp
      (LinearMap.proj i : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] (Fin r → ℂ))).toContinuousLinearMap
  exact L.contDiff.comp h

/-- Joint regularity, frequency measurability, all finite source-integral
interchanges, and fixed compact physical support for the four literal elapsed
kernels. `adj = false/true` selects forward/adjoint; `demod = false/true` selects
physical/demodulated observation. The actual output carrier is differentiated
on the right side as part of `annularSourceIntegrand`.

All hypotheses concern the original two-time phase, original two-time amplitude,
original masks/beta/selector, and original varying carrier phase and envelope.
The closed phase support uses the intersection of beta support with the original
spatial symbol support `Fη`, retaining its lower cutoff. Both may be unbounded
in frequency. The fixed graph, both
masks, beta, selector and lambda are unchanged by the external derivatives.
Consumer: quantitative annular kernel assembly and its independent Sobolev
consequence; sources: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem elapsedAnnularSourceKernelObservation_regularity
    (adj demod : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (φ : P → E → ℝ) (t lam : ℝ) (a : P → E → F)
    {U : Set P} (hU : IsOpen U)
    {X : Set E} {W : Set (Euclidean d)} (hX : IsOpen X) (hW : IsOpen W)
    (hχX : tsupport χout ⊆ X)
    {Fη : Set (Euclidean d)} (hFη : IsClosed Fη)
    (hbF : ∀ t s y η, η ∉ Fη → b t s y η = 0)
    (hβW : ∀ ξ ∈ tsupport β, spatialPart ξ ∈ Fη → spatialPart ξ ∈ W)
    (hΨ : ∀ x ∈ X, ∀ η ∈ W, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) => Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - t), (spatialPart x, η)))
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {V K : Set E} (hV : IsOpen V) (hK : IsCompact K)
    (hKV : K ⊆ V) (houtV : tsupport χout ⊆ V) (hsourceV : tsupport χsource ⊆ V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (U ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (a c) ⊆ K) :
    let Θ := elapsedPhase Ψ t
    let A := elapsedAmplitude b χout χsource β t
    ContDiffOn ℝ ∞ (fun p : (P × E) × E =>
      annularSourceKernelObservation adj demod Θ A π (φ p.1.1) lam (a p.1.1) p.1.2 p.2)
      ((U ×ˢ univ) ×ˢ univ) ∧
    (∀ c ∈ U, ∀ x, StronglyMeasurable (fun ξ =>
      annularSourceKernelObservation adj demod Θ A π (φ c) lam (a c) x ξ)) ∧
    ∀ (k : ℕ) (v : Fin k → P × E) (c : P), c ∈ U →
      (∀ x ξ, Integrable (fun z => iteratedFDeriv ℝ k (fun p : P × E =>
          annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z) (c, x) v) ∧
        iteratedFDeriv ℝ k (fun p : P × E =>
          annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ)
            (c, x) v =
          ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ z,
            iteratedFDeriv ℝ k (fun p : P × E =>
              annularSourceIntegrand adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ z) (c, x) v) ∧
      (∀ x, StronglyMeasurable (fun ξ => iteratedFDeriv ℝ k (fun p : P × E =>
        annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ) (c, x) v)) ∧
      (∀ ξ, tsupport (fun x => iteratedFDeriv ℝ k (fun p : P × E =>
          annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ) (c, x) v)
            ⊆ tsupport (if adj then χsource else χout) ∧
        HasCompactSupport (fun x => iteratedFDeriv ℝ k (fun p : P × E =>
          annularSourceKernelObservation adj demod Θ A π (φ p.1) lam (a p.1) p.2 ξ) (c, x) v)) := by
  dsimp only
  let Θ := elapsedPhase Ψ t
  let A := elapsedAmplitude b χout χsource β t
  have hsD (x z ξ : E) (h : A x z ξ ≠ 0) :
      (x, ξ) ∈ tsupport χout ×ˢ (tsupport β ∩ spatialPart ⁻¹' Fη) := by
    constructor
    · by_contra hx
      exact h (elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
        (Or.inl (image_eq_zero_of_notMem_tsupport hx)))
    · constructor
      · by_contra hξ
        exact h (elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
          (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ))))
      · by_contra hη
        exact h (by simp [A, elapsedAmplitude,
          hbF (x 0) (x 0 - t) (spatialPart x) (spatialPart ξ) hη])
  have hsX (x : E) (hx : x ∉ tsupport (if adj then χsource else χout)) (z ξ : E) :
      (if adj then A z x ξ else A x z ξ) = 0 := by
    cases adj
    · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
        (Or.inl (image_eq_zero_of_notMem_tsupport hx))
    · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t z x ξ
        (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hx)))
  have hobsV : tsupport (if adj then χsource else χout) ⊆ V := by
    cases adj <;> assumption
  have hJ := contDiffOn_annularSourceIntegrand_localCarrierPhase adj demod Θ A π φ lam a
    hU ((isClosed_tsupport χout).prod
      ((isClosed_tsupport β).inter (hFη.preimage spatialPartCLM.continuous)))
    (hX.prod (hW.preimage spatialPartCLM.continuous))
    (fun p hp => ⟨hχX hp.1, hβW p.2 hp.2.1 hp.2.2⟩)
    (elapsedPhase_contDiffOn Ψ t hΨ) hsD
    (contDiff_elapsedAnnularAmplitude_entries b χout χsource β hb hχout hχsource hβ t)
    hπ hV (isClosed_tsupport _) hK.isClosed hobsV hKV hφ ha hs hsX
  refine ⟨contDiffOn_annularSourceKernelObservation_of_joint
    adj demod Θ A π φ lam a hU hJ hK hs, ?_, ?_⟩
  · intro c hc x
    exact stronglyMeasurable_annularSourceKernelObservation_frequency_of_joint
      adj demod Θ A π φ lam a hU hJ hK hs hc x
  · intro k v c hc
    refine ⟨?_, ?_, ?_⟩
    · intro x ξ
      refine ⟨?_, iteratedFDeriv_annularSourceKernelObservation_of_joint
        adj demod Θ A π φ lam a hU hJ hK hs k v hc x ξ⟩
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × E) F v).integrable_comp
        (integrable_iteratedFDeriv_annularSourceIntegrand_of_joint
          adj demod Θ A π φ lam a hU hJ hK hs k hc x ξ)
    · intro x
      exact stronglyMeasurable_iteratedFDeriv_annularSourceKernelObservation_frequency_of_joint
        adj demod Θ A π φ lam a hU hJ hK hs k v hc x
    · intro ξ
      exact ⟨tsupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation_subset
          adj demod Ψ b χout χsource β π φ t lam a k v c ξ,
        hasCompactSupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation
          adj demod Ψ b χout χsource β π φ t lam a hout hsource k v c ξ⟩

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
