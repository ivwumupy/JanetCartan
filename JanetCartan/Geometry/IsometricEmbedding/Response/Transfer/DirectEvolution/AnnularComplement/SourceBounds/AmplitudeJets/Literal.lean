module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Basic

/-!
# Normalized external jets of the literal annular source amplitudes

The boolean `adjoint` selects the orientation and `demodulated` selects whether
the output carrier is included in the phase. Both choices precede external
differentiation. All four functions are identified with the published literal
source kernels of `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open FourierIntegral JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
variable {C : Type} {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The entire phase at fixed physical frequency. The output demodulator is
inside this function and is therefore differentiated with `p = (c,x)`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def annularExternalPhase (adjoint demodulated : Bool) (Θ : E → E → ℝ)
    (φ : C → E → ℝ) (lam : ℝ) (ξ : E) (p : C × E) (z : E) : ℝ :=
  (if adjoint then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ z
    else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ z) -
  if demodulated then lam * φ p.1 p.2 else 0

/-- The actual published vector amplitude. The full amplitude, selector,
physical frequency and carrier scale remain fixed in external derivatives.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def annularExternalAmplitude (adjoint : Bool) (A : FullAmplitude n r)
    (π : E → ℂ) (lam : ℝ) (a : C → E → F) (ξ : E) (p : C × E) (z : E) : F :=
  if adjoint then adjointAnnularSourceAmplitude A π lam (a p.1) p.2 ξ z
    else forwardAnnularSourceAmplitude A π lam (a p.1) p.2 ξ z

variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The normalized actual external jet used as the amplitude in
`norm_annularSourceIntegral_le`. No polynomial profile is part of this
definition (`app:ch_response:lem:energy-carrier-jets`). -/
def annularExternalJet (adjoint demodulated : Bool) (Θ : E → E → ℝ)
    (A : FullAmplitude n r) (π : E → ℂ) (φ : C → E → ℝ)
    (lam : ℝ) (a : C → E → F) (ξ : E)
    (j : ℕ) (v : Fin j → C × E) (p : C × E) : E → F :=
  normalizedExternalJet (annularExternalPhase adjoint demodulated Θ φ lam ξ)
    (annularExternalAmplitude adjoint A π lam a ξ) j v p

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- Exact output demodulator in the phase, before any external derivative.
This applies at every physical frequency, including zero and the unbounded
complementary tail (`app:ch_response:lem:energy-carrier-jets`). -/
theorem phaseOscillation_annularExternalPhase_demodulated
    (adjoint : Bool) (Θ : E → E → ℝ) (φ : C → E → ℝ)
    (lam : ℝ) (ξ : E) (p : C × E) (z : E) :
    phaseOscillation (annularExternalPhase adjoint true Θ φ lam ξ p) z =
      carrier (-lam) (φ p.1) p.2 *
        phaseOscillation (annularExternalPhase adjoint false Θ φ lam ξ p) z := by
  cases adjoint <;>
    simp only [annularExternalPhase, Bool.false_eq_true, ite_false, ite_true, sub_zero,
      phaseOscillation, carrier, ← Complex.exp_add] <;>
    congr 1 <;> push_cast <;> ring

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- The four source integrals coincide with the published physical and
demodulated kernels. No integrability assumption or altered kernel is used.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem integral_annularExternalPhase_amplitude
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : C → E → ℝ) (lam : ℝ) (a : C → E → F)
    (ξ : E) (p : C × E) :
    ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
      phaseOscillation (annularExternalPhase adjoint demodulated Θ φ lam ξ p) z •
        annularExternalAmplitude adjoint A π lam a ξ p z =
    if demodulated then
      if adjoint then demodulatedAdjointAnnularSourceKernel Θ A π (φ p.1) lam (a p.1) p.2 ξ
      else demodulatedForwardAnnularSourceKernel Θ A π (φ p.1) lam (a p.1) p.2 ξ
    else
      if adjoint then adjointAnnularSourceKernel Θ A π (φ p.1) lam (a p.1) p.2 ξ
      else forwardAnnularSourceKernel Θ A π (φ p.1) lam (a p.1) p.2 ξ := by
  cases demodulated with
  | false =>
    cases adjoint <;>
      simp [annularExternalPhase, annularExternalAmplitude, forwardAnnularSourceKernel,
        adjointAnnularSourceKernel, phaseOscillation]
  | true =>
    simp_rw [phaseOscillation_annularExternalPhase_demodulated, mul_smul, integral_smul]
    cases adjoint <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, demodulatedForwardAnnularSourceKernel,
        demodulatedAdjointAnnularSourceKernel, forwardAnnularSourceKernel,
        adjointAnnularSourceKernel, annularExternalAmplitude]
      <;> simp only [phaseOscillation, annularExternalPhase, Bool.false_eq_true, ite_false, ite_true, sub_zero]
      <;> exact smul_comm _ _ _

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- The envelope is the common source support for either orientation.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem tsupport_annularExternalAmplitude_subset (adjoint : Bool)
    (A : FullAmplitude n r) (π : E → ℂ) (lam : ℝ) (a : C → E → F)
    (ξ : E) (p : C × E) :
    tsupport (annularExternalAmplitude adjoint A π lam a ξ p) ⊆ tsupport (a p.1) := by
  cases adjoint
  · exact tsupport_forwardAnnularSourceAmplitude_subset A π lam (a p.1) p.2 ξ
  · exact tsupport_adjointAnnularSourceAmplitude_subset A π lam (a p.1) p.2 ξ

/-- All actual external jets retain the fixed envelope support in both
orientations and observations. This uses the open carrier neighborhood, not
merely the compact parameter box (`app:ch_response:lem:energy-carrier-jets`). -/
theorem tsupport_annularExternalJet_subset
    {V : Set C} {S : Set E} (hV : IsOpen V) (hS : IsClosed S)
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : C → E → ℝ) (lam : ℝ) (a : C → E → F)
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S) (ξ : E)
    (j : ℕ) (v : Fin j → C × E) (p : C × E) (hp : p.1 ∈ V) :
    tsupport (annularExternalJet adjoint demodulated Θ A π φ lam a ξ j v p) ⊆ S := by
  exact tsupport_normalizedExternalJet_subset (hV.prod (isOpen_univ : IsOpen (univ : Set E))) hS
    (annularExternalPhase adjoint demodulated Θ φ lam ξ)
    (annularExternalAmplitude adjoint A π lam a ξ)
    (fun q hq => (tsupport_annularExternalAmplitude_subset adjoint A π lam a ξ q).trans
      (hs q.1 hq.1)) j v ⟨hp, mem_univ _⟩

/-- The same support also controls every source derivative of the actual jet,
so the source cutoff and volume need not depend on either derivative order.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem tsupport_sourceDerivative_annularExternalJet_subset
    {V : Set C} {S : Set E} (hV : IsOpen V) (hS : IsClosed S)
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : C → E → ℝ) (lam : ℝ) (a : C → E → F)
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S) (ξ : E)
    (j : ℕ) (v : Fin j → C × E) (p : C × E) (hp : p.1 ∈ V) (k : ℕ) :
    tsupport (iteratedFDeriv ℝ k
      (annularExternalJet adjoint demodulated Θ A π φ lam a ξ j v p)) ⊆ S :=
  (tsupport_iteratedFDeriv_subset k).trans
    (tsupport_annularExternalJet_subset hV hS adjoint demodulated Θ A π φ lam a hs ξ j v p hp)

/-- An exact selector plateau kills every normalized external jet. The
selector and `λ` remain fixed under these derivatives.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularExternalJet_eq_zero_of_selector_eq_one
    (adjoint demodulated : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : C → E → ℝ) (lam : ℝ) (a : C → E → F)
    (ξ : E) (hπ : π (lam⁻¹ • ξ) = 1)
    (j : ℕ) (v : Fin j → C × E) (p : C × E) :
    annularExternalJet adjoint demodulated Θ A π φ lam a ξ j v p = 0 := by
  funext z
  apply normalizedExternalJet_eq_zero_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  cases adjoint <;>
    simp [annularExternalAmplitude, forwardAnnularSourceAmplitude, adjointAnnularSourceAmplitude,
      annularComplementAmplitude, frequencyCutFullAmplitude, hπ]

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- The literal forward amplitude after elapsed substitution displays both
physical masks, the original beta, and the unchanged selector. This identity
is the input to the primitive amplitude budget producer.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularExternalAmplitude_forward_elapsed {d : ℕ}
    (b : TwoTimeAmplitude d r) (χout χsource β π : Euclidean (d + 1) → ℂ)
    (t lam : ℝ) (a : C → Euclidean (d + 1) → F)
    (ξ : Euclidean (d + 1)) (p : C × Euclidean (d + 1)) (z : Euclidean (d + 1)) :
    annularExternalAmplitude false (elapsedAmplitude b χout χsource β t) π lam a ξ p z =
      WithLp.toLp 2 ((((1 - π (lam⁻¹ • ξ)) * (χout p.2 * χsource z * β ξ)) •
        b (p.2 0) (p.2 0 - t) (spatialPart p.2) (spatialPart ξ)).mulVec (a p.1 z).ofLp) := by
  simp only [annularExternalAmplitude, Bool.false_eq_true, ite_false,
    forwardAnnularSourceAmplitude, annularComplementAmplitude, frequencyCutFullAmplitude,
    elapsedAmplitude, smul_smul]

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- The literal adjoint elapsed amplitude includes conjugation of both masks
and beta, and the reversed physical positions.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularExternalAmplitude_adjoint_elapsed {d : ℕ}
    (b : TwoTimeAmplitude d r) (χout χsource β π : Euclidean (d + 1) → ℂ)
    (t lam : ℝ) (a : C → Euclidean (d + 1) → F)
    (ξ : Euclidean (d + 1)) (p : C × Euclidean (d + 1)) (z : Euclidean (d + 1)) :
    annularExternalAmplitude true (elapsedAmplitude b χout χsource β t) π lam a ξ p z =
      WithLp.toLp 2 ((star ((1 - π (lam⁻¹ • ξ)) * (χout z * χsource p.2 * β ξ)) •
        (b (z 0) (z 0 - t) (spatialPart z) (spatialPart ξ)).conjTranspose).mulVec
          (a p.1 z).ofLp) := by
  simp only [annularExternalAmplitude, ite_true, adjointAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude,
    smul_smul, Matrix.conjTranspose_smul]

/-- The original beta kills every actual external jet where it vanishes.
No phase regularity off beta's support is needed for this zero branch of
`app:ch_response:lem:energy-carrier-jets`. -/
theorem annularExternalJet_elapsed_eq_zero_of_beta_eq_zero {d : ℕ}
    (adjoint demodulated : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : C → Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : C → Euclidean (d + 1) → F) (ξ : Euclidean (d + 1)) (hβ : β ξ = 0)
    (j : ℕ) (v : Fin j → C × Euclidean (d + 1)) (p : C × Euclidean (d + 1)) :
    annularExternalJet adjoint demodulated (elapsedPhase Ψ t)
      (elapsedAmplitude b χout χsource β t) π φ lam a ξ j v p = 0 := by
  funext z
  apply normalizedExternalJet_eq_zero_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  cases adjoint <;>
    simp [annularExternalAmplitude, forwardAnnularSourceAmplitude, adjointAnnularSourceAmplitude,
      annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude, hβ]

omit [NormedAddCommGroup C] [NormedSpace ℝ C] in
/-- Removing the output phase changes no positive SOURCE derivative. This
identity does not commute demodulation with external differentiation; its
external derivatives are still retained by `annularExternalJet`. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem iteratedFDeriv_annularExternalPhase_demodulated
    (adjoint : Bool) (Θ : E → E → ℝ) (φ : C → E → ℝ)
    (lam : ℝ) (ξ : E) (p : C × E) (z : E)
    (hψ : ContDiffAt ℝ ∞ (annularExternalPhase adjoint false Θ φ lam ξ p) z)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (annularExternalPhase adjoint true Θ φ lam ξ p) z =
      iteratedFDeriv ℝ k (annularExternalPhase adjoint false Θ φ lam ξ p) z := by
  have he : annularExternalPhase adjoint true Θ φ lam ξ p =
      annularExternalPhase adjoint false Θ φ lam ξ p - fun _ => lam * φ p.1 p.2 := by
    funext y
    simp [annularExternalPhase]
  rw [he, iteratedFDeriv_sub_apply (hψ.of_le (by simp)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, sub_zero]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
