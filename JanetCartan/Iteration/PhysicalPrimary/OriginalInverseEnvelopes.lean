module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalPrimary.OriginalReservedWords
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterInverseApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalInverseEnvelopesTemplate

/-!
# Ordered Fourier envelopes for the same original full inverse

The parameter derivatives are taken of the complete complex, demodulated
solution. The forcing is the original `χ₂`-localized source; `χ₃` here is the
initialized recut before zero extension and the uncut paired solver. The
coefficient `τ³ * size` bounds a Fourier norm; it is not a pointwise
factorization of the source tensor. Consumer: the physical inverse query and the reduced-to-ambient response
(`app:ch_regular:eq:finite-neumann-identity`, `app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set MeasureTheory
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes
open FixedDomainInverse LocalSobolev ResponseTransfer ResponseTransfer.SourceNegative
open RegularSector.Characteristic.RetardedLocalization RegularSector.Realization SmallSupport
open scoped JanetCartan.RegularSector.Realization
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin q)

/-- Smoothness of the original restricted L² forcing, not just of its pointwise
amplitude. Use the actual compact source support, full phase, neutral bump and
restricted-class identity (`app:ch_response:eq:response-graded-source`). -/
theorem smooth_restricted_original_forcing (W : Set E) {x : E} (χ : ContDiffBump x)
    {V : Set Par} {X : Set E} (hV : IsOpen V) (hX : IsCompact X) (ρ : ℝ)
    {φ : Par → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    {f : Par → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ X)
    (hm : ∀ c, MemLp (modulatedSource χ (φ c) (f c) ρ) 2 volume)
    (source : Par → LocalL2 W F)
    (he : ∀ c ∈ V, source c = restrictL2 W ((hm c).toLp (modulatedSource χ (φ c) (f c) ρ))) :
    ContDiffOn ℝ ∞ source V := by
  have hp : ContDiffOn ℝ ∞
      (Function.uncurry (fun c ↦ modulatedSource χ (φ c) (f c) ρ)) (V ×ˢ univ) :=
    (χ.contDiff.comp_contDiffOn contDiffOn_snd).smul
      (contDiffOn_productParameterSourceFunction_localized hV isOpen_univ hX.isClosed
        (subset_univ _) ρ hφ hf hs)
  have hsupport (c : Par) (hc : c ∈ V) : tsupport (modulatedSource χ (φ c) (f c) ρ) ⊆ X :=
    (tsupport_smul_subset_right _ _).trans ((tsupport_smul_subset_right _ _).trans (hs c hc))
  exact ((restrictL2 W : Lp F 2 (volume : Measure E) →L[ℝ] LocalL2 W F).contDiff.comp_contDiffOn
    (contDiffOn_productParameterSourceClass hX hV hp hsupport hm)).congr he

/-- The original word-history reserve also pays the shifted residual-remainder
order, with the identical source reserve (`app:ch_regular:eq:inverse-remainder`). -/
theorem inverse_reserve_of_word_reserve {d r h : ℕ} (hr : d+1 ≤ r)
    (hword : r + 3*(d+1) + 20 ≤ h) :
    RegularSector.FiniteEvolution.sectorLowOrder d + (d+2) + 2 ≤ h := by
  simp only [RegularSector.FiniteEvolution.sectorLowOrder,
    RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    FourierIntegral.WholeImageGeometry.wholeImagePhaseReserve,
    FourierIntegral.LowBounds.primitiveNormalReserve, FourierIntegral.FullLowBounds.fullLowReserve_eq]
  omega

/-- Reaching a common prehistory threshold changes only the proof of the first
inequality. No history, source, scale or scalar is changed. -/
theorem admit_at_smaller_threshold {d : ℕ} {Payload : Type} {B : ℝ} {k : ℕ} {ν a b : ℝ}
    {i : OriginalHistoryFamily.RawIndex d Payload} {P : Prop} (hab : a ≤ b)
    (hi : OriginalHistoryFamily.Admitted B k ν b i ∧ P) :
    OriginalHistoryFamily.Admitted B k ν a i ∧ P :=
  ⟨⟨hab.trans hi.1.1, hi.1.2⟩, hi.2⟩

/-- The native complete solved observation as one parameter curve. In particular
there is no power of the residual on the right and no supplementary cutoff on
the solver output (`app:ch_response:eq:response-graded-reduced`). -/
def fullObservedCurve (W : Set E) (hW : MeasurableSet W) {x : E} (χ₃ : ContDiffBump x)
    (R : LocalL2 W F →L[ℂ] LocalL2 W F) (hR : ‖R‖ < 1)
    (Op : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E))
    (source : Par → LocalL2 W F) (V : Set Par) (ρ : ℝ) (φ : Par → E → ℝ)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ)) :
    Par → Lp F 2 (volume : Measure E) := fun c ↦
  ResponseTransfer.Complement.carrierMultiplication (-ρ) (ObservedParameterRemainders.totalizedObservationPhase V φ c)
    (ObservedParameterRemainders.continuous_totalizedObservationPhase hφ c)
    (Op (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hR (source c)))))

/-- This is smoothness in the norm of the whole observed `L²` class. It comes
from the solved-source curve and the original compact phase, without any
regularity across the boundary of the retained parameter window
(`app:ch_regular:eq:finite-observation`). -/
theorem contDiffOn_fullObservedCurve (W : Set E) (hW : MeasurableSet W) {x : E}
    (χ₃ : ContDiffBump x) (R : LocalL2 W F →L[ℂ] LocalL2 W F) (hR : ‖R‖ < 1)
    (Op : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E))
    (source : Par → LocalL2 W F) (V : Set Par) (ρ : ℝ) (φ : Par → E → ℝ)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ)) (hV : IsOpen V)
    {X : Set E} (hX : IsCompact X) (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (hsource : ContDiffOn ℝ ∞ source V) :
    ContDiffOn ℝ ∞ (fullObservedCurve W hW χ₃ R hR Op source V ρ φ hφ) V := by
  apply contDiffOn_demodulated_fixed_local_operator hW χ₃ hV hX ρ
    (ObservedParameterRemainders.totalizedObservationPhase V φ)
    (ObservedParameterRemainders.continuous_totalizedObservationPhase hφ)
    (ObservedParameterRemainders.contDiffOn_totalizedObservationPhase hφ) _ Op
    ((complexNeumannInverse R hR).restrictScalars ℝ) source hsource
  intro c hc
  rw [ObservedParameterRemainders.totalizedObservationPhase_of_mem φ hc]
  exact hs c hc

/-- Restrict the already uniform depth and cost to the same admitted tuples
after strengthening their threshold. This proof neither selects a sample member
nor assumes one exists (`app:ch_regular:eq:inverse-remainder`). -/
theorem retain_depth_and_cost {Raw J : Type} (P : Raw → Prop)
    (f : J → Subtype P) (Q : ℕ → ℝ → Subtype P → Prop)
    (h : ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i hi, Q N D ⟨i,hi⟩) :
    ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ j, Q N D (f j) := by
  obtain ⟨N,D,hD,hb⟩ := h
  exact ⟨N,D,hD,fun j ↦ hb (f j).val (f j).property⟩

end JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes

retain_original_restricted_source_regularity
choose_original_inverse_envelope_threshold
retain_original_envelope_points
apply_original_finite_words_and_inverse_remainder

end
