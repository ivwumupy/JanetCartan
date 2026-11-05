module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.BasePhase
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.BaseAmplitude
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks

/-!
# Noncomparable kernels of the literal complete residual

The per-time input of
`exists_uniform_elapsedGraphIntegral_fourier_bound_of_joint_grades` is proved
from two-time phase and amplitude grades. The amplitude is exactly one of
`directRetardedAmplitudes`, in either literal orientation. A supported smooth
auxiliary amplitude is removed using the masked identity produced in
`ResidualCoordinates.Assembly`; the original conic amplitude is not assumed
smooth at frequency zero. Neither a shell bound nor a localization estimate
is an input. Source: `app:ch_regular:eq:chain-tail` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open FourierIntegral CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization EvolutionLocalization.PrimitiveGrades
open EvolutionIntegratedLocalization
open FiniteChain.Graph FiniteChain.Graph.KernelLimits
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The physical noncomparable kernel estimate for both direct residual
amplitudes, including all negative orders, bounded graph frequencies and the
zeroth output ball. Constants and coefficient losses precede the coefficient
family, frequency, elapsed time and accuracy. The literal adjoint transposes
both physical masks in place.

The auxiliary masked identity is produced by
`ResidualCoordinates.Assembly.completeResidual_of_selected_physical_chart`
using `elapsedDirectAmplitude_eq_of_auxiliary_masks` and its coefficient
variant. `EvolutionLocalization.PrimitiveGrades` produces both physical-base
grades below from the original two-time grades; the conic graph producer
constructs all differentiated-kernel estimates. Phase carrier and frequency
comparison inputs come from `EvolutionLocalization.SupportedCarriers` and
`ChartControls.Frequency`. No arbitrary-energy graph separation is used here.
Consumer: the `hper` and order-zero `hperGlobal` inputs of the elapsed-integral
localization theorem (`app:ch_regular:lem:finite-chain`). -/
theorem exists_directResidual_noncomparable_kernel_bounds
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    {c C Ci a b₀ : ℝ} (hc : 0 < c) (hCi : 0 ≤ Ci) (ha : 0 < a)
    (χout χsource β : E → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβsmooth : ContDiff ℝ ∞ β)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {Bβ Cβ : ℝ} (hBβ : 0 ≤ Bβ) (hCβ : 0 ≤ Cβ)
    (hβ : ∀ ξ, ‖β ξ‖ ≤ Bβ)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ Cβ * ‖spatialPart ξ‖)
    (P B O : ℕ → ℝ) (hP : ∀ k, 0 ≤ P k) (hB : ∀ k, 0 ≤ B k)
    (hO : ∀ k, 0 ≤ O k) (s Δ : ℝ) (offset bo m : ℕ) :
    ∃ (bLoss : ℕ) (D : ℕ → ℝ), (∀ N, 0 ≤ D N) ∧
    ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
    ∀ (A : E → Fin (d + 1) → Mat) (B₀ : E → Mat)
      (W₀ W₁ : TwoTimeAmplitude d q) (branch : Bool)
      (Ψ : TwoTimePhase d) (aux : TwoTimeAmplitude d q),
    let actual := directRetardedAmplitudes A B₀ W₀ W₁ branch
    ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude aux) →
    (∀ r ∈ Icc 0 Δ, elapsedAmplitude aux χout χsource β r =
      elapsedAmplitude actual χout χsource β r) →
    ∀ (Up Ua : Set (SymbolBudgets.TwoTimePoint d)),
    IsOpen Up → ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) Up →
    (∀ η v, (v, η) ∈ Up → ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1)
        (fun w : ℝ × ℝ × Euclidean d ↦ Ψ w.1 w.2.1 w.2.2 η) v‖ ≤
          ‖η‖ * P k * L ^ k) →
    (∀ p ∈ Ua, ∀ k, ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude aux) p‖ ≤
      (1 + ‖p.2‖) ^ s * B k * L ^ (k + offset)) →
    (∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport χout ×ˢ tsupport χsource,
        β (ρ • ξ) ≠ 0 → SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ Ua) →
    ∀ (mi mo : LocalizerSymbol (d + 1)),
    ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo → HasCompactSupport mi →
    (∀ y, tsupport (fun η ↦ mi (y, η)) ⊆ frequencyAnnulus a b₀) →
    (∀ y η, ‖mi (y, η)‖ ≤ Ci) →
    (∀ x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤ O k * L ^ (k + bo)) →
    ∀ (r : ℝ), r ∈ Icc 0 Δ → ∀ (backward low : Bool) (j k : ℕ)
      (V Kphase : Set (E × E)) (g : E → E → E),
    IsOpen V → IsCompact Kphase → Kphase ⊆ V →
    ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) V →
    (∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : E × E ↦
        elapsedAmplitude actual χout χsource β r z.1 z.2 (ρ • ξ)),
      (z.1, ρ • ξ) ∈ Kphase ∧ SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ Up) →
    (∀ u ξ, (u, ξ) ∈ V →
      fderiv ℝ (fun t ↦ elapsedPhase Ψ r t ξ) u = innerSL ℝ (g u ξ)) →
    (∀ u ξ, (u, ξ) ∈ V → c * ‖ξ‖ ≤ ‖g u ξ‖ ∧ ‖g u ξ‖ ≤ C * ‖ξ‖) →
    SeparatedRanges c C (a * ρ) (b₀ * ρ)
      (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
    ∀ (N : ℕ) (x y : E) (v : Fin m → E), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t ↦ regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward actual χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D N * ρ ^ (d + 1) * L ^ bLoss *
          (L / ρ) ^ N * pairWeight low (d + 1) j k := by
  classical
  let Kb := tsupport χout ×ˢ tsupport χsource
  have hKb : IsCompact Kb := hout.prod hsource
  obtain ⟨Ba, hBa, hgrade⟩ := exists_physicalElapsedAmplitude_grades (q := q)
    hKb χout χsource β hχout hχsource hBβ hCβ hβ hcone B hB offset s Δ
  have hpair (backward : Bool) := exists_conicPhysicalPair_bound_of_primitive_grades
    (r := q) (C := C) (b := b₀) eu ez backward hc hCi ha hKb
    P Ba O hP hBa hO s 0 0 0 bo offset m
  choose threshold D hD hpair using hpair
  let loss backward := 0 + (m + bo) + offset + threshold backward + 2
  refine ⟨max (loss false) (loss true), fun N ↦ D false N + D true N,
    fun N ↦ add_nonneg (hD false N) (hD true N), ?_⟩
  intro ρ L hρ hL A B₀ W₀ W₁ branch Ψ aux actual haux heq
    Up Ua hUp hΨ hp haGrade haMap mi mo hi ho his hiAnn hiBound hoBound
    r hr backward low j k V Kphase g hV hKphase hKV hS hcarrier hg hcomp hsep N x y v hv
  have hAmp : ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      elapsedAmplitude actual χout χsource β r p.1.1 p.1.2 p.2) := by
    rw [← heq r hr]
    exact SymbolBudgets.contDiff_uncurry_elapsedAmplitude aux χout χsource β haux hχout hχsource hβsmooth r
  have hOrient : ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward actual χout χsource β r p.1.1 p.1.2 p.2) := by
    cases backward
    · exact hAmp
    · exact (Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hAmp
  have hzero : ∀ u z ξ, (u, z) ∉ Kb →
      orientedElapsedAmplitude backward actual χout χsource β r u z ξ = 0 := by
    intro u z ξ hz
    have he := elapsedAmplitude_eq_zero_off_physical_carrier actual χout χsource β r u z ξ hz
    cases backward <;> simp [orientedElapsedAmplitude, he]
  have hsupport (ξ : E) :
      tsupport (fun z : E × E ↦
        orientedElapsedAmplitude backward actual χout χsource β r z.1 z.2 (ρ • ξ)) =
      tsupport (fun z : E × E ↦ elapsedAmplitude actual χout χsource β r z.1 z.2 (ρ • ξ)) := by
    cases backward <;> simp [orientedElapsedAmplitude, tsupport, Function.support]
  let carriers : RegularizedCarriers
      (orientedElapsedAmplitude backward actual χout χsource β r) mi
      (graphBranchCutoff low j) (outputCutoff k) := {
    amplitudeBase := Kb
    inputBase := Prod.fst '' tsupport mi
    inputFrequency := Prod.snd '' tsupport mi
    compact_amplitudeBase := hKb
    compact_inputBase := his.image continuous_fst
    compact_inputFrequency := his.image continuous_snd
    compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j
    compact_outputCutoff := hasCompactSupport_outputCutoff k
    amplitude_zero := hzero
    input_zero := fun y η h ↦ image_eq_zero_of_notMem_tsupport
      (fun hh ↦ h ⟨⟨(y, η), hh, rfl⟩, ⟨(y, η), hh, rfl⟩⟩) }
  have hestimate :
      ‖iteratedFDeriv ℝ m (fun t ↦ regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward actual χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D backward N * ρ ^ (d + 1) * L ^ (loss backward) *
          (L / ρ) ^ N * pairWeight low (d + 1) j k := by
    apply hpair backward ρ L hρ hL (elapsedPhase Ψ r)
      (orientedElapsedAmplitude backward actual χout χsource β r)
      mi mo low j k x y V Kphase g hV hKphase hKV hS
      (fun ξ hξ z hz ↦ (hcarrier ξ hξ z (by rwa [hsupport] at hz)).1)
      hOrient hi ho hzero (hiAnn y) hsep hg hcomp
      ?_ ?_ ?_ ?_ carriers N v hv
    · intro ξ hξ z hz l hl
      exact elapsedPhase_physicalBase_grade P hP (zero_le_one.trans hL) hUp Ψ hΨ hp
        r (ρ • ξ) z (hcarrier ξ hξ z (by rwa [hsupport] at hz)).2 l hl
    · intro ξ hξ z hz l
      have hb := hgrade L ρ hL hρ aux haux Ua haGrade r hr (haMap r hr) low j ξ hξ z hz l
      rw [heq r hr] at hb
      cases backward
      · exact hb
      · simpa only [orientedElapsedAmplitude, ↓reduceIte,
          norm_iteratedFDeriv_transport_conjTranspose] using hb
    · intro η _
      simpa only [Real.rpow_zero, one_mul, pow_zero, mul_one] using hiBound y η
    · intro ζ _ l
      simpa only [Real.rpow_zero, one_mul] using hoBound x ζ l
  have hcoeff : D backward N ≤ D false N + D true N := by
    cases backward
    · exact le_add_of_nonneg_right (hD true N)
    · exact le_add_of_nonneg_left (hD false N)
  have hloss : loss backward ≤ max (loss false) (loss true) := by
    cases backward
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hweight := pairWeight_nonneg low (d + 1) j k
  apply hestimate.trans
  apply mul_le_mul_of_nonneg_right ?_ hweight
  apply mul_le_mul_of_nonneg_right ?_ (pow_nonneg (div_nonneg hL0 hρ0) N)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hρ0 (d + 1)))
    (pow_le_pow_right₀ hL hloss) (pow_nonneg hL0 _)
    (mul_nonneg (add_nonneg (hD false N) (hD true N)) (pow_nonneg hρ0 (d + 1)))


end JanetCartan.ArbitraryAccuracy.ResidualLocalization
