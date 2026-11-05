module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.Stationarity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UpperEndpoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.HalfSpaceEstimate
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Pointwise
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Integrability

/-!
# The bounded elapsed integral of compact-frequency graph kernels

For `app:ch_regular_base:eq:fixed-time-representation`, Fubini identifies the
bounded elapsed integral of the existing graph kernel with the half-space
kernel used in `app:ch_regular:eq:chain-tail`. The original lower buffer and
physical output slab remove the artificial upper endpoint. A smooth time
cutoff equal to one on the bounded interval only supplies a compact extension
to negative elapsed times. Both physical masks and the literal adjoint order
are retained. This is a pointwise kernel result, not an L²-to-Hᵐ estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral
open JanetCartan.Localization FiniteChain.Retarded.HalfSpace

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

local instance : SFinite (KernelEstimates.jointMeasure (d + 1)) := by
  unfold KernelEstimates.jointMeasure
  infer_instance

/-- The full elapsed amplitude in its original physical positions. Literal
adjunction conjugates the entire product, including the Fourier multiplier
and both masks (`app:ch_regular_base:eq:fixed-time-representation`). -/
def orientedElapsedAmplitude (backward : Bool) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (r : ℝ) : FullAmplitude (d + 1) q :=
  if backward then fun u z ξ ↦ (elapsedAmplitude b χout χsource β r u z ξ).conjTranspose
  else elapsedAmplitude b χout χsource β r

/-- The amplitude with the elapsed variable included, before splitting the
boundary collar. The full complementary output factor `1-mo` remains present
(`app:ch_regular:eq:joint-kernel-phase`). -/
def jointElapsedAmplitude (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) : Matrix (Fin q) (Fin q) ℂ :=
  jointAmplitude ρ (orientedElapsedAmplitude backward b χout χsource β p.1)
    mi mo χA χo x y p.2

/-- Both literal orientations vanish above the same actual time slab, even
before integration over bases or covectors (`app:ch_regular:lem:finite-chain`). -/
theorem jointElapsedAmplitude_eq_zero_above_slab
    (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    {a T r : ℝ} (hb : ∀ t s u η, s ≤ a → b t s u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hr : T - a ≤ r)
    (p : JointVariables (Euclidean (d + 1))) :
    jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y (r, p) = 0 := by
  cases backward <;>
    simp [jointElapsedAmplitude, jointAmplitude, orientedElapsedAmplitude,
      elapsedAmplitude_eq_zero_above_slab b χout χsource β hb hout hr]

/-- Fubini for the actual normalized compact-frequency graph kernel. No
measurability or interchange premise is needed: smoothness and the compact
extended amplitude prove absolute integrability. The upper artificial
endpoint is removed using the original lower buffer and output mask, in
both orientations (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem integral_regularizedElapsedKernel_eq_halfSpace
    (backward : Bool) (ρ Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    {a T : ℝ} (hb : ∀ t s u η, s ≤ a → b t s u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ x y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p))
    (hc : HasCompactSupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p)) :
    (∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      mi mo χA χo x y) =
    (KernelEstimates.jointNormalization (d + 1) * ρ ^ (3 * (d + 1))) •
      ∫ p in Ici (0 : ℝ) ×ˢ (univ : Set (JointVariables (Euclidean (d + 1)))),
        phaseOscillation (ρ • jointElapsedPhase backward Ψ x y) p •
          (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p)
        ∂(volume.prod (KernelEstimates.jointMeasure (d + 1))) := by
  let f := fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
    phaseOscillation (ρ • jointElapsedPhase backward Ψ x y) p •
      (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p)
  have hi : Integrable f (volume.prod (KernelEstimates.jointMeasure (d + 1))) :=
    integrable_phaseOscillation_smul isOpen_univ _ _
      (hF.const_smul ρ).contDiffOn ha.contDiffOn (subset_univ _) hc
  have hslice : (∫ p in Ici (0 : ℝ) ×ˢ
      (univ : Set (JointVariables (Euclidean (d + 1)))), f p
      ∂(volume.prod (KernelEstimates.jointMeasure (d + 1)))) =
      ∫ r in Ici (0 : ℝ), ∫ p, f (r, p) ∂KernelEstimates.jointMeasure (d + 1) := by
    rw [← Measure.restrict_prod_eq_prod_univ]
    exact integral_prod _ (by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hi.restrict)
  change _ = _ • ∫ p in Ici (0 : ℝ) ×ˢ
    (univ : Set (JointVariables (Euclidean (d + 1)))), f p
    ∂(volume.prod (KernelEstimates.jointMeasure (d + 1)))
  rw [hslice]
  have hrestrict : (∫ r in Icc 0 Δ, ∫ p, f (r, p)
      ∂KernelEstimates.jointMeasure (d + 1)) =
      ∫ r in Ici (0 : ℝ), ∫ p, f (r, p) ∂KernelEstimates.jointMeasure (d + 1) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
    intro r hr
    have hrΔ : Δ < r := by
      by_contra hn
      exact hr.2 ⟨hr.1, le_of_not_gt hn⟩
    have hz := jointElapsedAmplitude_eq_zero_above_slab backward ρ b χout χsource β
      mi mo χA χo x y hb hout (hslab.trans hrΔ.le)
    simp only [f, hz, smul_zero, integral_zero]
  rw [← hrestrict, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  simp only [KernelEstimates.regularizedJointKernel, f, hθ r hr, one_smul,
    jointElapsedPhase, jointElapsedAmplitude, phaseOscillation, Pi.smul_apply]

/-- The bounded elapsed integral of the existing compact-frequency graph
kernel has arbitrary pointwise decay from the JOINT half-space data. The
frequency loss `s + 3*(d+1)` and grade offset `b₀` are fixed before accuracy
`N`. This is the zeroth-output-derivative kernel obligation for
`app:ch_regular:eq:chain-tail`, not its final Sobolev/operator conclusion.
The preceding identity discharges the elapsed-integral interchange; the two
gradient branches are exactly those of `GradientGaps.lean`. -/
theorem norm_integral_regularizedElapsedKernel_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (s Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    {a T : ℝ} (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hout : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    {UT UI K : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hUT : IsOpen UT) (hUI : IsOpen UI) (hK : IsCompact K)
    (eT : ι → JointVariables (Euclidean (d + 1)))
    (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ x y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p))
    (hχ : ContDiff ℝ ∞ χ)
    (hsK : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p) ⊆ K)
    (hχT : K ∩ tsupport χ ⊆ UT)
    (hχI : (K ∩ tsupport (1 - χ)) ∩ {p | 0 < p.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ p, |p.1| < ε → χ p = 1)
    {δT δI GT GI : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hgapT : ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
      δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p)
    (hupperT : ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
      ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) (r, p)‖ ≤ GT)
    (hgapI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward Ψ x y) p)
    (hupperI : ∀ p ∈ UI ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) p‖ ≤ GI)
    {P H A : ℕ → ℝ} (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (b₀ N : ℕ)
    (hp : ∀ p ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward Ψ x y)) p‖ ≤ P j * L ^ j)
    (hχ_bound : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j χ p‖ ≤ H j)
    (ha_bound : ∀ p ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
        θ w.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y w) p‖ ≤
        ρ ^ s * A j * L ^ (j + b₀)) :
    ‖∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      mi mo χA χo x y‖ ≤
      (KernelEstimates.jointNormalization (d + 1) *
        collarDecayConstant (KernelEstimates.jointMeasure (d + 1)) K eT eI
          δT δI GT GI P H A N) * ρ ^ (s + (3 * (d + 1) : ℕ)) * L ^ b₀ * (L / ρ) ^ N := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  rw [integral_regularizedElapsedKernel_eq_halfSpace backward ρ Δ Ψ b χout χsource β
    mi mo χA χo x y θ hθ hb hout hslab hF ha
    (hK.of_isClosed_subset (isClosed_tsupport _) hsK), norm_smul,
    Real.norm_of_nonneg (mul_nonneg (KernelEstimates.jointNormalization_nonneg _)
      (pow_nonneg hρ0.le _))]
  have h := norm_halfSpace_vector_integral_le (μ := KernelEstimates.jointMeasure (d + 1))
    hUT hUI hK eT eI
    (jointElapsedPhase backward Ψ x y)
    (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p) χ
    hF ha hχ hsK hχT hχI hε hχ_one hδT hδI hL hρ (Real.rpow_pos_of_pos hρ0 s)
    hgapT hupperT hgapI hupperI hH hA b₀ N hp hχ_bound ha_bound
  apply (mul_le_mul_of_nonneg_left h
    (mul_nonneg (KernelEstimates.jointNormalization_nonneg _) (pow_nonneg hρ0.le _))).trans_eq
  rw [Real.rpow_add hρ0, Real.rpow_natCast]
  ring

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
