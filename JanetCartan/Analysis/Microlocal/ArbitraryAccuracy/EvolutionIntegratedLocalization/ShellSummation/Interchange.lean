module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputDifferentiation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellKernels

/-!
# Elapsed integration of the literal shell jets

The noncomparable estimates in `app:ch_regular:eq:chain-tail` hold at each
elapsed time. Common compact primitive support proves the differentiation
interchange needed to integrate them. Neither an integrated estimate nor a
kernel differentiability hypothesis is assumed. The two orientations, both
physical localizer rescalings, source shoulders and the identity in `1-mo`
are unchanged.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

section Normalized

variable (backward : Bool) (ρ Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
  (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
  (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (y : Euclidean (d + 1))

private theorem cutElapsedIntegrand_zero_of_notMem
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K)
    (x : Euclidean (d + 1)) (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hp : p ∉ K) :
    cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y x p = 0 := by
  have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hs h))
  have he := jointIntegrand_add_output backward ρ (elapsedPhase Ψ p.1)
    (orientedElapsedAmplitude backward b χout χsource β p.1) mi mo χA χo 0 y x p.2
  simp only [zero_add] at he
  unfold cutElapsedIntegrand
  rw [he, smul_comm (θ p.1), smul_comm (θ p.1)]
  change _ • (_ • (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β
    mi (fun _ ↦ 0) χA χo 0 y p)) = 0
  rw [hz, smul_zero, smul_zero]

/-- Integrating the jointly smooth compact primitive integrand gives joint
smoothness in output position and elapsed time. The premise `hF` and the
masked amplitude premise are exactly those of
`contDiff_cutElapsedIntegrand_joint`; no output-kernel regularity is an input.
Consumer: elapsed shell differentiation for `app:ch_regular:eq:chain-tail`. -/
theorem contDiff_cutNormalizedElapsedKernel
    (ho : ContDiff ℝ ∞ mo)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ 0 y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K) :
    ContDiff ℝ ∞ (fun z : Euclidean (d + 1) × ℝ ↦ θ z.2 •
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ z.2)
        (orientedElapsedAmplitude backward b χout χsource β z.2) mi mo χA χo z.1 y) := by
  let f := fun z : (Euclidean (d + 1) × ℝ) × JointVariables (Euclidean (d + 1)) ↦
    cutElapsedIntegrand backward ρ Ψ b χout χsource β mi mo χA χo θ y z.1.1 (z.1.2, z.2)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_cutElapsedIntegrand_joint backward ρ Ψ b χout χsource β mi mo χA χo θ y
      ho hF ha).comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hz : ∀ z p, p ∉ Prod.snd '' K → f (z, p) = 0 := by
    intro z p hp
    exact cutElapsedIntegrand_zero_of_notMem backward ρ Ψ b χout χsource β mi mo
      χA χo θ y hs z.1 (z.2, p) (fun h ↦ hp ⟨(z.2, p), h, rfl⟩)
  have hi := contDiff_integral_commonCarrier (μ := jointMeasure (d + 1)) hf
    (hK.image continuous_snd) hz
  have he : (fun z : Euclidean (d + 1) × ℝ ↦ θ z.2 •
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ z.2)
        (orientedElapsedAmplitude backward b χout χsource β z.2) mi mo χA χo z.1 y) =
      fun z ↦ (jointNormalization (d + 1) * ρ ^ (3 * (d + 1))) •
        ∫ p, f (z, p) ∂jointMeasure (d + 1) := by
    funext z
    simp only [f, cutElapsedIntegrand, KernelEstimates.regularizedJointKernel,
      integral_smul, smul_comm (θ z.2)]
    rfl
  rw [he]
  exact hi.const_smul _

/-- All evaluated output derivatives commute with the bounded elapsed
integral of the normalized kernels. Domination and measurability follow
from the preceding joint smoothness and the compact interval, including its
zero endpoint (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_integral_normalizedElapsedKernel_eq_integral
    (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1) (ho : ContDiff ℝ ∞ mo)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ 0 y))
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p) ⊆ K)
    (m : ℕ) (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1)) :
    iteratedFDeriv ℝ m (fun t ↦ ∫ r in Icc 0 Δ,
      KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) x v =
      ∫ r in Icc 0 Δ, iteratedFDeriv ℝ m
        (fun t ↦ KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
          (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) x v := by
  let f := fun z : Euclidean (d + 1) × ℝ ↦ θ z.2 •
    KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ z.2)
      (orientedElapsedAmplitude backward b χout χsource β z.2) mi mo χA χo z.1 y
  have hf : ContDiff ℝ ∞ f := contDiff_cutNormalizedElapsedKernel
    backward ρ Ψ b χout χsource β mi mo χA χo θ y ho hF ha hK hs
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) : (fun t ↦ f (t, r)) =
      fun t ↦ KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y := by
    funext t
    simp only [f, hθ r hr, one_smul]
  have hei : (fun t ↦ ∫ r in Icc 0 Δ, f (t, r)) =
      fun t ↦ ∫ r in Icc 0 Δ,
        KernelEstimates.regularizedJointKernel backward ρ (elapsedPhase Ψ r)
          (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y := by
    funext t
    exact setIntegral_congr_fun measurableSet_Icc (fun r hr ↦ congrFun (he r hr) t)
  rw [← hei, iteratedFDeriv_compactCarrierIntegral hf isCompact_Icc,
    ContinuousMultilinearMap.integral_apply (integrableOn_outputJet hf isCompact_Icc m x)]
  exact setIntegral_congr_fun measurableSet_Icc (fun r hr ↦ by rw [he r hr])

end Normalized

section Physical

variable (backward : Bool) {ρ : ℝ} (hρ : 0 < ρ) (Δ : ℝ)
  (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
  (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
  (χA χo : Euclidean (d + 1) → ℝ) (θ : ℝ → ℂ) (y : Euclidean (d + 1))
  (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
  (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
  (hb : ∀ r ∈ Icc 0 Δ, Continuous
    (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
  (hi : Continuous mi) (ho : ContDiff ℝ ∞ mo) (hg : Continuous χA) (hc : Continuous χo)
  (c : ∀ r ∈ Icc 0 Δ,
    KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      mi χA χo)
  (hF : ContDiff ℝ ∞
    (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) 0 y))
  (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
    θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
      χA χo 0 y p))
  {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
  (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
    θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
      χA χo 0 y p) ⊆ K)

set_option quotPrecheck false

local notation "Kphys" => fun r t ↦ KernelLimits.regularizedJointKernel backward
  (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
  (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo t y

local notation "Knorm" => fun r t ↦ KernelEstimates.regularizedJointKernel backward ρ
  (elapsedPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) r)
  (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y

include hρ hΨ hb hi ho hg hc c in
private theorem physicalElapsedKernel_eq_normalized_section (r : ℝ) (hr : r ∈ Icc 0 Δ) :
    Kphys r = Knorm r := by
  funext t
  apply PhysicalShells.regularizedJointKernel_eq_normalized backward _ _ _ mi mo χA χo t y
    hρ ?_ (hΨ r hr) (hb r hr) hi ho.continuous hg hc (c r hr)
  intro u ξ
  rw [← SymbolBudgets.normalizedPhase_elapsedPhase hρ.ne' Ψ r]
  simp only [FourierIntegral.WholeImageGeometry.normalizedPhase,
    ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

include hρ hθ hΨ hb hi ho hg hc c hF ha hK hs in
/-- The literal physical elapsed shell kernel is smooth in its output, and
each physical time section is integrable on the bounded elapsed interval.
Both facts are deduced from compact primitive regularity, for use in the
exact high/low splitting of `app:ch_regular:eq:chain-tail`. -/
theorem elapsedPhysicalShellKernel_regularity :
    ContDiff ℝ ∞ (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo χA χo t y) ∧
    ∀ x, IntegrableOn (fun r ↦ Kphys r x) (Icc 0 Δ) := by
  let f := fun z : Euclidean (d + 1) × ℝ ↦ θ z.2 • Knorm z.2 z.1
  have hf : ContDiff ℝ ∞ f := contDiff_cutNormalizedElapsedKernel backward ρ
    (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) b χout χsource β mi mo χA χo θ y
    ho hF ha hK hs
  have he (r : ℝ) (hr : r ∈ Icc 0 Δ) (t : Euclidean (d + 1)) : f (t, r) = Kphys r t := by
    dsimp [f]
    rw [hθ r hr, one_smul]
    exact (congrFun (physicalElapsedKernel_eq_normalized_section backward hρ Δ Ψ b
      χout χsource β mi mo χA χo y hΨ hb hi ho hg hc c r hr) t).symm
  constructor
  · have hei : (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
        χout χsource β mi mo χA χo t y) = fun t ↦ ∫ r in Icc 0 Δ, f (t, r) := by
      funext t
      exact setIntegral_congr_fun measurableSet_Icc (fun r hr ↦ (he r hr t).symm)
    rw [hei, ← contDiffOn_univ]
    exact JanetCartan.contDiffOn_compactParameterIntegral (U := univ) (V := univ)
      isOpen_univ isOpen_univ isCompact_Icc (subset_univ _) hf.contDiffOn
  · intro x
    apply ((hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      |>.integrableOn_compact isCompact_Icc).congr_fun (fun r hr ↦ he r hr x) measurableSet_Icc

include hρ hθ hΨ hb hi ho hg hc c hF ha hK hs in
/-- All evaluated output derivatives of the literal physical shell kernel
are the bounded elapsed integral of its physical per-time derivatives.
`PhysicalKernels` supplies the exact normalization and `OutputDifferentiation`
supplies primitive joint smoothness; the compact carrier discharges the
interchange. This is the bridge from the physical noncomparable per-time
estimate to `app:ch_regular:eq:chain-tail`, for either orientation. -/
theorem iteratedFDeriv_elapsedPhysicalShellKernel_eq_integral
    (m : ℕ) (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1)) :
    iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo χA χo t y) x v =
      ∫ r in Icc 0 Δ, iteratedFDeriv ℝ m (Kphys r) x v := by
  unfold elapsedPhysicalShellKernel
  rw [iteratedFDeriv_integral_physicalElapsedKernel_eq_normalized backward hρ Δ Ψ b
    χout χsource β mi mo χA χo x y hΨ hb hi ho.continuous hg hc c m v,
    iteratedFDeriv_integral_normalizedElapsedKernel_eq_integral backward ρ Δ
      (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) b χout χsource β mi mo χA χo θ y
      hθ ho hF ha hK hs m x v]
  exact setIntegral_congr_fun measurableSet_Icc (fun r hr ↦ by
    rw [physicalElapsedKernel_eq_normalized_section backward hρ Δ Ψ b
      χout χsource β mi mo χA χo y hΨ hb hi ho hg hc c r hr])

include hρ hθ hΨ hb hi ho hg hc c hF ha hK hs in
/-- A uniform physical per-time output-jet bound integrates with only the
length of the fixed elapsed interval. The per-time input is supplied by
`PhysicalShells.Noncomparable.exists_conicPhysicalPair_bound_of_primitive_grades`,
whose proof uses `ConicExtension.Summation` and `PhysicalTransfer`.
No integrated tail bound is assumed (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_elapsedPhysicalShellKernel_le
    (m : ℕ) (x : Euclidean (d + 1)) (v : Fin m → Euclidean (d + 1))
    {M : ℝ} (hbound : ∀ r ∈ Icc 0 Δ, ‖iteratedFDeriv ℝ m (Kphys r) x v‖ ≤ M) :
    ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo χA χo t y) x v‖ ≤ M * volume.real (Icc 0 Δ) := by
  rw [iteratedFDeriv_elapsedPhysicalShellKernel_eq_integral backward hρ Δ Ψ b
    χout χsource β mi mo χA χo θ y hθ hΨ hb hi ho hg hc c hF ha hK hs m x v]
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc 0 Δ))
    (Filter.Eventually.mono (ae_restrict_mem measurableSet_Icc) (fun r hr ↦ hbound r hr))
  simpa only [Measure.real, Measure.restrict_apply_univ] using h

end Physical

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
