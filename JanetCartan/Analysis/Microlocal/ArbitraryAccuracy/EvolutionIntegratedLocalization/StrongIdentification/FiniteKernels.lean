module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellKernels
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CutoffSums
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite partitions of the literal elapsed shell kernel

Elapsed integration preserves both independent frequency partitions. The
finite kernel is the literal forward or reverse composition, including the
regularized identity term and both localizers. Compact primitive carriers
justify every interchange before the shell estimate is used.

Consumers: the shell summation and L² identification steps of
`app:ch_regular:eq:chain-tail`, with the bounded elapsed interval from
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph RegularSector.Characteristic.EvolutionIntegral
open KernelLimits

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => JointVariables E
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem continuous_parameter_jointIntegrand
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (x : E) : Continuous (fun p : (ℝ × E) × P ↦
      regularizedJointIntegrand backward (S p.1.1) (A p.1.1) mi mo χA χo x p.1.2 p.2) := by
  change Continuous (mi : E × E → ℝ) at hi
  change Continuous (mo : E × E → ℝ) at ho
  change E × E → ℝ at mi mo
  have hs : Continuous (fun p : (ℝ × E) × P ↦ S p.1.1 p.2.1.1 p.2.2.1) :=
    hS.comp (f := fun p : (ℝ × E) × P ↦ (p.1.1, p.2.1.1, p.2.2.1)) (by fun_prop)
  have ha : Continuous (fun p : (ℝ × E) × P ↦ A p.1.1 p.2.1.1 p.2.1.2 p.2.2.1) :=
    hA.comp (f := fun p : (ℝ × E) × P ↦ (p.1.1, p.2.1, p.2.2.1)) (by fun_prop)
  have hp : Continuous (fun p : (ℝ × E) × P ↦ jointPhase backward (S p.1.1) x p.1.2 p.2) := by
    cases backward <;>
      simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase] <;>
      fun_prop
  have hb : Continuous (fun p : (ℝ × E) × P ↦ χA p.2.2.1 * χo p.2.2.2.2 *
      (1 - mo (x, p.2.2.2.2)) * mi (p.1.2, p.2.2.2.1)) := by fun_prop
  exact (Complex.continuous_exp.comp ((continuous_const (y := Complex.I)).mul
    (Complex.continuous_ofReal.comp hp))).smul ((Complex.continuous_ofReal.comp hb).smul ha)

private theorem continuous_parameter_jointKernel
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (A r) mi χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier) (x : E) :
    Continuous (fun p : ℝ × E ↦ regularizedJointKernel backward (S p.1) (A p.1)
      mi mo χA χo x p.2) := by
  have he (r : ℝ) (y : E) : regularizedJointKernel backward (S r) (A r) mi mo χA χo x y =
      jointNormalization (d + 1) • ∫ p in (c 0).jointCarrier,
        regularizedJointIntegrand backward (S r) (A r) mi mo χA χo x y p := by
    unfold regularizedJointKernel
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    apply (c r).integrand_zero backward (S r) mo x y p
    intro h
    exact hp ((hcommon r) ▸ h.1)
  simp_rw [he]
  exact (continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (z : ℝ × E) (p : P) ↦ regularizedJointIntegrand backward (S z.1) (A z.1) mi mo χA χo x z.2 p)
    (continuous_parameter_jointIntegrand backward S A mi mo χA χo hS hA hi ho hg hc x)
    (c 0).compact_jointCarrier).const_smul (jointNormalization (d + 1))

/-- Finite independent graph/output sums are exactly the corresponding
cutoffs of `elapsedPhysicalShellKernel`. Common carriers are primitive compact
base and frequency supports (for elapsed amplitudes the fixed masks supply
these); there is no kernel majorant or operator tail premise. Both the low
graph pieces and the zeroth output piece may occur in either finite set.
Consumer: shell assembly in `app:ch_regular:eq:chain-tail`. -/
theorem elapsedPhysicalShellKernel_finset_cutoffs {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA : ι → E → ℝ) (χo : κ → E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo)
    (hg : ∀ j, Continuous (χA j)) (hc : ∀ k, Continuous (χo k))
    (c : ∀ r j k, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (χA j) (χo k))
    (hcommon : ∀ r j k, (c r j k).jointCarrier = (c 0 j k).jointCarrier) (x y : E) :
    elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
      (fun ξ ↦ ∑ j ∈ s, χA j ξ) (fun ζ ↦ ∑ k ∈ t, χo k ζ) x y =
      ∑ j ∈ s, ∑ k ∈ t,
        elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo (χA j) (χo k) x y := by
  have hi' : Continuous (fun p : E × E ↦ mi (p.1, ρ⁻¹ • p.2)) := hi.comp (by fun_prop)
  have ho' : Continuous (fun p : E × E ↦ mo (p.1, ρ⁻¹ • p.2)) := ho.comp (by fun_prop)
  have hSi (r : ℝ) : Continuous (Function.uncurry (elapsedPhase Ψ r)) :=
    hS.comp (continuous_const.prodMk continuous_id)
  have hAi (r : ℝ) : Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2) :=
    hA.comp (continuous_const.prodMk continuous_id)
  have hint (j : ι) (k : κ) : IntegrableOn (fun r ↦ regularizedJointKernel backward
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) (χA j) (χo k) x y)
      (Icc 0 Δ) :=
    ((continuous_parameter_jointKernel backward _ _ _ _ _ _ hS hA hi' ho' (hg j) (hc k)
      (fun r ↦ c r j k) (fun r ↦ hcommon r j k) x).comp
        (continuous_id.prodMk continuous_const)).integrableOn_Icc
  simp only [elapsedPhysicalShellKernel]
  simp_rw [regularizedJointKernel_finset_cutoffs s t backward _ _ _ _ χA χo
    (hSi _) (hAi _) hi' ho' hg hc (c _) x y]
  rw [integral_finsetSum s (fun j _ ↦ integrable_finsetSum t (fun k _ ↦ hint j k))]
  simp_rw [integral_finsetSum t (fun k _ ↦ hint _ k)]


/-- Source continuity of the actual elapsed kernel follows from compact
primitive integration, before any shell estimate. Consumer: summation against
L¹ test inputs in `app:ch_regular:eq:chain-tail`. -/
theorem continuous_elapsedPhysicalShellKernel_source
    (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier)
    (x : E) :
    Continuous (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo x) := by
  have hK := continuous_parameter_jointKernel backward (elapsedPhase Ψ)
    (orientedElapsedAmplitude backward b χout χsource β) _ _ χA χo hS hA
    (hi.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
    (ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))) hg hc c hcommon x
  exact continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (y : E) (r : ℝ) ↦ regularizedJointKernel backward (elapsedPhase Ψ r)
      (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y)
    (hK.comp (f := fun p : E × ℝ ↦ (p.2, p.1))
      (continuous_snd.prodMk continuous_fst)) (isCompact_Icc : IsCompact (Icc 0 Δ))

/-- Testing the bounded elapsed shell commutes with elapsed integration.
Every integral is justified by continuity and the common compact primitive
carriers. No Sobolev bound, summable majorant, or uncut realization is used
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedPhysicalShellKernel_test_fubini
    (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier)
    (hinput : ∀ r, (c r).inputBase = (c 0).inputBase)
    (f : E → Fin q → ℂ) (hf : Continuous f) (x : E) :
    (∫ y, (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo x y).mulVec (f y)) =
      ∫ r in Icc 0 Δ, ∫ y, (regularizedJointKernel backward (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y).mulVec (f y) := by
  let K := fun r y ↦ regularizedJointKernel backward (elapsedPhase Ψ r)
    (orientedElapsedAmplitude backward b χout χsource β r)
    (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y
  have hK : Continuous (Function.uncurry K) :=
    continuous_parameter_jointKernel backward (elapsedPhase Ψ)
      (orientedElapsedAmplitude backward b χout χsource β) _ _ χA χo hS hA
      (hi.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
      (ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))) hg hc c hcommon x
  have hz (r : ℝ) (y : E) (hy : y ∉ (c 0).inputBase) : K r y = 0 := by
    apply regularizedJointKernel_zero_off_input _ _ _ _ _ _ _ (c r) x y
    simpa only [hinput r] using hy
  have hm (y : E) : (∫ r in Icc 0 Δ, K r y).mulVec (f y) =
      ∫ r in Icc 0 Δ, (K r y).mulVec (f y) :=
    (((sourceMatrixAction (r := q)).flip (f y)).integral_comp_comm
      ((hK.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc)).symm
  have hprod : Integrable (fun p : ℝ × E ↦ (K p.1 p.2).mulVec (f p.2))
      ((volume.restrict (Icc 0 Δ)).prod (volume.restrict (c 0).inputBase)) := by
    rw [Measure.prod_restrict]
    exact (hK.matrix_mulVec (hf.comp continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (c 0).compact_inputBase)
  change (∫ y, (∫ r in Icc 0 Δ, K r y).mulVec (f y)) = _
  simp_rw [hm]
  calc
    (∫ y, ∫ r in Icc 0 Δ, (K r y).mulVec (f y)) =
        ∫ y in (c 0).inputBase, ∫ r in Icc 0 Δ, (K r y).mulVec (f y) := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [hz _ y hy])
    _ = ∫ r in Icc 0 Δ, ∫ y in (c 0).inputBase, (K r y).mulVec (f y) :=
      (integral_integral_swap hprod).symm
    _ = ∫ r in Icc 0 Δ, ∫ y, (K r y).mulVec (f y) := by
      apply integral_congr_ae
      filter_upwards [] with r
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [hz r y hy])

/-- The finite elapsed kernel is the actual physically rescaled localized
composition in either literal orientation. Both Fourier regularizers remain
independent, and the full `χo (1-mo)` includes the regularized identity term.
The reverse amplitude is the conjugate transpose in its original positions,
so the masks and Fourier multiplier retain Hilbert-adjoint order. Consumer:
finite-cutoff identification for `app:ch_regular:eq:chain-tail`. -/
theorem elapsedPhysicalShellKernel_test_eq_composition
    (backward : Bool) (ρ Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA χo)
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier)
    (hinput : ∀ r, (c r).inputBase = (c 0).inputBase)
    (f : E → Fin q → ℂ) (hf : Continuous f) (x : E) (hρ : ρ ≠ 0) :
    (∫ y, (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo x y).mulVec (f y)) =
      ∫ r in Icc 0 Δ, leftLocalizer ρ (fun p ↦ χo (ρ • p.2) * (1 - mo p))
        ((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun u z ξ ↦ (χA ξ : ℂ) • orientedElapsedAmplitude backward b χout χsource β r u z ξ)
          (rightLocalizer ρ mi f)) x := by
  rw [elapsedPhysicalShellKernel_test_fubini backward ρ Δ Ψ b χout χsource β mi mo χA χo
    hS hA hi ho hg hc c hcommon hinput f hf x]
  apply integral_congr_ae
  filter_upwards [] with r
  have hSr : Continuous (Function.uncurry (elapsedPhase Ψ r)) :=
    hS.comp (continuous_const.prodMk continuous_id)
  have hAr : Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2) :=
    hA.comp (continuous_const.prodMk continuous_id)
  cases backward
  · exact (forward_composition_scaled_eq_jointKernel _ _ ρ mi mo χA χo
      hSr hAr hi ho hg hc (c r) f hf x hρ).symm
  · exact (reverse_composition_scaled_eq_jointKernel _ _ ρ mi mo χA χo
      hSr hAr hi ho hg hc (c r) f hf x hρ).symm

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
