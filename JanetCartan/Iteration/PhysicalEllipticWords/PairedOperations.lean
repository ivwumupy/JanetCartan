module

public import JanetCartan.Iteration.PhysicalEllipticWords.EndpointComplete
public import JanetCartan.Iteration.PhysicalEllipticWords.AlgebraicComplete
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.ConjugateSources
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PhysicalCoordinates
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators

/-!
# Exact operations on the reserved original residual letters

These deductions retain the natural source plateau while applying the literal
physical permutation, conjugate pair, scalar and measurement cutoff. Their
analytic inputs are produced by `EndpointComplete`, `AlgebraicComplete` and the
characteristic constructors. They are used by the actual paired alphabet's
`hstep` in `actual_finite_residual_word_reserved_bounds_of_one_step`; they do not
assert an inverse or an unconditional primary construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalEllipticWords
open RegularSector.Realization
open Pseudodifferential FourierIntegral FourierIntegral.LowBounds
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open ResponseTransfer.RetainedFactors
open RegularSector.FiniteEvolution RegularSector.NormalizedSolver
open RegularSector.Characteristic.ResidualCoordinates
open FixedDomainInverse.FiniteResidualEnvelopes
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect

variable {d : ℕ} {I : Type}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))
local notation "H" => Lp F 2 (volume : Measure E)

local instance : StarModule ℝ H where
  star_smul c u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul (star c) (star u), Lp.coeFn_star u] with x h₁ h₂ h₃ h₄
    simp only [Pi.star_apply] at h₁ h₄
    simp only [h₃, Pi.smul_apply, h₄, star_smul]

/-- The precise natural-reserve output of one original letter. An inverse
frequency factor, when present, is part of `A`, not a lost source derivative
(`app:ch_response:eq:response-graded-reduced`). -/
def ReservedLetterBounds (V : Set Par) (g : I → Par → H)
    (A K : I → ℝ) (reserve : ℕ) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (g i) V) ∧
  ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ≤
          C * A i * K i ^ (s + ps.length - reserve)

open FourierTransform

private theorem paired_scalar_complex_smul (s : ℝ) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure E)) (hu : MemFourierSobolev s u) :
    MemFourierSobolev s (z • u) ∧
      fourierSobolevNorm s (z • u) = ‖z‖ * fourierSobolevNorm s u := by
  have hf : 𝓕 (z • u) = z • 𝓕 u := map_smul (fourierCLM ℂ _) z u
  have hw : weightedL2Fourier s (z • u) =ᵐ[volume] z • weightedL2Fourier s u := by
    filter_upwards [Lp.coeFn_smul z (𝓕 u)] with ξ hξ
    simp only [weightedL2Fourier, hf, hξ, Pi.smul_apply]
    exact smul_comm _ _ _
  have hm : MemFourierSobolev s (z • u) := (hu.const_smul z).ae_eq hw.symm
  have he : hm.toLp (weightedL2Fourier s (z • u)) = z • hu.toLp (weightedL2Fourier s u) := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ hw
  refine ⟨hm, ?_⟩
  have hn := congrArg norm he
  rw [norm_smul] at hn
  simpa only [Lp.norm_toLp, fourierSobolevNorm] using hn

private theorem vector_fourier_complex_smul (s : ℝ) (z : ℂ) (u : H)
    (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (z • u) ∧
      vectorFourierSobolevNorm s (z • u) ≤ ‖z‖ * vectorFourierSobolevNorm s u := by
  have hc j : finiteL2CoordinateIsometry volume (z • u) j =
      z • finiteL2CoordinateIsometry volume u j :=
    congrArg (fun f ↦ f j) (map_smul (finiteL2CoordinateIsometry volume) z u)
  have hm : MemVectorFourierSobolev s (z • u) := by
    intro j
    rw [hc]
    exact (paired_scalar_complex_smul s z _ (hu j)).1
  refine ⟨hm, vectorFourierSobolevNorm_le_of_coordinate_bounds (norm_nonneg z) _ _ ?_⟩
  intro j
  rw [hc]
  exact (paired_scalar_complex_smul s z _ (hu j)).2.le

namespace ReservedLetterBounds

/-- Multiplication by the actual complex normalization, including `1/i` and
`1/2`, preserves the natural reserve (`energy-complete-residual`). -/
theorem smul {V : Set Par} (hV : IsOpen V) {g : I → Par → H}
    {A K : I → ℝ} {reserve : ℕ} (hg : ReservedLetterBounds V g A K reserve) (z : ℂ) :
    ReservedLetterBounds V (fun i c ↦ z • g i c) A K reserve := by
  let Mz : H →L[ℝ] H := (z • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
  have hsm i : ContDiffOn ℝ ∞ (fun c ↦ z • g i c) V :=
    Mz.contDiff.comp_contDiffOn (hg.1 i)
  refine ⟨hsm, ?_⟩
  intro ps hps s
  obtain ⟨C, hC, hb⟩ := hg.2 ps hps s
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg z) hC, ?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ z • g i c) c =
      z • orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hg.1 i) ps hc]
    have hat : ContDiffAt ℝ ps.length (g i) c :=
      ((hg.1 i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (Mz.iteratedFDeriv_comp_left hat (le_refl (ps.length : ℕ∞ω)))
  rw [he]
  obtain ⟨hm, hn⟩ := hb i c hc
  obtain ⟨hzm, hzn⟩ := vector_fourier_complex_smul (s : ℝ) z _ hm
  exact ⟨hzm, hzn.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg z)).trans_eq (by ring))⟩

/-- Sum the two original responses before normalizing the pair. No negative
power is extracted below the natural source reserve. -/
theorem add {V : Set Par} (hV : IsOpen V) {g h : I → Par → H}
    {A K : I → ℝ} {reserve : ℕ}
    (hg : ReservedLetterBounds V g A K reserve) (hh : ReservedLetterBounds V h A K reserve) :
    ReservedLetterBounds V (fun i c ↦ g i c + h i c) A K reserve := by
  have hsm i : ContDiffOn ℝ ∞ (fun c ↦ g i c + h i c) V := (hg.1 i).add (hh.1 i)
  refine ⟨hsm, ?_⟩
  intro ps hps s
  obtain ⟨Cg, hCg, hgb⟩ := hg.2 ps hps s
  obtain ⟨Ch, hCh, hhb⟩ := hh.2 ps hps s
  refine ⟨Cg + Ch, add_nonneg hCg hCh, ?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
      (fun c ↦ g i c + h i c) c =
      orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c +
        orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h i) c := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hg.1 i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hh.1 i) ps hc]
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (iteratedFDeriv_add_apply (i := ps.length)
        (((hg.1 i).contDiffAt (hV.mem_nhds hc)).of_le (by simp))
        (((hh.1 i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)))
  rw [he]
  obtain ⟨hgm, hgn⟩ := hgb i c hc
  obtain ⟨hhm, hhn⟩ := hhb i c hc
  obtain ⟨hm, hn⟩ := TerminalBounds.add_bound hgm hhm
  exact ⟨hm, hn.trans ((add_le_add hgn hhn).trans_eq (by ring))⟩

/-- Whole conjugation preserves every ordered jet of the same response; this
is not a replacement for an operator-adjoint estimate. -/
theorem star {V : Set Par} {g : I → Par → H} {A K : I → ℝ} {reserve : ℕ}
    (hg : ReservedLetterBounds V g A K reserve) :
    ReservedLetterBounds V (fun i c ↦ star (g i c)) A K reserve := by
  refine ⟨fun i ↦ (starL' ℝ : H ≃L[ℝ] H).contDiff.comp_contDiffOn (hg.1 i), ?_⟩
  intro ps hps s
  obtain ⟨C, hC, hb⟩ := hg.2 ps hps s
  obtain ⟨D, hD, hstar⟩ := exists_star_fourierSobolev_constant (d + 1) (d + 1) s
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  intro i c hc
  rw [orderedTransferAction_star]
  obtain ⟨hm, hn⟩ := hb i c hc
  obtain ⟨hsm, hsn⟩ := hstar _ hm
  exact ⟨hsm, hsn.trans ((mul_le_mul_of_nonneg_left hn hD.le).trans_eq (by ring))⟩

/-- The actual fixed physical output cut has no parameter or source-order
loss. Its Sobolev multiplier bound is constructed, not assumed. -/
theorem cut {V : Set Par} (hV : IsOpen V) {g : I → Par → H}
    {A K : I → ℝ} {reserve : ℕ} (hg : ReservedLetterBounds V g A K reserve)
    (μ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) :
    ReservedLetterBounds V
      (fun i c ↦ sourceCutMultiplier μ hμ.continuous hμb (g i c)) A K reserve := by
  let Mμ : H →L[ℝ] H := (sourceCutMultiplier μ hμ.continuous hμb).restrictScalars ℝ
  have hsm i : ContDiffOn ℝ ∞ (fun c ↦ sourceCutMultiplier μ hμ.continuous hμb (g i c)) V :=
    Mμ.contDiff.comp_contDiffOn (hg.1 i)
  refine ⟨hsm, ?_⟩
  intro ps hps s
  obtain ⟨C, hC, hb⟩ := hg.2 ps hps s
  obtain ⟨D, hD, hcut⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d + 1) μ hμ hμc hμb s
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
      (fun c ↦ sourceCutMultiplier μ hμ.continuous hμb (g i c)) c =
      sourceCutMultiplier μ hμ.continuous hμb
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hg.1 i) ps hc]
    have hat : ContDiffAt ℝ ps.length (g i) c :=
      ((hg.1 i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (Mμ.iteratedFDeriv_comp_left hat (le_refl (ps.length : ℕ∞ω)))
  rw [he]
  obtain ⟨hm, hn⟩ := hb i c hc
  obtain ⟨hcm, hcn⟩ := hcut _ hm
  exact ⟨hcm, hcn.trans ((mul_le_mul_of_nonneg_left hn hD).trans_eq (by ring))⟩

/-- Undo the SAME selected physical permutation. Every Sobolev norm is
preserved exactly and the natural reserve is untouched. -/
theorem physical {V : Set Par} (hV : IsOpen V) {g : I → Par → H}
    {A K : I → ℝ} {reserve : ℕ} (hg : ReservedLetterBounds V g A K reserve)
    (index : Fin (d + 1)) :
    ReservedLetterBounds V (fun i c ↦ (physicalPullbackL2 index).symm (g i c)) A K reserve := by
  let e : H →L[ℝ] H :=
    (physicalPullbackL2 index).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hsm i : ContDiffOn ℝ ∞ (fun c ↦ (physicalPullbackL2 index).symm (g i c)) V :=
    e.contDiff.comp_contDiffOn (hg.1 i)
  refine ⟨hsm, ?_⟩
  intro ps hps s
  obtain ⟨C, hC, hb⟩ := hg.2 ps hps s
  refine ⟨C, hC, ?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
      (fun c ↦ (physicalPullbackL2 index).symm (g i c)) c =
      (physicalPullbackL2 index).symm
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hg.1 i) ps hc]
    have hat : ContDiffAt ℝ ps.length (g i) c :=
      ((hg.1 i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (e.iteratedFDeriv_comp_left hat (le_refl (ps.length : ℕ∞ω)))
  rw [he]
  obtain ⟨hm, hn⟩ := hb i c hc
  exact ⟨(memVectorFourierSobolev_physicalPullbackL2_symm index (s : ℝ) _).mpr hm,
    (vectorFourierSobolevNorm_physicalPullbackL2_symm index (s : ℝ) _).trans_le hn⟩

/-- The residual-word consumer needs order zero. Since the actual carrier is
at least one, forgetting the PDO's extra inverse-frequency gain changes neither
the amplitude nor the natural derivative reserve. -/
theorem discard_inverse_frequency {V : Set Par} {g : I → Par → H}
    {lam A K : I → ℝ} {reserve : ℕ}
    (hg : ReservedLetterBounds V g (fun i ↦ lam i ^ (-1 : ℤ) * A i) K reserve)
    (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i) :
    ReservedLetterBounds V g A K reserve := by
  refine ⟨hg.1, ?_⟩
  intro ps hps s
  obtain ⟨C, hC, hb⟩ := hg.2 ps hps s
  refine ⟨C, hC, ?_⟩
  intro i c hc
  obtain ⟨hm, hn⟩ := hb i c hc
  have hgain : C * lam i ^ (-1 : ℤ) ≤ C := by
    rw [zpow_neg_one]
    exact mul_le_of_le_one_right hC (inv_le_one_of_one_le₀ (hlam i))
  refine ⟨hm, hn.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hgain (hA i)) (pow_nonneg (hK i) _)

end ReservedLetterBounds

/-- The external half and whole-operator conjugate are retained literally.
The opposite source response is the input to the conjugated summand, not an
independently selected operator (`energy-complete-residual`). -/
theorem normalized_pair_reserved_bounds
    {V : Set Par} (hV : IsOpen V) (T : I → H →L[ℂ] H) (lam A K : I → ℝ)
    (φ : I → Par → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (u : I → Par → H) (reserve : ℕ)
    (hforward : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (T i) (u i c)) A K reserve)
    (hnegative : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ -φ i c y) (hφ i c).neg
        (T i) (star (u i c))) A K reserve) (z : ℂ) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c)
        (normalizedPair (z • T i)) (u i c)) A K reserve := by
  have hstar := hnegative.star
  have hconjugate : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c)
        (boundedConjugate (T i)) (u i c)) A K reserve := by
    simpa only [demodulated_conjugate_eq_star_negative_source] using hstar
  have hsum := ((hforward.smul hV z).add hV (hconjugate.smul hV (star z))).smul hV (1 / 2 : ℂ)
  have he : (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c)
      (normalizedPair (z • T i)) (u i c)) =
      (fun i c ↦ (1 / 2 : ℂ) •
        (z • demodulatedL2Operator (lam i) (φ i c) (hφ i c) (T i) (u i c) +
         star z • demodulatedL2Operator (lam i) (φ i c) (hφ i c)
           (boundedConjugate (T i)) (u i c))) := by
    funext i c
    rw [normalizedPair_eq]
    simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply,
      smul_apply, add_apply, map_smul, map_add]
    congr 2
    change carrierMultiplication (-(lam i)) (φ i c) (hφ i c)
      (star (z • (T i) (star (carrierMultiplication (lam i) (φ i c) (hφ i c) (u i c))))) =
      star z • carrierMultiplication (-(lam i)) (φ i c) (hφ i c)
        (star ((T i) (star (carrierMultiplication (lam i) (φ i c) (hφ i c) (u i c)))))
    rw [star_smul, map_smul]
  rw [he]
  exact hsum

end JanetCartan.PhysicalEllipticWords
