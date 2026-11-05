module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedOperations
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.SourceDomain

/-!
# Reassemble the original characteristic source parameter partition

These are downstream assembly lemmas for the SAME bounded operator and source.
The two input bounds are supplied by the checked complete active characteristic
estimates and the checked inactive original-operator estimates, respectively.
The original supported active branch extends by zero to the original parameter
domain; arbitrary inactive precision preserves the natural reserve and the
solver/residual frequency order. No new inverse, phase or datum is selected.
Consumer: the retarded paired letter and final solver in
`actual_finite_residual_word_reserved_bounds_of_one_step`
(`app:ch_response:eq:response-whole-source-partition`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPrimary.CharacteristicPartition
open PhysicalEllipticWords FixedDomainInverse.ParameterSourceCutoffs
open Pseudodifferential FourierIntegral ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.CompactTransfer
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
variable {d : ℕ} {I : Type}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)

/-- An exact partition of the original source remains exact after the SAME
operator and carrier conjugation, including a literal adjoint operator.
Consumer: active/inactive characteristic reassembly. -/
theorem demodulated_originalDatum_partition
    (a a₀ a₁ : E × Par → F) (ha : ContDiff ℝ ∞ a)
    (ha₀ : ContDiff ℝ ∞ a₀) (ha₁ : ContDiff ℝ ∞ a₁)
    {S : Set E} (hS : IsCompact S)
    (has : ∀ q, q.1 ∉ S → a q = 0)
    (has₀ : ∀ q, q.1 ∉ S → a₀ q = 0)
    (has₁ : ∀ q, q.1 ∉ S → a₁ q = 0)
    (hsum : ∀ q, a q = a₀ q+a₁ q)
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (Op : H →L[ℂ] H) (c : Par) :
    demodulatedL2Operator lam φ hφ Op
      (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)) =
    demodulatedL2Operator lam φ hφ Op
      (graphTestToLp (vectorOriginalDatumTest a₀ ha₀ hS has₀ [] c)) +
    demodulatedL2Operator lam φ hφ Op
      (graphTestToLp (vectorOriginalDatumTest a₁ ha₁ hS has₁ [] c)) := by
  have he : graphTestToLp (vectorOriginalDatumTest a ha hS has [] c) =
      graphTestToLp (vectorOriginalDatumTest a₀ ha₀ hS has₀ [] c) +
      graphTestToLp (vectorOriginalDatumTest a₁ ha₁ hS has₁ [] c) := by
    apply Lp.ext
    filter_upwards [vectorOriginalDatumTest_toLp_ae a ha hS has [] c,
      vectorOriginalDatumTest_toLp_ae a₀ ha₀ hS has₀ [] c,
      vectorOriginalDatumTest_toLp_ae a₁ ha₁ hS has₁ [] c,
      Lp.coeFn_add (graphTestToLp (vectorOriginalDatumTest a₀ ha₀ hS has₀ [] c))
        (graphTestToLp (vectorOriginalDatumTest a₁ ha₁ hS has₁ [] c))] with y hy h₀ h₁ hplus
    rw [hplus,Pi.add_apply,hy,h₀,h₁]
    exact hsum (y,c)
  rw [he,map_add]

/-- A vanishing parameter slice of the original datum remains zero after the
SAME carrier-conjugated operator. No operator norm estimate is used. -/
theorem demodulated_originalDatum_zero
    (a : E × Par → F) (ha : ContDiff ℝ ∞ a)
    {S : Set E} (hS : IsCompact S) (has : ∀ q, q.1 ∉ S → a q = 0)
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (Op : H →L[ℂ] H)
    (c : Par) (hz : ∀ y, a (y,c) = 0) :
    demodulatedL2Operator lam φ hφ Op
      (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)) = 0 := by
  have he : graphTestToLp (vectorOriginalDatumTest a ha hS has [] c) = 0 := by
    apply Lp.ext
    filter_upwards [vectorOriginalDatumTest_toLp_ae a ha hS has [] c,
      Lp.coeFn_zero F 2 (volume : Measure E)] with y hy hzero
    simpa only [originalDatumDerivative,orderedTransferAction,hz,hzero,Pi.zero_apply] using hy
  rw [he,map_zero]

/-- The active envelope, supported in the original closed parameter carrier,
extends to the original parameter domain with identical constants and reserve.
This closes the domain mismatch between the active neighborhood and full source;
it does not assume any response bound outside the active neighborhood. -/
theorem reserved_letter_bounds_of_closed_parameter_support
    {U C V : Set Par} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    {g : I → Par → H} {A K : I → ℝ} {reserve : ℕ}
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i)
    (hs : ∀ i c, c ∉ C → g i c = 0)
    (hg : ReservedLetterBounds U g A K reserve) :
    ReservedLetterBounds V g A K reserve := by
  have hreg i : ContDiff ℝ ∞ (g i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro c
    by_cases hc : c ∈ U
    · exact (hg.1 i).contDiffAt (hU.mem_nhds hc)
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      filter_upwards [hC.isOpen_compl.mem_nhds (fun h ↦ hc (hCU h))] with b hb
      exact hs i b hb
  refine ⟨fun i ↦ (hreg i).contDiffOn,?_⟩
  intro ps hps s
  obtain ⟨B,hB,hbound⟩ := hg.2 ps hps s
  refine ⟨B,hB,?_⟩
  intro i c _hcV
  by_cases hc : c ∈ C
  · exact hbound i c (hCU hc)
  · have hz : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c = 0 := by
      rw [orderedParameterWord_eq_iteratedFDeriv isOpen_univ (hreg i).contDiffOn ps (mem_univ c)]
      exact parameter_jet_eq_zero_off_closed_support (fun q : Unit × Par ↦ g i q.2)
        hC (fun q hq ↦ hs i q.2 hq) hc () ps.length ps.get
    rw [hz]
    let G : GradedScale H := vectorFourierSobolevScale
    have hm : MemVectorFourierSobolev (s : ℝ) (0 : H) := (G.level s).zero_mem
    refine ⟨hm,?_⟩
    rw [← vectorFourierSobolevScale_gradeNorm s hm]
    change G.gradeNorm s 0 ≤ _
    rw [G.gradeNorm_eq hm]
    change G.seminorm s 0 ≤ _
    rw [map_zero]
    exact mul_nonneg (mul_nonneg hB (hA i)) (pow_nonneg (hK i) _)

/-- The checked inactive arbitrary-precision estimate implies exactly the
reserved ordered bound used by a solver or residual letter. The natural
exponent is retained, including its plateau; no negative reserve is extracted.
Consumer: the inactive part of the SAME paired characteristic letter. -/
theorem reserved_letter_bounds_of_arbitrary_precision
    {V : Set Par} (hV : IsOpen V) (g : I → Par → H)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (g i) V)
    (lam A K : I → ℝ) (p : ℤ) (reserve : ℕ)
    (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hdecay : ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ w : Fin k → Par, (∀ j, ‖w j‖ ≤ 1) →
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k (g i) c w) ∧
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (g i) c w) ≤
          C*A i*lam i^(-Q)) :
    ReservedLetterBounds V g (fun i ↦ lam i^p*A i) K reserve := by
  refine ⟨hsm,?_⟩
  intro ps hps s
  obtain ⟨C,hC,hbound⟩ := hdecay s ps.length (-(p : ℝ))
  refine ⟨C,hC,?_⟩
  intro i c hc
  rw [orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc]
  obtain ⟨hm,hb⟩ := hbound i c hc ps.get (fun j ↦ hps _ (List.get_mem _ _))
  simp only [neg_neg,Real.rpow_intCast] at hb
  refine ⟨hm,hb.trans ?_⟩
  have hAi := hA i
  have hlampos := hlam i
  calc C*A i*lam i^p ≤ (C*A i*lam i^p)*K i^(s+ps.length-reserve) :=
         le_mul_of_one_le_right (by positivity) (one_le_pow₀ (hK i))
       _ = C*(lam i^p*A i)*K i^(s+ps.length-reserve) := by ring

/-- The actual parameter partition closes the complete source estimate for
one fixed physical operator. The active estimate is used only on its genuine
neighborhood; its original closed support supplies the extension. Both branch
bounds are provided by the characteristic constructors, not assumed by the
parent existence result. The operator may equally be the literal adjoint.
Consumer: the paired retarded letter and the SAME final solver step. -/
theorem whole_source_reserved_bounds_of_parameter_partition
    {U V C : Set Par} (hU : IsOpen U) (hV : IsOpen V)
    (hC : IsClosed C) (hCU : C ⊆ U)
    (a a₀ a₁ : I → E × Par → F)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (ha₀ : ∀ i, ContDiff ℝ ∞ (a₀ i))
    (ha₁ : ∀ i, ContDiff ℝ ∞ (a₁ i))
    {S : Set E} (hS : IsCompact S)
    (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (has₀ : ∀ i q, q.1 ∉ S → a₀ i q = 0)
    (has₁ : ∀ i q, q.1 ∉ S → a₁ i q = 0)
    (hsum : ∀ i q, a i q = a₀ i q+a₁ i q)
    (hparam₀ : ∀ i c, c ∉ C → ∀ y, a₀ i (y,c) = 0)
    (lam A K : I → ℝ) (reserve : ℕ)
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i)
    (φ : I → Par → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (Op : I → H →L[ℂ] H)
    (hactive : ReservedLetterBounds U
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c))) A K reserve)
    (hinactive : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a₁ i) (ha₁ i) hS (has₁ i) [] c))) A K reserve) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve := by
  have hglobal := reserved_letter_bounds_of_closed_parameter_support (V := V)
    hU hC hCU hA hK
    (fun i c hc ↦ demodulated_originalDatum_zero (a₀ i) (ha₀ i) hS (has₀ i)
      (lam i) (φ i c) (hφ i c) (Op i) c (hparam₀ i c hc)) hactive
  have hadd := hglobal.add hV hinactive
  have he : (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) =
      (fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c)) +
      demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Op i)
        (graphTestToLp (vectorOriginalDatumTest (a₁ i) (ha₁ i) hS (has₁ i) [] c))) := by
    funext i c
    exact demodulated_originalDatum_partition (a i) (a₀ i) (a₁ i) (ha i) (ha₀ i) (ha₁ i)
      hS (has i) (has₀ i) (has₁ i) (hsum i) (lam i) (φ i c) (hφ i c) (Op i) c
  rw [he]
  exact hadd

end JanetCartan.PhysicalPrimary.CharacteristicPartition
