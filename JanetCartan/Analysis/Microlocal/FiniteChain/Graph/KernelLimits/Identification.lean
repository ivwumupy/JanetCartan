module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.SummedSupport

/-!
# Identification of the completed graph action

For `app:ch_regular:eq:chain-tail`, the conditional Cartesian Sobolev extension
represents the genuine physical limit of the regularized compositions. The
summable bounds on the actual matrix kernels and output jets are the explicit
inputs from `jc-graph-factor-kernel-estimates`. The identities and convergence
are deduced here. The fixed output cutoff is removed only after Fourier
inversion recovers the identity contribution and its common physical support.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral Retarded.KernelSobolev AmplitudeBound
open JanetCartan.RetardedSobolev.Spaces
variable {n r d m : ℕ}
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The physical vector datum corresponding to Cartesian scalar test channels
in the matrix extension of `app:ch_regular:eq:chain-tail`. -/
def physicalTestField (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (f : Fin r → Test d) : Euclidean n → Fin r → ℂ :=
  fun y b => (f b).val (J.symm y)

/-- Coordinate transport preserves smoothness of the test datum used in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem contDiff_physicalTestField (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (f : Fin r → Test d) : ContDiff ℝ ∞ (physicalTestField J f) :=
  contDiff_pi.mpr (fun b => (f b).property.1.comp J.symm.contDiff)

/-- All physical test channels have a common compact support, so their literal
matrix action is integrable (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_physicalTestField
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (f : Fin r → Test d) :
    HasCompactSupport (physicalTestField J f) := by
  apply HasCompactSupport.intro
    (isCompact_iUnion (fun b => (f b).property.2.comp_homeomorph J.symm.toHomeomorph))
  intro y hy
  funext b
  change (fun y => (f b).val (J.symm y)) y = 0
  exact image_eq_zero_of_notMem_tsupport (f := fun y => (f b).val (J.symm y))
    (fun hb => hy (mem_iUnion.mpr ⟨b, hb⟩))

section Identification
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
  (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
  (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ) (ψ : Euclidean n → ℝ)
  (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
  (hSc : Continuous (Function.uncurry S))
  (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
  (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
    A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
  (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hc : ∀ k, ContDiff ℝ ∞ (χo k))
  (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
  (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
  (μ ν : Measure ((Fin d → ℝ) × ℝ))
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  (hJ : MeasurePreserving (graphInputCoordinates J) μ volume)

local notation "K" => (fun (p : ℕ × ℕ) (a b : Fin r) => supportedJointKernelEntry J
  backward S A mi mo (χA (Prod.fst p)) (χo (Prod.snd p)) ψ
  (RegularizedCarriers.commonBases c (Prod.fst p) (Prod.snd p))
  hS hA hi ho (hg (Prod.fst p)) (hc (Prod.snd p)) (hg0 (Prod.fst p)) hψ hsψ a b)
local notation "sI" => (fun y : (Fin d → ℝ) × ℝ => J (Prod.snd y, Prod.fst y)) ⁻¹' RegularizedCarriers.inputBase (c 0 0)
local notation "sO" => J ⁻¹' tsupport ψ

include hSc hJ

omit [IsFiniteMeasureOnCompacts μ] in
/-- The literal finite matrix action is the sum of its actual Cartesian
channel integrals, with the precise joint normalization retained
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem sum_kernelIntegral_supportedJointKernelEntry_physical
    (f : Fin r → Test d) (p : ℕ × ℕ) (a : Fin r) (x : ℝ × (Fin d → ℝ)) :
    (∑ b, kernelIntegral (K p a b) μ (f b).val x) =
      (ψ (J x) : ℂ) * (∫ y, (regularizedJointKernel backward S A mi mo
        (χA p.1) (χo p.2) (J x) y).mulVec (physicalTestField J f y)) a := by
  have he b := kernelIntegral_supportedJointKernelEntry_physical J μ hJ backward S A mi mo
    (χA p.1) (χo p.2) ψ (RegularizedCarriers.commonBases c p.1 p.2)
    hS hA hi ho (hg p.1) (hc p.2) (hg0 p.1) hψ hsψ a b (f b).val x
  simp_rw [he, ← Finset.mul_sum]
  congr 1
  have hint b : Integrable (fun y => regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) (J x) y a b * (f b).val (J.symm y)) := by
    have hk : Continuous (fun y => regularizedJointKernel backward S A mi mo
        (χA p.1) (χo p.2) (J x) y a b) := (matrixEntryEvaluation a b).continuous.comp
      ((contDiff_regularizedJointKernel backward S A mi mo (χA p.1) (χo p.2)
        (c p.1 p.2) hS hA hi ho (hg p.1) (hc p.2) (hg0 p.1)).continuous.comp
          (continuous_const.prodMk continuous_id))
    exact (hk.mul ((f b).property.1.continuous.comp J.symm.continuous)).integrable_of_hasCompactSupport
      ((f b).property.2.comp_homeomorph J.symm.toHomeomorph).mul_left
  have hp := (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℂ] ℂ).integral_comp_comm
    (regularizedJointKernel_test_integrable backward S A mi mo (χA p.1) (χo p.2)
      hSc hA.continuous hi.continuous ho.continuous (hg p.1).continuous (hc p.2).continuous
      (c p.1 p.2) (physicalTestField J f) (contDiff_physicalTestField J f).continuous (J x))
  exact (integral_finsetSum Finset.univ (fun b _ => hint b)).symm.trans hp

/-- The summed zeroth Cartesian jets have the physical matrix value. This
uses the independently proved convergence of actual kernels on test inputs;
neither a composition identity nor a convergence claim is a premise
(`app:ch_regular:eq:chain-tail`). -/
theorem sum_summedJointKernel_zerothJet_physical
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k (a b : Fin r) (i : JetIndex d m) p (y : (Fin d → ℝ) × ℝ),
      ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
        (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C (j,k))
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀)
    (hb₀ : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo
      (χA j) (χo k) x y‖ ≤ C₀ (j,k))
    (f : Fin r → Test d) (a : Fin r) (p : (Fin d → ℝ) × ℝ) :
    (∑ b, ∫ y, (∑' q, kernelJet (K q a b) (zeroIndex d m) p y) * (f b).val (y.2, y.1) ∂μ) =
      (ψ (J (p.2, p.1)) : ℂ) * (∫ y, (∑' q : ℕ × ℕ,
        regularizedJointKernel backward S A mi mo (χA q.1) (χo q.2)
          (J (p.2, p.1)) y).mulVec (physicalTestField J f y)) a := by
  have hsum := hasSum_sum (s := Finset.univ) (fun b _ =>
    hasSum_kernelIntegral_jet (fun q => K q a b) μ C hs
      (fun q => hb q.1 q.2 a b) (f b) (zeroIndex d m) p)
  simp only [jet_zeroIndex] at hsum
  have hphys := hasSum_regularizedJointKernel_test backward S A mi mo
    (fun q : ℕ × ℕ => χA q.1) (fun q : ℕ × ℕ => χo q.2)
    hSc hA.continuous hi.continuous ho.continuous (fun q => (hg q.1).continuous)
    (fun q => (hc q.2).continuous) C₀ hs₀ (fun q => hb₀ q.1 q.2)
    (physicalTestField J f) ((contDiff_physicalTestField J f).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_physicalTestField J f)) (J (p.2, p.1))
  have he q := sum_kernelIntegral_supportedJointKernelEntry_physical J backward S A mi mo
    χA χo ψ c hSc hS hA hi ho hg hc hg0 hψ hsψ μ hJ f q a (p.2, p.1)
  simp only [he] at hsum
  exact hsum.unique ((Pi.hasSum.mp hphys a).mul_left (ψ (J (p.2, p.1)) : ℂ))

/-- A conditional Sobolev extension of the genuine, uncut physical limit in
both literal orientations. All completed jets and shell actions are retained;
the zeroth jet is identified with the full matrix action after removing the
auxiliary output cutoff. The two majorants are estimates of the actual kernels
and their cutoff output jets, supplied by `jc-graph-factor-kernel-estimates` and
instantiated in the parent (`app:ch_regular:eq:chain-tail`). -/
theorem exists_jointKernel_physical_extension
    (C : ℕ × ℕ → ℝ) (hC : ∀ q, 0 ≤ C q) (hs : Summable C)
    (hb : ∀ j k (a b : Fin r) (i : JetIndex d m) p (y : (Fin d → ℝ) × ℝ),
      ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
        (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C (j,k))
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀)
    (hb₀ : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo
      (χA j) (χo k) x y‖ ≤ C₀ (j,k))
    (hcb : ∀ N ξ, |∑ k ∈ Finset.range N, χo k ξ| ≤ 1)
    (hclim : ∀ ξ, Tendsto (fun N => ∑ k ∈ Finset.range N, χo k ξ) atTop (𝓝 1))
    (B : ℝ) (hbmo : ∀ x ξ, |mo (x,ξ)| ≤ B)
    (t : Set (Euclidean n)) (ht : IsCompact t) (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (hplateau : ∀ x ∈ leakageOutputCarrier backward (c 0 0).amplitudeBase t, ψ x = 1) :
    ∃ T : Fin r → Fin r → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖matrixOperator T‖ ≤ (r : ℝ) * r *
        ((∑' q, C q) * compactSupportFactor μ ν sI (Prod.swap ⁻¹' sO)) ∧
      (∀ a b f, HasSum (fun q => ofTest m ν (kernelIntegralLinear (K q a b) μ f))
        (T a b (ofTest 0 μ f))) ∧
      (∀ a b f (i : JetIndex d m), (T a b (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p => ∫ y, (∑' q, kernelJet (K q a b) i p y) * f.val (y.2, y.1) ∂μ) ∧
      (∀ (f : Fin r → Test d) (a : Fin r),
        ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
          (zeroIndex d m) =ᵐ[ν] fun p => (∫ y, (∑' q : ℕ × ℕ,
            regularizedJointKernel backward S A mi mo (χA q.1) (χo q.2)
              (J (p.2, p.1)) y).mulVec (physicalTestField J f y)) a) ∧
      ∀ (f : Fin r → Test d) (a : Fin r), ∀ᵐ p ∂ν,
        Tendsto (fun q : Finset ℕ × Finset ℕ =>
          leftLocalizer 1 (fun z => (∑ k ∈ q.2, χo k z.2) * (1 - mo z))
            ((if backward then reverseGraphOperator else graphOperator) S
              (fun u z ξ => ((∑ j ∈ q.1, χA j ξ) : ℂ) • A u z ξ)
              (rightLocalizer 1 mi (physicalTestField J f))) (J (p.2, p.1)) a) atTop
          (𝓝 (((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
            (zeroIndex d m) p)) := by
  obtain ⟨T, hn, htest, hjet⟩ := exists_jointKernel_matrix_shell_extension J backward S A mi mo
    χA χo ψ c hS hA hi ho hg hc hg0 hψ hsψ μ ν C hC hs hb
  have hident : ∀ (f : Fin r → Test d) (a : Fin r),
      ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
        (zeroIndex d m) =ᵐ[ν] fun p => (∫ y, (∑' q : ℕ × ℕ,
          regularizedJointKernel backward S A mi mo (χA q.1) (χo q.2)
            (J (p.2, p.1)) y).mulVec (physicalTestField J f y)) a := by
    intro f a
    let P : Sobolev m ν →L[ℂ] Lp ℂ 2 ν :=
      (ContinuousLinearMap.proj (zeroIndex d m)).comp (sobolevSubmodule m ν).subtypeL
    have he : ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
        (zeroIndex d m) = ∑ b, (T a b (ofTest 0 μ (f b))).val (zeroIndex d m) := by
      change P (matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b))) a) = _
      rw [matrixOperator_apply, map_sum]
      rfl
    rw [he]
    have hj : ∀ᵐ p ∂ν, ∀ b, (T a b (ofTest 0 μ (f b))).val (zeroIndex d m) p =
        ∫ y, (∑' q, kernelJet (K q a b) (zeroIndex d m) p y) * (f b).val (y.2, y.1) ∂μ :=
      ae_all_iff.mpr (fun b => hjet a b (f b) (zeroIndex d m))
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun b => (T a b (ofTest 0 μ (f b))).val (zeroIndex d m)), hj] with p hp hjp
    rw [hp]
    simp_rw [hjp]
    rw [sum_summedJointKernel_zerothJet_physical J backward S A mi mo χA χo ψ c
      hSc hS hA hi ho hg hc hg0 hψ hsψ μ hJ C hs hb C₀ hs₀ hb₀ f a p]
    exact congrFun (summedJointKernel_test_cutoff backward S A mi mo χA χo c
      hSc hS hA hi ho.continuous hg hg0 (fun k => (hc k).continuous) hcb hclim B hbmo
      t ht hmt C₀ hs₀ hb₀ (physicalTestField J f) (contDiff_physicalTestField J f)
      ((contDiff_physicalTestField J f).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_physicalTestField J f)) ψ hplateau (J (p.2, p.1))) a
  refine ⟨T, hn, htest, hjet, hident, ?_⟩
  intro f a
  filter_upwards [hident f a] with p hp
  rw [hp]
  have hfi : Integrable (physicalTestField J f) :=
    (contDiff_physicalTestField J f).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_physicalTestField J f)
  cases backward
  · exact (tendsto_pi_nhds.mp (tendsto_forward_composition_cutoffs S A mi mo χA χo
      hSc hA.continuous hi.continuous ho.continuous (fun j => (hg j).continuous)
      (fun k => (hc k).continuous) c C₀ hs₀ hb₀ (physicalTestField J f)
      (contDiff_physicalTestField J f).continuous hfi (J (p.2, p.1)))) a
  · exact (tendsto_pi_nhds.mp (tendsto_reverse_composition_cutoffs S A mi mo χA χo
      hSc hA.continuous hi.continuous ho.continuous (fun j => (hg j).continuous)
      (fun k => (hc k).continuous) c C₀ hs₀ hb₀ (physicalTestField J f)
      (contDiff_physicalTestField J f).continuous hfi (J (p.2, p.1)))) a

end Identification
end JanetCartan.FiniteChain.Graph.KernelLimits
