module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits

/-!
# Recovering the identity for phases defined on conic charts

A smooth extension on each compact graph-frequency support suffices for the
existing Fourier inversion argument. Equality on the full amplitude support
keeps the original phase in the actual leakage and in every limiting action.
This closes the support step of `app:ch_regular:eq:chain-tail` without requiring
the original phase to be smooth outside its chart.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.ConicLimits
open FourierIntegral KernelLimits
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Replacing the phase only on a graph-frequency piece preserves either
literal orientation, including both amplitude positions
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularized_orientedGraph_phase_congr (backward : Bool)
    (S S' : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (χ : Euclidean n → ℝ)
    (he : ∀ u z ξ, A u z ξ ≠ 0 → χ ξ ≠ 0 → S' u ξ = S u ξ)
    (f : Euclidean n → Fin r → ℂ) :
    (if backward then reverseGraphOperator else graphOperator) S'
      (fun u z ξ => (χ ξ : ℂ) • A u z ξ) f =
    (if backward then reverseGraphOperator else graphOperator) S
      (fun u z ξ => (χ ξ : ℂ) • A u z ξ) f := by
  cases backward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> funext x
  · unfold graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases ha : A x z ξ = 0
    · simp [ha]
    by_cases hc : χ ξ = 0
    · simp [hc]
    simp only [graphOscillation, he x z ξ ha hc]
  · unfold reverseGraphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases ha : A u x ξ = 0
    · simp [ha]
    by_cases hc : χ ξ = 0
    · simp [hc]
    simp only [graphOscillation, he u x ξ ha hc]

section Reconstruction
variable (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
  (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
  (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
  (hSc : Continuous (Function.uncurry S))
  (Sext : ℕ → Euclidean n → Euclidean n → ℝ)
  (hsExt : ∀ j, ContDiff ℝ ∞ (Function.uncurry (Sext j)))
  (hext : ∀ j u z ξ, A u z ξ ≠ 0 → χA j ξ ≠ 0 → Sext j u ξ = S u ξ)
  (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
    A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
  (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
  (hc : ∀ k, Continuous (χo k))
  (hcb : ∀ N ξ, |∑ k ∈ Finset.range N, χo k ξ| ≤ 1)
  (hclim : ∀ ξ, Tendsto (fun N => ∑ k ∈ Finset.range N, χo k ξ) atTop (𝓝 1))
  (B : ℝ) (hbmo : ∀ x ξ, |mo (x,ξ)| ≤ B)
  (t : Set (Euclidean n)) (ht : IsCompact t) (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
  (C : ℕ × ℕ → ℝ) (hs : Summable C)
  (hb : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo (χA j) (χo k) x y‖ ≤ C (j,k))
  (f : Euclidean n → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) (hfi : Integrable f)

include c hSc Sext hsExt hext hA hi ho hg hg0 hc hcb hclim hbmo ht hmt hs hb hf hfi

/-- A full output-frequency row sums to the literal leakage, including the
identity. Only the matrix-kernel majorant is conditional on the estimates
producer; the Fourier reconstruction is proved (`app:ch_regular:eq:chain-tail`). -/
theorem hasSum_jointKernel_outputRow (j : ℕ) (x : Euclidean n) :
    HasSum (fun k => ∫ y,
      (regularizedJointKernel backward S A mi mo (χA j) (χo k) x y).mulVec (f y))
      (if backward then reverseLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
        else forwardLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x) := by
  have hrow := hasSum_regularizedJointKernel_test backward S A mi mo (fun _ => χA j) χo
    hSc hA.continuous hi.continuous ho (fun _ => (hg j).continuous) hc
    (fun k => C (j,k)) (hs.prod_factor j) (fun k => hb j k) f hfi x
  have he (N : ℕ) :
      (∫ y, (regularizedJointKernel backward S A mi mo (χA j)
        (fun ζ => ∑ k ∈ Finset.range N, χo k ζ) x y).mulVec (f y)) =
      ∑ k ∈ Finset.range N, ∫ y,
        (regularizedJointKernel backward S A mi mo (χA j) (χo k) x y).mulVec (f y) := by
    simpa using regularizedJointKernel_test_finset_cutoffs {j} (Finset.range N)
      backward S A mi mo χA χo hSc hA.continuous hi.continuous ho
      (fun j => (hg j).continuous) hc c f hf.continuous x
  have heK (χ : Euclidean n → ℝ) (x y : Euclidean n) :
      regularizedJointKernel backward S A mi mo (χA j) χ x y =
        regularizedJointKernel backward (Sext j) A mi mo (χA j) χ x y :=
    PhysicalShells.Noncomparable.physicalJointKernel_congr_phase backward S (Sext j) A
      mi mo (χA j) χ x y (fun u z ξ ha hg => (hext j u z ξ ha hg).symm)
  have heL : (if backward then
      reverseLeakage (Sext j) (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
      else forwardLeakage (Sext j) (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x) =
      (if backward then
      reverseLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
      else forwardLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x) := by
    have heG := regularized_orientedGraph_phase_congr backward S (Sext j) A (χA j)
      (hext j) (rightLocalizer 1 mi f)
    cases backward <;> simp only [Bool.false_eq_true, ite_false, ite_true] at heG ⊢
    · simp only [forwardLeakage, heG]
    · simp only [reverseLeakage, heG]
  have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, ∫ y,
      (regularizedJointKernel backward S A mi mo (χA j) (χo k) x y).mulVec (f y)) atTop
      (𝓝 (if backward then reverseLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
        else forwardLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x)) := by
    simp_rw [← he, heK]
    rw [← heL]
    cases backward
    · exact (tendsto_forwardJointKernel_outputCutoff (Sext j) A mi mo (χA j)
        (fun N ζ => ∑ k ∈ Finset.range N, χo k ζ)
        (fun N => RegularizedCarriers.outputSum (c j) (Finset.range N))
        (hsExt j).continuous (fun _ _ _ => (hsExt j).contDiffAt) hA hi ho (hg j) (hg0 j)
        (fun N => continuous_finsetSum _ (fun k _ => hc k)) hcb hclim
        B hbmo t ht hmt f hf).1 x
    · exact (tendsto_reverseJointKernel_outputCutoff (Sext j) A mi mo (χA j)
        (fun N ζ => ∑ k ∈ Finset.range N, χo k ζ)
        (fun N => RegularizedCarriers.outputSum (c j) (Finset.range N))
        (hsExt j).continuous (fun _ _ _ => (hsExt j).contDiffAt) hA hi ho (hg j) (hg0 j)
        (fun N => continuous_finsetSum _ (fun k _ => hc k)) hcb hclim
        B hbmo t ht hmt f hf).1 x
  exact (tendsto_nhds_unique hrow.tendsto_sum_nat hlim) ▸ hrow

/-- The genuine test-input limit is also the sum of the recovered compact
frequency leakages. This exchanges the two regularizations by absolute
summability, without using a raw nonintegrable Bochner graph operator
(`app:ch_regular:eq:chain-tail`). -/
theorem hasSum_regularizedLeakage (x : Euclidean n) :
    HasSum (fun j => if backward then
      reverseLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
      else forwardLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x)
      (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
        (χA p.1) (χo p.2) x y).mulVec (f y)) := by
  exact (hasSum_regularizedJointKernel_test backward S A mi mo
    (fun p : ℕ × ℕ => χA p.1) (fun p : ℕ × ℕ => χo p.2)
    hSc hA.continuous hi.continuous ho (fun p => (hg p.1).continuous) (fun p => hc p.2)
    C hs (fun p => hb p.1 p.2) f hfi x).prod_fiberwise
      (fun j => hasSum_jointKernel_outputRow backward S A mi mo χA χo c hSc Sext hsExt hext hA hi ho
        hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi j x)

/-- The summed action vanishes off a fixed physical carrier, even though the
finite output-frequency regularizations do not. This justifies a fixed smooth
output cutoff before applying `Retarded.KernelSobolev`
(`app:ch_regular:eq:chain-tail`). -/
theorem summedJointKernel_test_zero_off_output (x : Euclidean n)
    (hx : x ∉ leakageOutputCarrier backward (c 0 0).amplitudeBase t) :
    (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) x y).mulVec (f y)) = 0 := by
  have hsum := hasSum_regularizedLeakage backward S A mi mo χA χo c hSc Sext hsExt hext hA hi ho
    hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi x
  have hz (j : ℕ) := regularizedLeakage_zero_off_output backward S A mi mo
    (χA 0) (χo 0) (χA j) (c 0 0) t hmt f x hx
  simpa only [hz, tsum_zero] using hsum.tsum_eq.symm

/-- Compact support of the genuine summed action on smooth integrable inputs;
compactness is established after recovering the identity, as required in
`app:ch_regular:eq:chain-tail`. -/
theorem summedJointKernel_test_hasCompactSupport :
    HasCompactSupport (fun x => ∫ y, (∑' p : ℕ × ℕ,
      regularizedJointKernel backward S A mi mo (χA p.1) (χo p.2) x y).mulVec (f y)) :=
  HasCompactSupport.intro
    (isCompact_leakageOutputCarrier backward (c 0 0).compact_amplitudeBase ht)
    (summedJointKernel_test_zero_off_output backward S A mi mo χA χo c hSc Sext hsExt hext hA hi ho
      hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi)

/-- A fixed output cutoff equal to one on the recovered carrier preserves the
entire limiting action. This is the support step needed by the conditional
Sobolev extension, not a deletion of the identity contribution
(`app:ch_regular:eq:chain-tail`). -/
theorem summedJointKernel_test_cutoff (ψ : Euclidean n → ℝ)
    (hψ : ∀ x ∈ leakageOutputCarrier backward (c 0 0).amplitudeBase t, ψ x = 1)
    (x : Euclidean n) :
    (ψ x : ℂ) • (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) x y).mulVec (f y)) =
    ∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) x y).mulVec (f y) := by
  by_cases hx : x ∈ leakageOutputCarrier backward (c 0 0).amplitudeBase t
  · simp [hψ x hx]
  · rw [summedJointKernel_test_zero_off_output backward S A mi mo χA χo c hSc Sext hsExt hext hA hi ho
      hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi x hx, smul_zero]

end Reconstruction
end JanetCartan.FiniteChain.Graph.ConicLimits
