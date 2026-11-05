module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CutoffSums
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.TestOutputs

/-!
# Common support after summing the output regularization

For `app:ch_regular:eq:chain-tail`, summable joint kernel bounds allow the
output-frequency sum to be performed first. Fourier inversion identifies each
row with the literal leakage of a compact-frequency graph. All these rows have
one common output carrier, so their sum has that carrier too. No compact output
support is asserted for an individual joint regularization.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- One physical carrier for every graph cutoff, in either orientation, after
recovering the identity (`app:ch_regular:eq:chain-tail`). -/
def leakageOutputCarrier (backward : Bool) (s : Set (Euclidean n × Euclidean n))
    (t : Set (Euclidean n)) : Set (Euclidean n) :=
  (if backward then Prod.snd '' s else Prod.fst '' s) ∪ t

/-- Compactness of the common recovered output carrier
(`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_leakageOutputCarrier (backward : Bool)
    {s : Set (Euclidean n × Euclidean n)} {t : Set (Euclidean n)}
    (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (leakageOutputCarrier backward s t) := by
  cases backward <;> exact (hs.image (by fun_prop)).union ht

/-- Vanishing outside the same physical carrier for any graph-frequency
cutoff. The amplitude's two positions remain in their literal order
(`app:ch_regular:eq:chain-tail`). -/
theorem regularizedLeakage_zero_off_output
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo χ : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (t : Set (Euclidean n)) (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (f : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (hx : x ∉ leakageOutputCarrier backward c.amplitudeBase t) :
    (if backward then reverseLeakage S (fun u z ξ => (χ ξ : ℂ) • A u z ξ) 1 mi mo f x
      else forwardLeakage S (fun u z ξ => (χ ξ : ℂ) • A u z ξ) 1 mi mo f x) = 0 := by
  have hxt : x ∉ t := fun h => hx (Or.inr h)
  have hlo (g : Euclidean n → Fin r → ℂ) : leftLocalizer 1 mo g x = 0 :=
    leftLocalizer_zero_off_output 1 mo g t hmt x hxt
  cases backward
  · have hz (z ξ : Euclidean n) : A x z ξ = 0 :=
      c.amplitude_zero x z ξ (fun h => hx (Or.inl ⟨(x,z), h, rfl⟩))
    simp [forwardLeakage, hlo, graphOperator, hz]
  · have hu (u ξ : Euclidean n) : A u x ξ = 0 :=
      c.amplitude_zero u x ξ (fun h => hx (Or.inl ⟨(u,x), h, rfl⟩))
    simp [reverseLeakage, hlo, reverseGraphOperator, hu]

/-- Finite sums in only the output frequency preserve all primitive carriers
(`app:ch_regular:eq:joint-kernel-phase`). -/
def RegularizedCarriers.outputSum
    {A : FullAmplitude n r} {mi : LocalizerSymbol n} {χA : Euclidean n → ℝ}
    {χo : ℕ → Euclidean n → ℝ}
    (c : ∀ k, RegularizedCarriers A mi χA (χo k)) (s : Finset ℕ) :
    RegularizedCarriers A mi χA (fun ζ => ∑ k ∈ s, χo k ζ) :=
  { c 0 with
    compact_outputCutoff := by
      convert HasCompactSupport.finset_sum (fun k (_ : k ∈ s) => (c k).compact_outputCutoff) using 1
      ext ζ
      simp }

section Reconstruction
variable (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
  (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
  (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
  (hSc : Continuous (Function.uncurry S))
  (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
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

include c hSc hS hA hi ho hg hg0 hc hcb hclim hbmo ht hmt hs hb hf hfi

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
  have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, ∫ y,
      (regularizedJointKernel backward S A mi mo (χA j) (χo k) x y).mulVec (f y)) atTop
      (𝓝 (if backward then reverseLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x
        else forwardLeakage S (fun u z ξ => (χA j ξ : ℂ) • A u z ξ) 1 mi mo f x)) := by
    cases backward
    · simpa only [he, Bool.false_eq_true, ite_false, ite_true] using (tendsto_forwardJointKernel_outputCutoff S A mi mo (χA j)
        (fun N ζ => ∑ k ∈ Finset.range N, χo k ζ)
        (fun N => RegularizedCarriers.outputSum (c j) (Finset.range N))
        hSc hS hA hi ho (hg j) (hg0 j)
        (fun N => continuous_finsetSum _ (fun k _ => hc k)) hcb hclim
        B hbmo t ht hmt f hf).1 x
    · simpa only [he, Bool.false_eq_true, ite_false, ite_true] using (tendsto_reverseJointKernel_outputCutoff S A mi mo (χA j)
        (fun N ζ => ∑ k ∈ Finset.range N, χo k ζ)
        (fun N => RegularizedCarriers.outputSum (c j) (Finset.range N))
        hSc hS hA hi ho (hg j) (hg0 j)
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
      (fun j => hasSum_jointKernel_outputRow backward S A mi mo χA χo c hSc hS hA hi ho
        hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi j x)

/-- The summed action vanishes off a fixed physical carrier, even though the
finite output-frequency regularizations do not. This justifies a fixed smooth
output cutoff before applying `Retarded.KernelSobolev`
(`app:ch_regular:eq:chain-tail`). -/
theorem summedJointKernel_test_zero_off_output (x : Euclidean n)
    (hx : x ∉ leakageOutputCarrier backward (c 0 0).amplitudeBase t) :
    (∫ y, (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) x y).mulVec (f y)) = 0 := by
  have hsum := hasSum_regularizedLeakage backward S A mi mo χA χo c hSc hS hA hi ho
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
    (summedJointKernel_test_zero_off_output backward S A mi mo χA χo c hSc hS hA hi ho
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
  · rw [summedJointKernel_test_zero_off_output backward S A mi mo χA χo c hSc hS hA hi ho
      hg hg0 hc hcb hclim B hbmo t ht hmt C hs hb f hf hfi x hx, smul_zero]

end Reconstruction
end JanetCartan.FiniteChain.Graph.KernelLimits
