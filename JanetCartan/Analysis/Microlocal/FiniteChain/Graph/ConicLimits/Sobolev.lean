module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.ConicLimits.Identification
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.CartesianJets

/-!
# Uniform Sobolev assembly for original conic phases

The phase extensions enter only the Fourier inversion step; all kernel jets,
operators and quantitative bounds retain the original phase. The physical-shell
producer supplies the kernel smoothness and estimates, and compact conic support
supplies the extensions (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.ConicLimits
open FourierIntegral KernelLimits CartesianJets
open Retarded.KernelSobolev AmplitudeBound
open JanetCartan.RetardedSobolev.Spaces

variable {n r d m : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Assemble the graph, literal reverse-graph, weighted-inverse, and diagonal
factor estimate from the physical shell derivative grades
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`).

`B` bounds the evaluated physical output derivatives of every independent
graph/output cutoff pair, while `C₀` bounds the un-differentiated kernels.
These are explicit conditional kernel estimates: the first
is converted to Cartesian Sobolev jets by
`CartesianJets.summable_regularizedJointKernel_jet_majorant`, and the second
is used only for the genuine regularization limit.  The resulting operator is
the summed literal action, with the fixed `r*r` Frobenius channel factor and
the support factor of `ConicLimits.exists_jointKernel_physical_extension`.
The forward and reverse orientations are selected by `backward`; choosing the
weighted inverse amplitude is handled by `Graph.Basic`'s exact identity.
-/
theorem exists_graph_factor_sobolev_bound
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ) (ψ : Euclidean n → ℝ)
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (hSc : Continuous (Function.uncurry S))
    (hK : ∀ j k, ContDiff ℝ ∞ (Function.uncurry
      (regularizedJointKernel backward S A mi mo (χA j) (χo k))))
    (Sext : ℕ → Euclidean n → Euclidean n → ℝ)
    (hsExt : ∀ j, ContDiff ℝ ∞ (Function.uncurry (Sext j)))
    (hext : ∀ j u z ξ, A u z ξ ≠ 0 → χA j ξ ≠ 0 → Sext j u ξ = S u ξ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hc : ∀ k, ContDiff ℝ ∞ (χo k))
    (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (μ ν : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hJ : MeasurePreserving (graphInputCoordinates J) μ volume)
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ α, 0 ≤ B l α)
    (hsB : ∀ l ≤ m, Summable (B l))
    (hbB : ∀ j k x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m,
      ∀ v : Fin l → Euclidean n, (∀ a, ‖v a‖ ≤ 1) →
        ‖iteratedFDeriv ℝ l (fun z =>
          regularizedJointKernel backward S A mi mo (χA j) (χo k) z y) x v‖ ≤ B l (j, k))
    (C₀ : ℕ × ℕ → ℝ) (hsC₀ : Summable C₀)
    (hb₀ : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo
      (χA j) (χo k) x y‖ ≤ C₀ (j, k))
    (hcb : ∀ N ξ, |∑ k ∈ Finset.range N, χo k ξ| ≤ 1)
    (hclim : ∀ ξ, Tendsto (fun N => ∑ k ∈ Finset.range N, χo k ξ) atTop (𝓝 1))
    (Bmo : ℝ) (hbmo : ∀ x ξ, |mo (x, ξ)| ≤ Bmo)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (hplateau : ∀ x ∈ leakageOutputCarrier backward (c 0 0).amplitudeBase t,
      ψ x = 1) :
    ∃ T : Fin r → Fin r → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖matrixOperator T‖ ≤ (r : ℝ) * r *
        ((∑' α, jetMajorant J (cutoffDerivativeProfile hψ hsψ)
          (fun l => B l α) m) *
          compactSupportFactor μ ν
            ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹'
              RegularizedCarriers.inputBase (c 0 0))
            (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) ∧
      (∀ (a b : Fin r) (f : Test d), HasSum (fun q : ℕ × ℕ => ofTest m ν
          (kernelIntegralLinear
            (supportedJointKernelEntry J backward S A mi mo (χA q.1) (χo q.2) ψ
              (RegularizedCarriers.commonBases c q.1 q.2)
              (hK q.1 q.2) hψ hsψ a b) μ f))
        (T a b (ofTest 0 μ f))) ∧
      (∀ (a b : Fin r) (f : Test d) (i : JetIndex d m),
        (T a b (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p => ∫ y, (∑' q : ℕ × ℕ, kernelJet
          (supportedJointKernelEntry J backward S A mi mo (χA q.1) (χo q.2) ψ
            (RegularizedCarriers.commonBases c q.1 q.2)
            (hK q.1 q.2) hψ hsψ a b) i p y) *
          f.val (y.2, y.1) ∂μ) ∧
      (∀ (f : Fin r → Test d) (a : Fin r),
        ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
          (zeroIndex d m) =ᵐ[ν] fun p =>
            (∫ y, (∑' q : ℕ × ℕ,
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
  let C := fun α : ℕ × ℕ =>
    jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l => B l α) m
  have hmaj := CartesianJets.summable_cutMatrixEntry_jet_majorant (m := m) J hψ hsψ
    (fun α : ℕ × ℕ => regularizedJointKernel backward S A mi mo (χA α.1) (χo α.2))
    (fun α => hK α.1 α.2) B hB hsB
    (fun α x hx y l hl v hv => hbB α.1 α.2 x hx y l hl v hv)
  dsimp [C] at hmaj
  obtain ⟨hC, hsC, _, hbC⟩ := hmaj
  obtain ⟨T, hnorm, hsum, hjet, hphys, hlim⟩ :=
    ConicLimits.exists_jointKernel_physical_extension
      J backward S A mi mo χA χo ψ c hSc hK Sext hsExt hext hA hi ho hg hc hg0 hψ hsψ μ ν hJ
      C hC hsC (fun j k => hbC (j, k)) C₀ hsC₀ hb₀ hcb hclim Bmo hbmo t ht hmt hplateau
  exact ⟨T, hnorm, hsum, hjet, hphys, hlim⟩

/-- The operator in the preceding assembly is independent of the requested
accuracy.  If the physical bridge supplies, for each `q`, derivative sums with
the graded bound
`D q l * ρ^(l+a) * L^b * (L/ρ)^q * P`, then one fixed summed graph operator
satisfies the corresponding `L² → Hᵐ` estimate for every `q`.  The fixed
coordinate/cutoff loss is the finite `jetMajorant`; the powers of `ρ`, `L`,
and the full accuracy factor are untouched.  This is the graph form of
`app:ch_regular:eq:chain-tail`; the reverse orientation, weighted inverse,
and diagonal specialization use the same theorem after their exact phase and
amplitude identifications.
-/
theorem exists_graph_factor_sobolev_bound_uniform
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ) (ψ : Euclidean n → ℝ)
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (hSc : Continuous (Function.uncurry S))
    (hK : ∀ j k, ContDiff ℝ ∞ (Function.uncurry
      (regularizedJointKernel backward S A mi mo (χA j) (χo k))))
    (Sext : ℕ → Euclidean n → Euclidean n → ℝ)
    (hsExt : ∀ j, ContDiff ℝ ∞ (Function.uncurry (Sext j)))
    (hext : ∀ j u z ξ, A u z ξ ≠ 0 → χA j ξ ≠ 0 → Sext j u ξ = S u ξ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hc : ∀ k, ContDiff ℝ ∞ (χo k))
    (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (μ ν : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hJ : MeasurePreserving (graphInputCoordinates J) μ volume)
    (B : ℕ → ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ q, ∀ l ≤ m, ∀ α, 0 ≤ B q l α)
    (hsB : ∀ q, ∀ l ≤ m, Summable (B q l))
    (hbB : ∀ q j k x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m,
      ∀ v : Fin l → Euclidean n, (∀ a, ‖v a‖ ≤ 1) →
        ‖iteratedFDeriv ℝ l (fun z =>
          regularizedJointKernel backward S A mi mo (χA j) (χo k) z y) x v‖ ≤
          B q l (j, k))
    (C₀ : ℕ × ℕ → ℝ) (hsC₀ : Summable C₀)
    (hb₀ : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo
      (χA j) (χo k) x y‖ ≤ C₀ (j, k))
    (hcb : ∀ N ξ, |∑ k ∈ Finset.range N, χo k ξ| ≤ 1)
    (hclim : ∀ ξ, Tendsto (fun N => ∑ k ∈ Finset.range N, χo k ξ) atTop (𝓝 1))
    (Bmo : ℝ) (hbmo : ∀ x ξ, |mo (x, ξ)| ≤ Bmo)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (hplateau : ∀ x ∈ leakageOutputCarrier backward (c 0 0).amplitudeBase t,
      ψ x = 1)
    {D : ℕ → ℕ → ℝ} (hD : ∀ q, ∀ l ≤ m, 0 ≤ D q l)
    {ρ L P : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (aExp : ℝ) (bExp : ℕ)
    (hgraded : ∀ q, ∀ l ≤ m, (∑' α, B q l α) ≤
      D q l * ρ ^ ((l : ℝ) + aExp) * L ^ bExp * (L / ρ) ^ q * P) :
    ∃ T : Fin r → Fin r → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      (∀ q, ‖matrixOperator T‖ ≤
        (r : ℝ) * r *
          (jetMajorant J (cutoffDerivativeProfile hψ hsψ) (D q) m *
            ρ ^ ((m : ℝ) + aExp) * L ^ bExp * (L / ρ) ^ q * P) *
          compactSupportFactor μ ν
            ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹'
              RegularizedCarriers.inputBase (c 0 0))
            (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) ∧
      (∀ (a b : Fin r) (f : Test d), HasSum (fun q : ℕ × ℕ => ofTest m ν
          (kernelIntegralLinear
            (supportedJointKernelEntry J backward S A mi mo (χA q.1) (χo q.2) ψ
              (RegularizedCarriers.commonBases c q.1 q.2)
              (hK q.1 q.2) hψ hsψ a b) μ f))
        (T a b (ofTest 0 μ f))) ∧
      (∀ (a b : Fin r) (f : Test d) (i : JetIndex d m),
        (T a b (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p => ∫ y, (∑' q : ℕ × ℕ, kernelJet
          (supportedJointKernelEntry J backward S A mi mo (χA q.1) (χo q.2) ψ
            (RegularizedCarriers.commonBases c q.1 q.2)
            (hK q.1 q.2) hψ hsψ a b) i p y) *
          f.val (y.2, y.1) ∂μ) ∧
      (∀ (f : Fin r → Test d) (a : Fin r),
        ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
          (zeroIndex d m) =ᵐ[ν] fun p =>
            (∫ y, (∑' q : ℕ × ℕ,
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
  let C := fun (accuracy : ℕ) (α : ℕ × ℕ) =>
    jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l => B accuracy l α) m
  have hmaj q := CartesianJets.summable_cutMatrixEntry_jet_majorant (m := m) J hψ hsψ
    (fun α : ℕ × ℕ => regularizedJointKernel backward S A mi mo (χA α.1) (χo α.2))
    (fun α => hK α.1 α.2) (fun l α => B q l α) (hB q) (hsB q)
    (fun α x hx y l hl v hv => hbB q α.1 α.2 x hx y l hl v hv)
  have hC q : ∀ α, 0 ≤ C q α := by
    dsimp [C]
    exact (hmaj q).1
  have hsC q : Summable (C q) := by
    dsimp [C]
    exact (hmaj q).2.1
  have hsumC q : (∑' α, C q α) =
      jetMajorant J (cutoffDerivativeProfile hψ hsψ)
        (fun l => ∑' α, B q l α) m := by
    dsimp [C]
    exact (hmaj q).2.2.1
  have hbC q : ∀ j k (a b : Fin r) (i : JetIndex d m) p
      (y : (Fin d → ℝ) × ℝ),
      ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
        (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C q (j, k) := by
    intro j k a b i p y
    exact (hmaj q).2.2.2 (j, k) a b i p y
  have hex q := exists_graph_factor_sobolev_bound
    (m := m) J backward S A mi mo χA χo ψ c hSc hK Sext hsExt hext hA hi ho hg hc hg0 hψ hsψ μ ν hJ
    (fun l α => B q l α) (hB q) (hsB q) (hbB q) C₀ hsC₀ hb₀ hcb hclim Bmo hbmo t ht hmt hplateau
  choose T hnorm hsum hjet hphys hlim using hex
  have hT_eq (q : ℕ) (a b : Fin r) : T q a b = T 0 a b := by
    exact shell_extension_unique
      (fun p : ℕ × ℕ => supportedJointKernelEntry J backward S A mi mo
        (χA p.1) (χo p.2) ψ (RegularizedCarriers.commonBases c p.1 p.2)
        (hK p.1 p.2) hψ hsψ a b)
      μ ν (T q a b) (T 0 a b) (hsum q a b) (hsum 0 a b)
  let T₀ := T 0
  refine ⟨T₀, ?_, hsum 0, hjet 0, hphys 0, hlim 0⟩
  intro q
  have hTfun : T q = T₀ := by
    funext a b
    exact hT_eq q a b
  rw [← hTfun]
  have hsumBound := CartesianJets.tsum_jetMajorant_le_grades
    (m := m) J (cutoffDerivativeProfile_nonneg hψ hsψ)
    (hD q) (fun l α => B q l α) (hsB q) hρ hL hP aExp bExp q
    (hgraded q)
  have hsumBound' :
      jetMajorant J (cutoffDerivativeProfile hψ hsψ)
          (fun l => ∑' α, B q l α) m ≤
        jetMajorant J (cutoffDerivativeProfile hψ hsψ) (D q) m *
          ρ ^ ((m : ℝ) + aExp) * L ^ bExp * (L / ρ) ^ q * P := by
    rw [← hsumC q]
    exact hsumBound
  have hsupport : 0 ≤ compactSupportFactor μ ν
      ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹'
        RegularizedCarriers.inputBase (c 0 0))
      (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ)) := compactSupportFactor_nonneg _ _ _ _
  have hrr : 0 ≤ (r : ℝ) * r := by positivity
  calc
    ‖matrixOperator (T q)‖ ≤ (r : ℝ) * r *
        ((∑' α, C q α) *
          compactSupportFactor μ ν
            ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹'
              RegularizedCarriers.inputBase (c 0 0))
            (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) := hnorm q
    _ ≤ (r : ℝ) * r *
        ((jetMajorant J (cutoffDerivativeProfile hψ hsψ) (D q) m *
          ρ ^ ((m : ℝ) + aExp) * L ^ bExp * (L / ρ) ^ q * P) *
          compactSupportFactor μ ν
            ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹'
              RegularizedCarriers.inputBase (c 0 0))
            (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) := by
      rw [hsumC q]
      gcongr
    _ = _ := by ring

end JanetCartan.FiniteChain.Graph.ConicLimits
