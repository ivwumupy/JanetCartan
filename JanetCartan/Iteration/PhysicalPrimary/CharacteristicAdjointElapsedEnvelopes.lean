module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointOperatorRealization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Primitive

/-!
# The original inactive literal-adjoint elapsed operator

The actual complete kernel estimate is integrated over the original elapsed
interval. The retained graph certificates supply both measurability and the
canonical strong limits. Its bounded integral is identified with the supplied
selected operator, so no complementary operator or Fourier-mask factorization
is substituted. Consumer: the inactive parameter piece in the finite measured
residual words (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds ResponseTransfer Pseudodifferential
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open ResponseTransfer.RetainedFactors
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral.LowBounds.FrequencyCutoff
variable {p d r : ℕ} {I : Type}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Every carrier derivative of the SAME inactive selected elapsed operator
has arbitrary Fourier Sobolev precision. The quantitative estimate is derived
from the original phase/amplitude jets and transported-momentum source gap; the retained
regularizations identify the operator and establish time measurability.
Their possibly history-dependent norm bound does not enter the tail constants
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem inactive_adjoint_elapsed_operator_sobolev
    {V P₀ : Set P} (hV : IsOpen V) (hP₀ : IsClosed P₀) {X₀ S : Set E}
    (hX₀ : IsCompact X₀) [CompactSpace X₀] (hS : IsCompact S)
    {U : Set E} (hU : IsOpen U) (hSU : S ⊆ U) (hXU : X₀ ⊆ U)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    {gap B₀ Mfreq : ℝ} (hgap : 0 < gap) (hMfreq : 0 ≤ Mfreq)
    (Pφ PΘ BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hPφ : ∀ k, 0 ≤ Pφ k) (hPΘ : ∀ k, 0 ≤ PΘ k)
    (hBΨ : ∀ k, 0 ≤ BΨ k) (hBφ : ∀ k, 0 ≤ Bφ k)
    (hO : ∀ k, 0 ≤ O k) (hT : ∀ k, 0 ≤ T k) (hB : ∀ k, 0 ≤ B k) (hMβ : 0 ≤ Mβ)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d) (b : I → TwoTimeAmplitude d r)
    (χout χsource β : I → E → ℂ) (φ : I → P → E → ℝ) (a : I → P → E → F)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
    (hparam : ∀ i c, c ∉ P₀ → ∀ y, a i c y = 0)
    (hmask : ∀ i, tsupport (χout i) ∪ tsupport (χsource i) ⊆ X₀)
    (ho : ∀ i, ContDiff ℝ ∞ (χout i)) (hs : ∀ i, ContDiff ℝ ∞ (χsource i))
    (hβsmooth : ∀ i, ContDiff ℝ ∞ (β i)) (hβ : ∀ i ξ, ‖β i ξ‖ ≤ Mβ)
    (hΨ : ∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i)))
    (hb : ∀ i, ContDiff ℝ ∞ (jointAmplitude (b i)))
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hΨb : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointPhase (Ψ i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        BΨ k * (1 + ‖ξ‖) * L i ^ k)
    (hφb : ∀ i k c, c ∈ V → ∀ y ∈ S ∪ X₀,
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) (c, y)‖ ≤ Bφ k * L i ^ k)
    (hbb : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointAmplitude (b i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        B k * L i ^ k)
    (hout : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χout i) y‖ ≤ O k)
    (hsource : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χsource i) y‖ ≤ T k)
    (hmem : ∀ i c (hc : c ∈ V) l (w : Fin l → P),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)))
    (hsob : ∀ i c (hc : c ∈ V) l (w : Fin l → P),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤
            C l s * A₀ i * K i ^ (s + l))
    (hupper : ∀ i c, c ∈ V → ∀ y ∈ U, ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hupperΘ : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ U,
      ‖fderiv ℝ (fun z ↦ elapsedPhase (Ψ i) t z ξ) y‖ ≤ Mfreq*‖ξ‖)
    (hfrequency : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ c ∈ V, c ∈ P₀ → ∀ y ∈ U,
      gap*(lam i+‖ξ‖) ≤ ‖lam i • fderiv ℝ (φ i c) y-fderiv ℝ (fun z ↦ elapsedPhase (Ψ i) t z ξ) y‖)
    (hsourceφ : ∀ i c, c ∈ V → ∀ y ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (φ i c) y‖ ≤ Pφ k * L i ^ k)
    (hsourceΘ : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (fun z ↦ elapsedPhase (Ψ i) t z ξ) y‖ ≤ PΘ k*‖ξ‖*L i^k)
    (Creg : I → ℝ)
    (hgraphs : ∀ i, CappedGraphRealizations Δ (Ψ i) (b i)
      (χout i) (χsource i) (β i) (Creg i))
    (Op : I → H →L[ℂ] H)
    (hOp : ∀ i u, Op i u = ∫ t in Icc 0 Δ, (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint u)
    (u : I → P → H) (hu : ∀ i c, c ∈ V → u i c =ᵐ[volume] a i c) :
    let out := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
      ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (Op i) (u i c)
    (∀ i, ContDiffOn ℝ ∞ (out i) V) ∧
      ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ Csob : ℝ, 0 ≤ Csob ∧
        ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
          MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧
          vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (out i) c v) ≤
            Csob * A₀ i * lam i ^ (-Q) := by
  dsimp only
  let R := fun i t ↦ elapsedAnnularRemainder hX₀ true true (Ψ i) (b i)
    (χout i) (χsource i) (β i) 0 (φ i) t (lam i) (a i)
  have hp := inactive_adjoint_elapsed_kernel_sobolev (I := I × Icc (0 : ℝ) Δ)
    hV hP₀ hX₀ hS hU hU hSU hXU hΔ hν hν1 hgap hMfreq
    Pφ PΘ BΨ Bφ O T B C Mβ hPφ hPΘ hBΨ hBφ hO hT hB hMβ
    (fun j ↦ lam j.1) (fun j ↦ L j.1) (fun j ↦ K j.1) (fun j ↦ j.2.val)
    (fun j ↦ A₀ j.1) (fun j ↦ hlam j.1) (fun j ↦ hL j.1) (fun j ↦ hLK j.1)
    (fun j ↦ hscale j.1) (fun j ↦ j.2.property) (fun j ↦ hA₀ j.1)
    (fun j ↦ Ψ j.1) (fun j ↦ b j.1) (fun j ↦ χout j.1) (fun j ↦ χsource j.1)
    (fun j ↦ β j.1) (fun j ↦ φ j.1) (fun j ↦ a j.1)
    (fun j ↦ ha j.1) (fun j ↦ has j.1) (fun j ↦ hparam j.1) (fun j ↦ hmask j.1)
    (fun j ↦ ho j.1) (fun j ↦ hs j.1) (fun j ↦ hβsmooth j.1) (fun j ↦ hβ j.1)
    (fun _ ↦ univ) (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ isOpen_univ)
    (fun j ↦ (hΨ j.1).contDiffOn) (fun j ↦ hb j.1)
    (fun _ _ _ _ _ ↦ mem_univ _) (fun _ _ _ _ _ ↦ mem_univ _)
    (fun j ↦ (hφ j.1).contDiffOn)
    (fun j ↦ hΨb j.1 j.2 j.2.property) (fun j ↦ hφb j.1)
    (fun j ↦ hbb j.1 j.2 j.2.property) (fun j ↦ hout j.1) (fun j ↦ hsource j.1)
    (fun j ↦ hmem j.1) (fun j ↦ hsob j.1) (fun j ↦ hupper j.1)
    (fun j ↦ hupperΘ j.1 j.2 j.2.property)
    (fun j ↦ hfrequency j.1 j.2 j.2.property) (fun j ↦ hsourceφ j.1)
    (fun j ↦ hsourceΘ j.1 j.2 j.2.property)
    (fun _ ↦ univ) (fun _ ↦ univ) (fun _ ↦ isClosed_univ) (fun _ ↦ isOpen_univ)
    (fun _ ↦ subset_rfl) (fun _ _ _ ↦ mem_univ _) (fun _ _ _ _ _ ↦ mem_univ _) true
  have hstrong (j : I × Icc (0 : ℝ) Δ) : ∀ w : H,
      Tendsto (fun k ↦ annularGraphOrientation true
        (fullGraphOperator (elapsedPhase (Ψ j.1) j.2)
          (frequencyCutFullAmplitude (complexPhysicalCutoff k)
            (elapsedAmplitude (b j.1) (χout j.1) (χsource j.1) (β j.1) j.2))) w)
        atTop (𝓝 (annularGraphOrientation true
          (fullGraphOperator (elapsedPhase (Ψ j.1) j.2)
            (elapsedAmplitude (b j.1) (χout j.1) (χsource j.1) (β j.1) j.2)) w)) := by
    obtain ⟨χ,hχ,hχcs,Treg,hlow,hbound,hreal,hrealAdj,hcut,hlim,hlimAdj⟩ := hgraphs j.1
    exact annularGraphOrientation_strongLimit_of_testRealizations true
      (elapsedPhase (Ψ j.1) j.2)
      (elapsedAmplitude (b j.1) (χout j.1) (χsource j.1) (β j.1) j.2)
      χ (fun k ↦ Treg k j.2) (fun k ↦ hreal k j.2 j.2.property)
      (fun k ↦ hcut k j.2) (hlimAdj j.2 j.2.property)
  have hid := hp.2.2.2.2.1 (fun _ ↦ complexPhysicalCutoff)
    (fun _ ↦ complexPhysicalCutoff_contDiff) (fun _ ↦ complexPhysicalCutoff_hasCompactSupport)
    (fun _ ↦ complexPhysicalCutoff_norm_le) (fun _ ↦ complexPhysicalCutoff_tendsto) hstrong
  have heq (i : I) (t : ℝ) (ht : t ∈ Icc 0 Δ) (c : P) (hc : c ∈ V) :
      R i t c = demodulatedL2Operator (lam i) (φ i c)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
        ((elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint) (u i c) := by
    exact inactive_kernel_eq_demodulated_adjoint_graph
      (Ψ i) (b i) (χout i) (χsource i) (β i) t (lam i) (φ i c) _
      (a i c) (u i c) (R i t c) (hu i c hc) (hid (i,⟨t,ht⟩) c hc)
  have hfull (i : I) (w : H) : IntegrableOn
      (fun t ↦ (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint w) (Icc 0 Δ) := by
    have hΨcont : Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ i q.1.1 q.1.2 q.2.1 q.2.2) :=
      ((hΨ i).comp ((contDiff_fst.fst.prodMk
        (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous
    have hoc : HasCompactSupport (χout i) :=
      hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h ↦ hmask i (Or.inl h))
    have hsc : HasCompactSupport (χsource i) :=
      hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h ↦ hmask i (Or.inr h))
    exact ((hgraphs i).integrableOn_elapsed_and_adjoint hΔ hΨcont (hb i)
      (ho i).continuous (hs i).continuous (hβsmooth i).continuous hoc hsc).2 w
  have hmR (i : I) (c : P) (hc : c ∈ V) :
      AEStronglyMeasurable (fun t ↦ R i t c) (volume.restrict (Icc 0 Δ)) := by
    have hh := ((carrierMultiplication (-(lam i)) (φ i c)
      ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))).continuous).comp_aestronglyMeasurable
        (hfull i (carrierMultiplication (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (u i c))).aestronglyMeasurable
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (heq i t ht c hc).symm
  have hInt := elapsedIntegral_complementary_sobolev hΔ hV R lam A₀ hA₀ hmR
    (fun i t ht ↦ hp.2.1 (i,⟨t,ht⟩)) (by
      intro s k Q
      obtain ⟨Csob,hCsob,hbound⟩ := hp.2.2.2.2.2 s k Q
      exact ⟨Csob,hCsob,fun i t ht c hc v hv ↦ hbound (i,⟨t,ht⟩) c hc v hv⟩)
  let out := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (Op i) (u i c)
  have hiEq (i : I) (c : P) (hc : c ∈ V) : (∫ t in Icc 0 Δ, R i t c) = out i c := by
    have hh : ∀ᵐ t ∂volume.restrict (Icc 0 Δ), R i t c =
        demodulatedL2Operator (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
          ((elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint) (u i c) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact heq i t ht c hc
    rw [integral_congr_ae hh]
    change (∫ t in Icc 0 Δ, carrierMultiplication (-(lam i)) (φ i c) _
      ((elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint
        (carrierMultiplication (lam i) (φ i c) _ (u i c)))) = _
    rw [(carrierMultiplication (-(lam i)) (φ i c) _).integral_comp_comm (hfull i _)]
    change _ = carrierMultiplication (-(lam i)) (φ i c) _
      (Op i (carrierMultiplication (lam i) (φ i c) _ (u i c)))
    rw [hOp]
  refine ⟨fun i ↦ (hInt.2.2.1 i).congr (fun c hc ↦ (hiEq i c hc).symm),?_⟩
  intro s k Q
  obtain ⟨Csob,hCsob,hbound⟩ := hInt.2.2.2.2.2 s k Q
  refine ⟨Δ*Csob,mul_nonneg hΔ hCsob,fun i c hc v hv ↦ ?_⟩
  have he : out i =ᶠ[𝓝 c] (fun c ↦ ∫ t in Icc 0 Δ, R i t c) :=
    Filter.mem_of_superset (hV.mem_nhds hc) (fun c hc ↦ (hiEq i c hc).symm)
  change MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧ _
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hbound i c hc v hv

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
