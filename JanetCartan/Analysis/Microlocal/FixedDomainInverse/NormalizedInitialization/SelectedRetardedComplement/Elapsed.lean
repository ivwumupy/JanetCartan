module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Primitive

/-!
# The actual forward elapsed operator minus its annular part

Apply the proved radial complementary tail estimate to the retained graph
regularizations. The integral is identified with the supplied bounded operator
and the original annular envelope; no operator is selected anew.
Consumer: the selected retarded complement in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.SelectedRetardedComplement
open FourierIntegral FourierIntegral.FullLowBounds ResponseTransfer Pseudodifferential
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open ResponseTransfer.RetainedFactors
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral.LowBounds.FrequencyCutoff
variable {p d r : ℕ} {I : Type}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The actual full-minus-annular forward operator has every parameter jet
in every real Sobolev space with arbitrary frequency decay. Its original
radial and source-gradient bounds are precisely the inputs of the existing
primitive tail theorem; the original graph certificates identify the same
operator. Consumer: `app:ch_response:lem:energy-carrier-jets`. -/
theorem forward_elapsed_complement_sobolev
    {V : Set P} (hV : IsOpen V) {X₀ S : Set E}
    (hX₀ : IsCompact X₀) [CompactSpace X₀] (hS : IsCompact S)
    {U : Set E} (hU : IsOpen U) (hSU : S ⊆ U) (hXU : X₀ ⊆ U)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    {a₀ B₀ m M : ℝ} (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    (Pφ PΨ BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hPφ : ∀ k, 0 ≤ Pφ k) (hPΨ : ∀ k, 0 ≤ PΨ k)
    (hBΨ : ∀ k, 0 ≤ BΨ k) (hBφ : ∀ k, 0 ≤ Bφ k)
    (hO : ∀ k, 0 ≤ O k) (hT : ∀ k, 0 ≤ T k) (hB : ∀ k, 0 ≤ B k) (hMβ : 0 ≤ Mβ)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d) (b : I → TwoTimeAmplitude d r)
    (χout χsource β : I → E → ℂ) (φ : I → P → E → ℝ) (a : I → P → E → F)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
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
    (hgradient : ∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hradial : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ U,
      m*‖ξ‖ ≤ ‖fderiv ℝ (fun z ↦ elapsedPhase (Ψ i) t z ξ) y‖ ∧
        ‖fderiv ℝ (fun z ↦ elapsedPhase (Ψ i) t z ξ) y‖ ≤ M*‖ξ‖)
    (hsourceφ : ∀ i c, c ∈ V → ∀ y ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (φ i c) y‖ ≤ Pφ k * L i ^ k)
    (hsourceΨ : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ S,
      ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ (k+1) (jointPhase (Ψ i)) (elapsedPoint t ((y,0),ξ))‖ ≤
          PΨ k*(1+‖ξ‖)*L i^k)
    (Creg : I → ℝ)
    (hgraphs : ∀ i, CappedGraphRealizations Δ (Ψ i) (b i)
      (χout i) (χsource i) (β i) (Creg i))
    (Op : I → H →L[ℂ] H)
    (hOp : ∀ i u, Op i u = elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i) u)
    (u : I → P → H) (hu : ∀ i c, c ∈ V → u i c =ᵐ[volume] a i c) :
    let π : E → ℂ := fun η ↦
      annularSelector (a₀/(2*M)) (2*B₀/m) (by positivity) (by positivity) η
    let out := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
      ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (Op i) (u i c) -
      IntegratedEnvelope.annularEnvelopeIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
        (β i) π (lam i) (φ i c)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (u i c)
    (∀ i, ContDiffOn ℝ ∞ (out i) V) ∧
      ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ Csob : ℝ, 0 ≤ Csob ∧
        ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
          MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧
          vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (out i) c v) ≤
            Csob * A₀ i * lam i ^ (-Q) := by
  dsimp only
  let π : E → ℂ := fun η ↦
    annularSelector (a₀/(2*M)) (2*B₀/m) (by positivity) (by positivity) η
  let R := fun i t ↦ elapsedAnnularRemainder hX₀ false true (Ψ i) (b i)
    (χout i) (χsource i) (β i) π (φ i) t (lam i) (a i)
  choose χ hχ hχcs Treg _hlow hregBound hreal hrealAdj hcut hlim hlimAdj using hgraphs
  have hΨtime i t (_ht : t ∈ Icc 0 Δ) x (_hx : x ∈ tsupport (χout i)) ξ
      (_hξ : ξ ∈ tsupport (β i)) :
      ContinuousAt (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ i q.1.1 q.1.2 q.2.1 q.2.2)
        ((x 0,x 0-t),(spatialPart x,spatialPart ξ)) :=
    ((hΨ i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous.continuousAt
  have ht := originalAnnularComplement_elapsed_sobolev
    hV hX₀ hS hU hU hSU hXU hΔ hν hν1 ha₀ hB₀ hm hm1 hM1
    Pφ PΨ BΨ Bφ O T B C Mβ hPφ hPΨ hBΨ hBφ hO hT hB hMβ
    lam L K A₀ hlam hL hLK hscale hA₀ Ψ b χout χsource β φ a ha has hmask
    ho hs hβsmooth hβ (fun _ ↦ univ) (fun _ ↦ univ)
    (fun _ ↦ isOpen_univ) (fun _ ↦ isOpen_univ) (fun i ↦ (hΨ i).contDiffOn) hb
    (fun _ _ _ _ _ _ _ ↦ mem_univ _) (fun _ _ _ _ _ _ _ ↦ mem_univ _)
    (fun i ↦ (hφ i).contDiffOn) hΨb hφb hbb hout hsource hmem hsob hgradient hradial
    hsourceφ hsourceΨ (fun _ _ ↦ univ) (fun _ _ ↦ univ)
    (fun _ _ _ ↦ isClosed_univ) (fun _ _ _ ↦ isOpen_univ)
    (fun _ _ _ ↦ subset_rfl) (fun _ _ _ _ _ ↦ mem_univ _)
    (fun _ _ _ _ _ _ _ ↦ mem_univ _) hΨtime χ hχ hχcs Treg hreal hrealAdj
    (fun i j t _ ↦ hcut i j t) hlim hlimAdj Creg hregBound false
  let out := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (Op i) (u i c) -
      IntegratedEnvelope.annularEnvelopeIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
        (β i) π (lam i) (φ i c)
        ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (u i c)
  have hiEq i c (hc : c ∈ V) : (∫ t in Icc 0 Δ, R i t c) = out i c := by
    obtain ⟨w,_,_,_,_,_,hDm⟩ := ht.1 i c hc
    obtain ⟨u₀,hu₀,hcu,he,_⟩ :=
      hDm ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
    have heu : u₀ = u i c := Lp.ext (hu₀.trans (hu i c hc).symm)
    subst u₀
    rw [← hcu] at he
    change (∫ t in Icc 0 Δ, R i t c) =
      carrierMultiplication (-(lam i)) (φ i c) _
        (elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i)
          (carrierMultiplication (lam i) (φ i c) _ (u i c))) -
        IntegratedEnvelope.annularEnvelopeIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
          (β i) π (lam i) (φ i c) _ (u i c) at he
    rw [← hOp i] at he
    exact he
  refine ⟨fun i ↦ ((ht.2.2 true).2.2.2.1 i).congr (fun c hc ↦ (hiEq i c hc).symm),?_⟩
  intro s k Q
  obtain ⟨Csob,hCsob,hbound⟩ := (ht.2.2 true).2.2.2.2.2.2 s k Q
  refine ⟨Δ*Csob,mul_nonneg hΔ hCsob,fun i c hc v hv ↦ ?_⟩
  have he : out i =ᶠ[𝓝 c] (fun c ↦ ∫ t in Icc 0 Δ, R i t c) :=
    Filter.mem_of_superset (hV.mem_nhds hc) (fun c hc ↦ (hiEq i c hc).symm)
  change MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧ _
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hbound i c hc v hv

end JanetCartan.FixedDomainInverse.SelectedRetardedComplement
