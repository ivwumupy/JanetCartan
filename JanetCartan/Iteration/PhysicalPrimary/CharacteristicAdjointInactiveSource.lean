module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointElapsedEnvelopes
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale

/-!
# Inactive literal-adjoint envelopes in the original full source parameters

The label and covector stay independent. Apply the proved complete inactive literal-adjoint
kernel and time integral in their canonical Euclidean coordinates, then pull
back every actual derivative. Only the fixed factor two per parameter direction
is introduced; the spatial measure, operator, masks and decay are unchanged.
Consumer: the inactive pieces of finite selected characteristic words in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds ResponseTransfer Pseudodifferential
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open ResponseTransfer.RetainedFactors ResponseTransfer.FullSourceEnvelopes
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
variable {d r : ℕ} {I : Type}
local notation "P" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3+d)
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem inactive_vectorSobolev_real_smul (s c : ℝ) {v : H}
    (hv : MemVectorFourierSobolev s v) :
    vectorFourierSobolevNorm s (c • v) = |c| * vectorFourierSobolevNorm s v := by
  have hcv := (vectorFourierSobolevLevel s).smul_mem c hv
  rw [← norm_vectorWeightedFourier s ⟨c • v,hcv⟩, ← norm_vectorWeightedFourier s ⟨v,hv⟩]
  change ‖vectorWeightedFourier s (c • (⟨v,hv⟩ : vectorFourierSobolevLevel s))‖ = _
  rw [map_smul,norm_smul,Real.norm_eq_abs]

/-- Apply the actual inactive elapsed estimate to all original label and
covector directions. The existential source Fourier classes are the literal
ones supplied by `SourceProfiles`; no new source smoothness or output bound
is postulated (`app:ch_response:lem:energy-carrier-jets`). -/
theorem inactive_fullSource_adjoint_elapsed_operator_sobolev
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
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C l s * A₀ i * K i ^ (s+l))
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
  let e : Pc ≃L[ℝ] P := EuclideanSpace.finAddEquivProd
  let ec := e.prodCongr (ContinuousLinearEquiv.refl ℝ E)
  let Vc := e ⁻¹' V
  let P₀c := e ⁻¹' P₀
  have hVc : IsOpen Vc := hV.preimage e.continuous
  have hP₀c : IsClosed P₀c := hP₀.preimage e.continuous
  have he (z : Pc) : ‖e z‖ ≤ ‖z‖ := fullSource_coordinate_norm_bounds.1 z
  have hec (q : Pc × E) : ‖ec q‖ ≤ ‖q‖ := max_le_max (he q.1) le_rfl
  let ac : I → Pc → E → F := fun i c y ↦ a i (e c) y
  let φc : I → Pc → E → ℝ := fun i c y ↦ φ i (e c) y
  let uc : I → Pc → H := fun i c ↦ u i (e c)
  have hac i : ContDiffOn ℝ ∞ (Function.uncurry (ac i)) (Vc ×ˢ univ) :=
    (ha i).comp ec.contDiff.contDiffOn (fun q hq ↦ ⟨hq.1,mem_univ _⟩)
  have hasc i c (hc : c ∈ Vc) : tsupport (ac i c) ⊆ S := has i (e c) hc
  have hφc i : ContDiff ℝ ∞ (Function.uncurry (φc i)) := (hφ i).comp ec.contDiff
  have hφbc i k c (hc : c ∈ Vc) y (hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (φc i)) (c,y)‖ ≤ Bφ k*L i^k :=
    (norm_externalCoordinate_jet_le ec hec (Function.uncurry (φ i)) (c,y) k).trans
      (hφb i k (e c) hc y hy)
  have hfc i c (hc : c ∈ Vc) l (w : Fin l → Pc) (hw : ∀ j, ‖w j‖ ≤ 1) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hVc (hac i) (hasc i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac i q y) c w)) ∧
      vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hVc (hac i) (hasc i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac i q y) c w)) ≤ C l s*A₀ i*K i^(s+l) := by
    obtain ⟨hm,hmem,hbound⟩ := hfourier i (e c) hc l (fun j ↦ e (w j))
      (fun j ↦ (he (w j)).trans (hw j)) s
    have hedata : (parameterSource_memLp hS hVc (hac i) (hasc i) l w hc).toLp
        (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac i q y) c w) =
        hm.toLp (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) (e c) (fun j ↦ e (w j))) := by
      apply Lp.ext
      filter_upwards [(parameterSource_memLp hS hVc (hac i) (hasc i) l w hc).coeFn_toLp,
        hm.coeFn_toLp] with y hy hz
      rw [hy,hz]
      change iteratedFDeriv ℝ l ((fun q ↦ a i q y) ∘ e) c w = _
      rw [externalCoordinate_jet]
      rfl
    rw [hedata]
    exact ⟨hmem,hbound⟩
  obtain ⟨hsm,hbound⟩ := inactive_adjoint_elapsed_operator_sobolev
    hVc hP₀c hX₀ hS hU hSU hXU hΔ hν hν1 hgap hMfreq Pφ PΘ BΨ Bφ O T B C Mβ
    hPφ hPΘ hBΨ hBφ hO hT hB hMβ lam L K A₀ hlam hL hLK hscale hA₀
    Ψ b χout χsource β φc ac hac hasc (fun i c hc y ↦ hparam i (e c) hc y)
    hmask ho hs hβsmooth hβ hΨ hb hφc hΨb hφbc hbb hout hsource
    (fun i c hc l w hw s ↦ (hfc i c hc l w hw s).1)
    (fun i c hc l w hw s ↦ (hfc i c hc l w hw s).2)
    (fun i c hc ↦ hupper i (e c) hc) hupperΘ
    (fun i t ht ξ hξ c hc ↦ hfrequency i t ht ξ hξ (e c) hc)
    (fun i c hc ↦ hsourceφ i (e c) hc) hsourceΘ Creg hgraphs Op hOp uc
    (fun i c hc ↦ hu i (e c) hc)
  let out : I → P → H := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (Op i) (u i c)
  have hsmooth (i : I) : ContDiffOn ℝ ∞ (out i) V := by
    have hh := (hsm i).comp e.symm.contDiff.contDiffOn (s := V) (by
      intro c hc
      change e (e.symm c) ∈ V
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc)
    simpa only [uc,φc,Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using hh
  refine ⟨hsmooth,?_⟩
  intro s k Q
  obtain ⟨Csob,hCsob,hbc⟩ := hbound s k Q
  refine ⟨(2:ℝ)^k*Csob,mul_nonneg (by positivity) hCsob,fun i c hc v hv ↦ ?_⟩
  let vc : Fin k → Pc := fun j ↦ (2:ℝ)⁻¹ • e.symm (v j)
  have hvc : ∀ j, ‖vc j‖ ≤ 1 := by
    intro j
    change ‖(2:ℝ)⁻¹ • e.symm (v j)‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)]
    linarith [fullSource_coordinate_norm_bounds.2 (v j),hv j]
  have hcc : e.symm c ∈ Vc := by
    change e (e.symm c) ∈ V
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc
  have hejet : iteratedFDeriv ℝ k (out i) c v =
      (2:ℝ)^k • iteratedFDeriv ℝ k (out i ∘ e) (e.symm c) vc := by
    rw [externalCoordinate_jet,ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hdirs : (fun j ↦ e.toContinuousLinearMap (vc j)) = fun j ↦ (2:ℝ)⁻¹ • v j := by
      funext j
      simp only [vc,ContinuousLinearMap.map_smul,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [hdirs,ContinuousMultilinearMap.map_smul_univ,smul_smul]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      ← mul_pow,mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),one_pow,one_smul]
  have hh : MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i ∘ e) (e.symm c) vc) ∧
      vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (out i ∘ e) (e.symm c) vc) ≤
        Csob*A₀ i*lam i^(-Q) := hbc i (e.symm c) hcc vc hvc
  change MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧ _
  rw [hejet]
  refine ⟨(vectorFourierSobolevLevel s).smul_mem _ hh.1,?_⟩
  rw [inactive_vectorSobolev_real_smul s _ hh.1,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^k)]
  exact (mul_le_mul_of_nonneg_left hh.2 (by positivity : 0 ≤ (2:ℝ)^k)).trans_eq (by ring)

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
