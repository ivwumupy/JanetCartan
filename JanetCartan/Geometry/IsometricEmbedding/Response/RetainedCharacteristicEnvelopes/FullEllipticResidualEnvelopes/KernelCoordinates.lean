module
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.KernelProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates

/-!
# Exact external coordinates for full PDO complementary kernels

Only the carrier parameter is changed. The full covector, source and output
spatial variables remain the original ones. This supplies the product
parameter space of the actual elliptic/endpoint/algebraic residual letters in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open FourierIntegral Pseudodifferential DirectEvolution.AnnularComplement
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open FullSourceEnvelopes
variable {p d r : ℕ} {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "P" => Par
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The primitive complete-frequency source estimate in the original carrier
parameter space. A contractive Euclidean chart has no input-profile cost;
its inverse contributes only a fixed constant to each external derivative.
Consumer: `completeDiagonalAnnularComplement_sobolev`
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem exists_complete_diagonal_sourceKernel_profiles_of_coordinates
    (e : Euclidean p ≃L[ℝ] Par) (he : ∀ z, ‖e z‖ ≤ ‖z‖)
    {V : Set P} (hV : IsOpen V) {S X₀ : Set E}
    (hS : IsCompact S) (hX₀ : IsCompact X₀)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (Bsymbol Bphase Pphase : ℕ → ℝ) (Csource : ℕ → ℕ → ℝ)
    (hBsymbol : ∀ k, 0 ≤ Bsymbol k) (hBphase : ∀ k, 0 ≤ Bphase k)
    (hPphase : ∀ k, 0 ≤ Pphase k) :
    ∃ Ckernel : ℕ → ℕ → ℝ, (∀ j N, 0 ≤ Ckernel j N) ∧
      ∀ (lam L K A₀ : ℝ), 1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam^(1-ν) → 0 ≤ A₀ →
      ∀ (σ : E → E → Mat), ContDiff ℝ ∞ (Function.uncurry σ) →
        (∀ k ξ y, y ∈ S ∪ X₀ →
          ‖iteratedFDeriv ℝ k (fun z ↦ σ z ξ) y‖ ≤ Bsymbol k * L^k) →
      ∀ (φ : P → E → ℝ), ContDiff ℝ ∞ (Function.uncurry φ) →
        (∀ k c, c ∈ V → ∀ y ∈ S ∪ X₀,
          ‖iteratedFDeriv ℝ k (Function.uncurry φ) (c,y)‖ ≤ Bphase k * L^k) →
      ∀ U X : Set E, IsOpen U → IsOpen X → S ⊆ U → X₀ ⊆ X →
        (∀ c ∈ V, ∀ y ∈ U, a₀ ≤ ‖fderiv ℝ (φ c) y‖ ∧
          ‖fderiv ℝ (φ c) y‖ ≤ B₀) →
        (∀ c ∈ V, ∀ y ∈ S, ∀ k, 1 ≤ k →
          ‖iteratedFDeriv ℝ (k+1) (φ c) y‖ ≤ Pphase k * L^k) →
      ∀ (a : P → E → F) (_ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (_has : ∀ c ∈ V, tsupport (a c) ⊆ S),
        (∀ c, c ∈ V → ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
          let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) c w
          ∃ hm : MemLp f 2 volume,
            MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
              vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * A₀ * K^(s+l)) →
      let π : E → ℂ := fun η ↦ annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) η
      ∀ (adj demod : Bool) (j N : ℕ) (ξ : E) (q : P × E), q.1 ∈ V →
      ∀ v : Fin j → P × E, (∀ k, ‖v k‖ ≤ 1) →
        ‖iteratedFDeriv ℝ j (fun q : P × E ↦
          annularSourceKernelObservation adj demod (fun y η ↦ inner ℝ y η)
            (fun y z η ↦ (χout y * χsource z) • σ y η)
            π (φ q.1) lam (a q.1) q.2 ξ) q v‖ ≤
          Ckernel j N * (A₀ * (lam+‖ξ‖)^j * K^(d+1+1+j) *
            (K/(lam+‖ξ‖))^N) := by
  let ec := e.prodCongr (ContinuousLinearEquiv.refl ℝ E)
  have hec (q : Euclidean p × E) : ‖ec q‖ ≤ ‖q‖ := by
    exact max_le_max (he q.1) le_rfl
  let D : ℝ := 1 + ‖e.symm.toContinuousLinearMap‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hinv (q : Par × E) : ‖ec.symm q‖ ≤ D * ‖q‖ := by
    apply max_le
    · exact (e.symm.toContinuousLinearMap.le_opNorm q.1).trans
        (mul_le_mul (by dsimp [D]; linarith) (norm_fst_le q)
          (norm_nonneg _) (by positivity))
    · exact (norm_snd_le q).trans (le_mul_of_one_le_left (norm_nonneg _) hD1)
  let Vc := e ⁻¹' V
  have hVc : IsOpen Vc := hV.preimage e.continuous
  obtain ⟨C,hC,hprofile⟩ := exists_complete_diagonal_sourceKernel_profiles
    hVc hS hX₀ χout χsource ho hs hmask hν hν1 ha₀ hB₀
    Bsymbol Bphase Pphase Csource hBsymbol hBphase hPphase
  refine ⟨fun j N ↦ D^j * C j N,fun j N ↦ mul_nonneg (pow_nonneg hD.le _) (hC j N),?_⟩
  intro lam L K A₀ hlam hL hLK hscale hA₀ σ hσ hσjets φ hφ hφjets
    U X hU hX hSU hXX hgradient hsourceφ a ha has hfourier π adj demod j N ξ q hq v hv
  let φc : Euclidean p → E → ℝ := fun c y ↦ φ (e c) y
  let ac : Euclidean p → E → F := fun c y ↦ a (e c) y
  have hφc : ContDiff ℝ ∞ (Function.uncurry φc) := hφ.comp ec.contDiff
  have hφcjets (k : ℕ) (c : Euclidean p) (hc : c ∈ Vc) (y : E) (hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (Function.uncurry φc) (c,y)‖ ≤ Bphase k * L^k :=
    (norm_externalCoordinate_jet_le ec hec (Function.uncurry φ) (c,y) k).trans
      (hφjets k (e c) hc y hy)
  have hac : ContDiffOn ℝ ∞ (Function.uncurry ac) (Vc ×ˢ univ) :=
    ha.comp ec.contDiff.contDiffOn (fun q hq ↦ ⟨hq.1,mem_univ _⟩)
  have hasc (c : Euclidean p) (hc : c ∈ Vc) : tsupport (ac c) ⊆ S := has (e c) hc
  have hunit {l : ℕ} (w : Fin l → Euclidean p) (hw : ∀ k, ‖w k‖ ≤ 1) :
      ∀ k, ‖e (w k)‖ ≤ 1 := fun k ↦ (he (w k)).trans (hw k)
  have hfourierc (c : Euclidean p) (hc : c ∈ Vc) (l : ℕ) (w : Fin l → Euclidean p)
      (hw : ∀ k, ‖w k‖ ≤ 1) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hVc hac hasc l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac q y) c w)) ∧
      vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hVc hac hasc l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac q y) c w)) ≤ Csource l s * A₀ * K^(s+l) := by
    obtain ⟨hm, hmem, hsob⟩ := hfourier (e c) hc l (fun k ↦ e (w k)) (hunit w hw) s
    have hedata : (parameterSource_memLp hS hVc hac hasc l w hc).toLp
        (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac q y) c w) =
        hm.toLp (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) (e c) (fun k ↦ e (w k))) := by
      apply Lp.ext
      filter_upwards [(parameterSource_memLp hS hVc hac hasc l w hc).coeFn_toLp,
        hm.coeFn_toLp] with y hy hz
      rw [hy,hz]
      change iteratedFDeriv ℝ l ((fun q ↦ a q y) ∘ e) c w = _
      rw [externalCoordinate_jet]
      rfl
    rw [hedata]
    exact ⟨hmem,hsob⟩
  let vc : Fin j → Euclidean p × E := fun k ↦ D⁻¹ • ec.symm (v k)
  have hvc : ∀ k, ‖vc k‖ ≤ 1 := by
    intro k
    calc
      ‖vc k‖ = D⁻¹ * ‖ec.symm (v k)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
      _ ≤ D⁻¹ * (D * ‖v k‖) := mul_le_mul_of_nonneg_left (hinv (v k)) (inv_nonneg.mpr hD.le)
      _ = ‖v k‖ := by rw [← mul_assoc,inv_mul_cancel₀ hD.ne',one_mul]
      _ ≤ 1 := hv k
  have hqc : (ec.symm q).1 ∈ Vc := by
    change e (e.symm q.1) ∈ V
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq
  have hk := hprofile lam L K A₀ hlam hL hLK hscale hA₀ σ hσ hσjets φc hφc hφcjets
    U X hU hX hSU hXX (fun c hc ↦ hgradient (e c) hc)
    (fun c hc ↦ hsourceφ (e c) hc) ac hac hasc
    (fun c hc l w hw s ↦ (hfourierc c hc l w hw s).1)
    (fun c hc l w hw s ↦ (hfourierc c hc l w hw s).2)
    adj demod j N ξ (ec.symm q) hqc vc hvc
  let Fk : Par × E → F := fun z ↦ annularSourceKernelObservation adj demod
    (fun y η ↦ inner ℝ y η) (fun y z η ↦ (χout y * χsource z) • σ y η)
      π (φ z.1) lam (a z.1) z.2 ξ
  have hejet : iteratedFDeriv ℝ j Fk q v =
      D^j • iteratedFDeriv ℝ j (Fk ∘ ec) (ec.symm q) vc := by
    rw [externalCoordinate_jet,ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hdirs : (fun k ↦ ec.toContinuousLinearMap (vc k)) = fun k ↦ D⁻¹ • v k := by
      funext k
      simp only [vc,ContinuousLinearMap.map_smul,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [hdirs,ContinuousMultilinearMap.map_smul_univ,smul_smul]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      ← mul_pow,mul_inv_cancel₀ hD.ne',one_pow,one_smul]
  change ‖iteratedFDeriv ℝ j Fk q v‖ ≤ _
  rw [hejet,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hD.le _)]
  exact (mul_le_mul_of_nonneg_left hk (pow_nonneg hD.le _)).trans_eq (by ring)

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
