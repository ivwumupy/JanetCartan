module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointKernelProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.PrimitiveSobolev

/-!
# Complete inactive literal-adjoint kernels in the original Fourier Sobolev scale

Apply the actual inactive kernel-jet producer to the full frequency integral.
The source may vanish outside a fixed closed parameter set: only parameters
on that set require the angular gap. Outside it, all actual kernel derivatives
vanish by local equality. The graph's original canonical strong regularizations
identify the same output, and the auxiliary annular selector is exactly zero.

Consumer: positive and negative source pieces of the selected retarded solver
and residual in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open ResponseTransfer
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives ResponseTransfer.Complement.ParameterDerivatives.Hilbert
open Pseudodifferential
variable {p d r : ℕ} {I : Type}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The literal adjoint of the same full graph has arbitrary inactive Sobolev precision in
all original external parameter jets. Every kernel bound and joint derivative
is proved from the original primitives; the only regularization input is the
actual graph constructor's strong limit (`app:ch_response:lem:energy-carrier-jets`). -/
theorem inactive_adjoint_elapsed_kernel_sobolev
    {V P₀ : Set P} (hV : IsOpen V) (hP₀ : IsClosed P₀) {X₀ S : Set E}
    (hX₀ : IsCompact X₀) [CompactSpace X₀] (hS : IsCompact S)
    {U X : Set E} (hU : IsOpen U) (hX : IsOpen X) (hSU : S ⊆ U) (hXX : X₀ ⊆ X)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    {gap B₀ Mfreq : ℝ} (hgap : 0 < gap) (hMfreq : 0 ≤ Mfreq)
    (Pφ PΘ BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hPφ : ∀ k, 0 ≤ Pφ k) (hPΘ : ∀ k, 0 ≤ PΘ k)
    (hBΨ : ∀ k, 0 ≤ BΨ k) (hBφ : ∀ k, 0 ≤ Bφ k)
    (hO : ∀ k, 0 ≤ O k) (hT : ∀ k, 0 ≤ T k) (hB : ∀ k, 0 ≤ B k) (hMβ : 0 ≤ Mβ)
    (lam L K t A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (ht : ∀ i, t i ∈ Icc 0 Δ)
    (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d) (b : I → TwoTimeAmplitude d r)
    (χout χsource β : I → E → ℂ) (φ : I → P → E → ℝ) (a : I → P → E → F)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
    (hparam : ∀ i c, c ∉ P₀ → ∀ x, a i c x = 0)
    (hmask : ∀ i, tsupport (χout i) ∪ tsupport (χsource i) ⊆ X₀)
    (ho : ∀ i, ContDiff ℝ ∞ (χout i)) (hs : ∀ i, ContDiff ℝ ∞ (χsource i))
    (hβsmooth : ∀ i, ContDiff ℝ ∞ (β i))
    (hβ : ∀ i ξ, ‖β i ξ‖ ≤ Mβ)
    (OΨ Ob : I → Set (TwoTimePoint d))
    (hOΨ : ∀ i, IsOpen (OΨ i)) (hOb : ∀ i, IsOpen (Ob i))
    (hΨ : ∀ i, ContDiffOn ℝ ∞ (jointPhase (Ψ i)) (OΨ i))
    (hb : ∀ i, ContDiff ℝ ∞ (jointAmplitude (b i)))
    (hmapΨ : ∀ i ξ, β i ξ ≠ 0 → ∀ y ∈ U ∪ X,
      elapsedPoint (t i) ((y, 0), ξ) ∈ OΨ i)
    (hmapb : ∀ i ξ, β i ξ ≠ 0 → ∀ y ∈ U ∪ X,
      elapsedPoint (t i) ((y, 0), ξ) ∈ Ob i)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ (U ∪ X)))
    (hΨb : ∀ i ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointPhase (Ψ i)) (elapsedPoint (t i) ((y, 0), ξ))‖ ≤
        BΨ k * (1 + ‖ξ‖) * L i ^ k)
    (hφb : ∀ i k c, c ∈ V → ∀ y ∈ S ∪ X₀,
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) (c, y)‖ ≤ Bφ k * L i ^ k)
    (hbb : ∀ i ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointAmplitude (b i)) (elapsedPoint (t i) ((y, 0), ξ))‖ ≤
        B k * L i ^ k)
    (hout : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χout i) y‖ ≤ O k)
    (hsource : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χsource i) y‖ ≤ T k)
    (hmem : ∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y => iteratedFDeriv ℝ l (fun q => a i q y) c w)))
    (hsob : ∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y => iteratedFDeriv ℝ l (fun q => a i q y) c w)) ≤
            C l s * A₀ i * K i ^ (s + l))
    (hupper : ∀ i c, c ∈ V → ∀ z ∈ U, ‖fderiv ℝ (φ i c) z‖ ≤ B₀)
    (hupperΘ : ∀ i ξ, β i ξ ≠ 0 → ∀ z ∈ U,
      ‖fderiv ℝ (fun y ↦ elapsedPhase (Ψ i) (t i) y ξ) z‖ ≤ Mfreq*‖ξ‖)
    (hfrequency : ∀ i ξ, β i ξ ≠ 0 → ∀ c ∈ V, c ∈ P₀ → ∀ z ∈ U,
      gap*(lam i+‖ξ‖) ≤ ‖lam i • fderiv ℝ (φ i c) z-fderiv ℝ (fun y ↦ elapsedPhase (Ψ i) (t i) y ξ) z‖)
    (hsourceφ : ∀ i c, c ∈ V → ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (φ i c) z‖ ≤ Pφ k * L i ^ k)
    (hsourceΘ : ∀ i ξ, β i ξ ≠ 0 → ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (fun y ↦ elapsedPhase (Ψ i) (t i) y ξ) z‖ ≤ PΘ k*‖ξ‖*L i^k)
    (D Ω : I → Set (E × E)) (hD : ∀ i, IsClosed (D i))
    (hΩ : ∀ i, IsOpen (Ω i)) (hDΩ : ∀ i, D i ⊆ Ω i)
    (hphaseMap : ∀ i q, q ∈ Ω i → elapsedPoint (t i) ((q.1, 0), q.2) ∈ OΨ i)
    (hsD : ∀ i x z ξ, elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i) x z ξ ≠ 0 →
      (x, ξ) ∈ D i)
    (demod : Bool) :
    let π : E → ℂ := 0
    let κ := fun i ξ (q : P × E) => annularSourceKernelObservation true demod
      (elapsedPhase (Ψ i) (t i)) (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
        π (φ i q.1) (lam i) (a i q.1) q.2 ξ
    let R := fun i => elapsedAnnularRemainder hX₀ true demod (Ψ i) (b i)
      (χout i) (χsource i) (β i) π (φ i) (t i) (lam i) (a i)
    let Tfull := fun i => annularGraphOrientation true
      (fullGraphOperator (elapsedPhase (Ψ i) (t i))
        (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i)))
    let Tcut := fun i => annularGraphOrientation true
      (fullGraphOperator (elapsedPhase (Ψ i) (t i))
        (frequencyCutFullAmplitude (fun ξ => π ((lam i)⁻¹ • ξ))
          (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))))
    (∀ i q, q ∈ V ×ˢ univ → Integrable (fun ξ => κ i ξ q)) ∧
    (∀ i, ContDiffOn ℝ ∞ (R i) V) ∧
    (∀ i c, c ∈ V → R i c =ᵐ[volume] fun x => ∫ ξ, κ i ξ (c, x)) ∧
    (∀ i k (v : Fin k → P) c, c ∈ V →
      iteratedFDeriv ℝ k (R i) c v =ᵐ[volume]
        fun x => ∫ ξ, iteratedFDeriv ℝ k (fun q => κ i ξ (q, x)) c v) ∧
    (∀ (χ : I → ℕ → E → ℂ),
      (∀ i j, ContDiff ℝ ∞ (χ i j)) →
      (∀ i j, HasCompactSupport (χ i j)) → (∀ i j ξ, ‖χ i j ξ‖ ≤ 1) →
      (∀ i ξ, Tendsto (fun j => χ i j ξ) atTop (𝓝 1)) →
      (∀ i (w : H), Tendsto (fun j => annularGraphOrientation true
        (fullGraphOperator (elapsedPhase (Ψ i) (t i))
          (frequencyCutFullAmplitude (χ i j)
            (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i)))) w) atTop
        (𝓝 (annularGraphOrientation true (fullGraphOperator (elapsedPhase (Ψ i) (t i))
          (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))) w))) →
      ∀ i c, c ∈ V → ∃ w : H,
        w =ᵐ[volume] (fun x => carrier (lam i) (φ i c) x • a i c x) ∧
        R i c =ᵐ[volume] fun x => (if demod then carrier (-lam i) (φ i c) x else 1) •
          ((Tfull i w - Tcut i w) x)) ∧
    ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
      MemVectorFourierSobolev s (iteratedFDeriv ℝ k (R i) c v) ∧
      vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (R i) c v) ≤
        Csob * A₀ i * lam i ^ (-Q) := by
  dsimp only
  let π : E → ℂ := 0
  let κ := fun i ξ (q : P × E) => annularSourceKernelObservation true demod
    (elapsedPhase (Ψ i) (t i)) (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
      π (φ i q.1) (lam i) (a i q.1) q.2 ξ
  have hπ : ContDiff ℝ ∞ π := contDiff_const
  have hA (i : I) : ContDiff ℝ ∞ (fun q : E × E × E =>
      elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i) q.1 q.2.1 q.2.2) :=
    (contDiff_uncurry_elapsedAmplitude (b i) (χout i) (χsource i) (β i)
      (hb i) (ho i) (hs i) (hβsmooth i) (t i)).comp
      ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  have hΘ (i : I) : ContDiffOn ℝ ∞
      (Function.uncurry (elapsedPhase (Ψ i) (t i))) (Ω i) := by
    have hE : ContDiff ℝ ∞ (fun q : E × E => elapsedPoint (t i) ((q.1, 0), q.2)) :=
      (elapsedLinear.contDiff.add contDiff_const).comp
        ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    have hp := (hΨ i).comp hE.contDiffOn (hphaseMap i)
    simp only [Function.comp_def, jointPhase, elapsedPoint_eq] at hp
    have hc : ContDiff ℝ ∞ (fun x : E => x 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff
    exact (((hc.comp contDiff_fst).sub contDiff_const).mul
      (hc.comp contDiff_snd)).contDiffOn.add hp
  have hzero (i : I) (x : E) (hx : x ∉ X₀) (z ξ : E) :
      (if true then elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i) z x ξ
      else elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i) x z ξ) = 0 := by
    exact elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _
      (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport (fun h => hx (hmask i (Or.inr h))))))
  have hJ (i : I) (dm : Bool) (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') :=
    contDiffOn_annularSourceIntegrand_localCarrierPhase true dm
    (elapsedPhase (Ψ i) (t i)) (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
    π' (φ i) (lam i) (a i) hV (hD i) (hΩ i) (hDΩ i) (hΘ i) (hsD i)
    (fun k l => (AmplitudeBound.matrixEntryEvaluation k l).contDiff.comp (hA i)) hπ'
    (hU.union hX) hX₀.isClosed hS.isClosed
    (fun _ h => Or.inr (hXX h)) (fun _ h => Or.inl (hSU h))
    (hφ i) (ha i) (has i) (hzero i)
  have hκ (i : I) (dm : Bool) (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') :=
    contDiffOn_annularSourceKernelObservation_of_joint true dm
    (elapsedPhase (Ψ i) (t i)) (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
    π' (φ i) (lam i) (a i) hV (hJ i dm π' hπ') hS (has i)
  have hκξ (i : I) (ξ : E) : ContDiffOn ℝ ∞ (κ i ξ) (V ×ˢ univ) :=
    (hκ i demod π hπ).comp (f := fun q : P × E => (q, ξ))
      (contDiffOn_id.prodMk contDiffOn_const)
      (fun q hq => ⟨hq, mem_univ ξ⟩)
  have hmeas (i : I) (q : P × E) (hq : q ∈ V ×ˢ univ) :
      AEStronglyMeasurable (fun ξ => κ i ξ q) volume := by
    exact (contDiffOn_univ.mp ((hκ i demod π hπ).comp (f := fun ξ : E => (q, ξ))
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun ξ _ => ⟨hq, mem_univ ξ⟩))).continuous.aestronglyMeasurable
  obtain ⟨Ckernel,hCkernel,hprofile⟩ := exists_inactive_adjoint_sourceKernel_profile
    (V ∩ P₀) hX₀ hS hΔ hν hν1 hgap hMfreq Pφ PΘ hPφ hPΘ
    BΨ Bφ O T B C Mβ hBΨ hBφ hO hT hB hMβ
  have hbound (j N : ℕ) (i : I) (ξ : E) (q : P × E) (hq : q ∈ V ×ˢ univ)
      (v : Fin j → P × E) (hv : ∀ k, ‖v k‖ ≤ 1) :
      ‖iteratedFDeriv ℝ j (κ i ξ) q v‖ ≤
        Ckernel j N*((A₀ i*(lam i+‖ξ‖)^j*K i^(d+1+1+j))*(K i/(lam i+‖ξ‖))^N) := by
    by_cases hqP : q.1 ∈ P₀
    · exact hprofile j N (lam i) (L i) (K i) (t i) (A₀ i)
        (hlam i) (hL i) (hLK i) (hscale i) (ht i) (hA₀ i)
        ξ (Ψ i) (b i) (χout i) (χsource i) (β i) (φ i)
        V U X (OΨ i) (Ob i) hV hU hX (hOΨ i) (hOb i) inter_subset_left hSU hXX
        (a i) (ha i) (has i) (hmask i) (ho i) (hs i) (hβ i ξ)
        (fun _ ↦ hΨ i) (fun _ ↦ (hb i).contDiffOn) (hmapΨ i ξ) (hmapb i ξ)
        (fun _ ↦ hφ i) (hΨb i ξ) (fun _ k c hc ↦ hφb i k c hc.1) (hbb i ξ)
        (hout i) (hsource i)
        (fun c hc _ l _ w hw s ↦ hmem i c hc l w hw s)
        (fun c hc _ l _ w hw s ↦ hsob i c hc l w hw s)
        (fun _ c hc ↦ hupper i c hc.1) (hupperΘ i ξ)
        (fun hn c hc ↦ hfrequency i ξ hn c hc.1 hc.2)
        (fun _ c hc ↦ hsourceφ i c hc.1) (hsourceΘ i ξ) demod v hv q ⟨hq.1,hqP⟩
    · have he : κ i ξ =ᶠ[𝓝 q] (fun _ ↦ (0 : F)) := by
        have hn : ∀ᶠ w : P × E in 𝓝 q, w.1 ∉ P₀ :=
          (hP₀.isOpen_compl.preimage continuous_fst).mem_nhds hqP
        filter_upwards [hn] with w hw
        dsimp only [κ]
        rw [annularSourceKernelObservation_eq_integral]
        simp only [annularSourceIntegrand_eq_zero_of_source_eq_zero _ _ _ _ _ _ _ _ _ _ _
          (hparam i w.1 hw _),integral_zero,smul_zero]
      rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
      change ‖iteratedFDeriv ℝ j (0 : P × E → F) q v‖ ≤ _
      simp only [iteratedFDeriv_zero,Pi.zero_apply,zero_apply,norm_zero]
      have hC := hCkernel j N
      have hA := hA₀ i
      have hK : 0 ≤ K i := zero_le_one.trans ((hL i).trans (hLK i))
      have hLpos : 0 < lam i := zero_lt_one.trans_le (hlam i)
      positivity
  have hresult := annularKernel_sobolev_realization hV hX₀ κ hκξ hmeas
    (fun i ξ c _ x hx => annularSourceKernelObservation_eq_zero_of_amplitude
      true demod _ _ π (φ i c) (lam i) (a i c) x ξ (fun z => hzero i x hx z ξ))
    (fun _ => 0) (fun j => j) (fun _ => 0) (fun j => d + 1 + 1 + j)
    Ckernel hCkernel hν hν1 lam L K A₀ hlam hL hLK hscale hA₀ (by
      intro j N i ξ q hq v hv
      apply (hbound j N i ξ q hq v hv).trans_eq
      simp only [Real.rpow_zero, pow_zero, mul_one]
      ring)
  refine ⟨hresult.1, hresult.2.2.2.1, hresult.2.2.2.2.1,
    hresult.2.2.2.2.2.1, ?_, hresult.2.2.2.2.2.2⟩


  intro χ hχ hχc hχb hχlim hstrong i c hc
  have hφc : ContDiffOn ℝ ∞ (φ i c) U :=
    (hφ i).comp (f := fun x : E => (c, x))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hc, Or.inl hz⟩)
  have hac : ContDiffOn ℝ ∞ (a i c) U :=
    (ha i).comp (f := fun x : E => (c, x))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ => ⟨hc, mem_univ _⟩)
  have hmemc := Complement.InactiveSource.memLp_carrier_source hU (lam i) (φ i c) (a i c)
    hφc hac ((has i c hc).trans hSU)
    (hS.of_isClosed_subset (isClosed_tsupport _) (has i c hc))
  let w : H := hmemc.toLp (fun x => carrier (lam i) (φ i c) x • a i c x)
  have hw : w =ᵐ[volume] fun x => carrier (lam i) (φ i c) x • a i c x := hmemc.coeFn_toLp
  refine ⟨w, hw, ?_⟩
  have hkcont (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') (x : E) :
      Continuous (fun ξ => annularSourceKernelObservation true false
        (elapsedPhase (Ψ i) (t i))
        (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
        π' (φ i c) (lam i) (a i c) x ξ) :=
    (contDiffOn_univ.mp ((hκ i false π' hπ').comp
      (f := fun ξ : E => ((c, x), ξ)) (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ => ⟨⟨hc, mem_univ _⟩, mem_univ _⟩))).continuous
  have hip (x : E) : Integrable (fun ξ => annularSourceKernelObservation true false
      (elapsedPhase (Ψ i) (t i))
      (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i))
      π (φ i c) (lam i) (a i c) x ξ) := by
    apply (hresult.1 i (c, x) ⟨hc, mem_univ _⟩).norm.mono'
      (hkcont π hπ x).aestronglyMeasurable
    filter_upwards [] with ξ
    dsimp only [κ]
    cases demod <;>
      simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
        norm_demodulatedAdjointAnnularSourceKernel,
        le_refl]
  have hphys (x z ξ : E) (hh : x ∉ X₀ ∨ z ∉ X₀) :
      elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i) x z ξ = 0 := by
    rcases hh with hx | hz
    · exact elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _
        (Or.inl (image_eq_zero_of_notMem_tsupport (fun h => hx (hmask i (Or.inl h)))))
    · exact elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _
        (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport
          (fun h => hz (hmask i (Or.inr h))))))
  have hid := annularGraphDifference_ae_of_supported_strong_limit true
    (elapsedPhase (Ψ i) (t i)) (hD i) (hΩ i) (hDΩ i) (hΘ i)
    (elapsedAmplitude (b i) (χout i) (χsource i) (β i) (t i)) (hA i) (hsD i)
    hX₀ hX₀ hphys π (lam i)
    contDiff_const (by change HasCompactSupport (0 : E → ℂ); exact HasCompactSupport.zero)
    (φ i c) (a i c) w hw (hkcont 0 contDiff_const) hip
    (χ i) (hχ i) (hχc i) (hχb i) (hχlim i) (hstrong i w)
  apply (hresult.2.2.2.2.1 i c hc).trans
  filter_upwards [hid] with x hx
  rw [hx]
  dsimp only [κ]
  cases demod <;>
    simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
      demodulatedAdjointAnnularSourceKernel,
      integral_smul, one_smul]


end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
