module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.KernelCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.OperatorIdentification
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Regularizations

/-!
# Complete complementary frequency integration for diagonal PDOs

The complete symbol is retained in the original source integral. Its physical
jets give arbitrary complementary Sobolev precision. The original normal
certificate identifies this integral with the SAME bounded PDO minus its
annular part, in both orientations. The concrete consumers are the elliptic,
endpoint and algebraic residual letters in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds
open FourierIntegral.LowBounds.FrequencyCutoff
open Pseudodifferential CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.PdoRealization
open ArbitraryAccuracy.ResidualLocalization
open DirectEvolution.AnnularComplement
open Complement.ParameterDerivatives Complement.ParameterDerivatives.Hilbert
variable {p d r : ℕ} {I : Type} {Par : Type}
  [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par]
local notation "P" => Par
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp F 2 (volume : Measure E)

/-- Literal L² realization of the complementary kernel for the complete
diagonal symbol (`app:ch_response:lem:energy-carrier-jets`). -/
def completeDiagonalAnnularRemainder {X₀ : Set E} (hX₀ : IsCompact X₀) [CompactSpace X₀]
    (adj demod : Bool) (σ : E → E → Mat) (χout χsource π : E → ℂ)
    (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F) :=
  compactVectorL2Family hX₀ (fun c x ↦ ∫ ξ,
    annularSourceKernelObservation adj demod (fun y η ↦ inner ℝ y η)
      (fun y z η ↦ (χout y * χsource z) • σ y η) π (φ c) lam (a c) x ξ)

/-- Complete complementary PDO estimates from original symbol and source
profiles, with the exact SAME bounded-operator identity supplied by its normal
certificate. The profile losses are fixed before arbitrary integration order.
Consumer: full elliptic/endpoint/algebraic one-letter envelope estimates in
`app:ch_response:eq:response-graded-reduced`. -/
theorem completeDiagonalAnnularComplement_sobolev
    (e : Euclidean p ≃L[ℝ] Par) (he : ∀ z, ‖e z‖ ≤ ‖z‖)
    {V : Set P} (hV : IsOpen V) {X₀ S : Set E}
    (hX₀ : IsCompact X₀) [CompactSpace X₀] (hS : IsCompact S)
    {U X : Set E} (hU : IsOpen U) (hX : IsOpen X) (hSU : S ⊆ U) (hXX : X₀ ⊆ X)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (Bsymbol Bphase Pphase : ℕ → ℝ) (Csource : ℕ → ℕ → ℝ)
    (hBsymbol : ∀ k, 0 ≤ Bsymbol k) (hBphase : ∀ k, 0 ≤ Bphase k)
    (hPphase : ∀ k, 0 ≤ Pphase k)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (σ : I → E → E → Mat) (φ : I → P → E → ℝ) (a : I → P → E → F)
    (hσ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (σ i)))
    (hσjets : ∀ i k ξ y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (fun z ↦ σ i z ξ) y‖ ≤ Bsymbol k * L i ^ k)
    (hnormal : ∀ i, ∃ R M,
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource (σ i)) R M)
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hφjets : ∀ i k c, c ∈ V → ∀ y ∈ S ∪ X₀,
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) (c,y)‖ ≤ Bphase k * L i ^ k)
    (hgradient : ∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hsourceφ : ∀ i c, c ∈ V → ∀ y ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (φ i c) y‖ ≤ Pphase k * L i ^ k)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w
      ∃ hm : MemLp f 2 volume,
        MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * A₀ i * K i ^ (s+l))
    (adj demod : Bool) :
    let π : E → ℂ := fun η ↦
      annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) η
    let κ := fun i ξ (q : P × E) ↦ annularSourceKernelObservation adj demod
      (fun y η ↦ inner ℝ y η) (fun y z η ↦ (χout y * χsource z) • σ i y η)
        π (φ i q.1) (lam i) (a i q.1) q.2 ξ
    let R := fun i ↦ completeDiagonalAnnularRemainder hX₀ adj demod (σ i)
      χout χsource π (φ i) (lam i) (a i)
    let Tfull := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO χout χsource (σ i))
    let Tcut := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO χout χsource
      (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σ i y ξ))
    (∀ i q, q ∈ V ×ˢ univ → Integrable (fun ξ ↦ κ i ξ q)) ∧
    (∀ i, ContDiffOn ℝ ∞ (R i) V) ∧
    (∀ i c, c ∈ V → R i c =ᵐ[volume] fun x ↦ ∫ ξ, κ i ξ (c,x)) ∧
    (∀ i k (v : Fin k → P) c, c ∈ V →
      iteratedFDeriv ℝ k (R i) c v =ᵐ[volume]
        fun x ↦ ∫ ξ, iteratedFDeriv ℝ k (fun q ↦ κ i ξ (q,x)) c v) ∧
    (∀ i c, c ∈ V → ∃ w : H,
      w =ᵐ[volume] (fun x ↦ carrier (lam i) (φ i c) x • a i c x) ∧
      R i c =ᵐ[volume] fun x ↦ (if demod then carrier (-lam i) (φ i c) x else 1) •
        ((Tfull i w - Tcut i w) x)) ∧
    ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
      MemVectorFourierSobolev s (iteratedFDeriv ℝ k (R i) c v) ∧
      vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (R i) c v) ≤
        Csob * A₀ i * lam i ^ (-Q) := by
  dsimp only
  let π : E → ℂ := fun η ↦
    annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) η
  let A : I → FullAmplitude (d+1) r := fun i y z η ↦ (χout y * χsource z) • σ i y η
  let κ := fun i ξ (q : P × E) ↦ annularSourceKernelObservation adj demod
    (fun y η ↦ inner ℝ y η) (A i) π (φ i q.1) (lam i) (a i q.1) q.2 ξ
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp
    (contDiff_annularSelector _ _ _ _)
  have hA (i : I) : ContDiff ℝ ∞ (fun q : E × E × E ↦ A i q.1 q.2.1 q.2.2) :=
    ((ho.comp contDiff_fst).mul (hs.comp contDiff_snd.fst)).smul
      ((hσ i).comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hΘ : ContDiff ℝ ∞ (Function.uncurry (fun y η : E ↦ inner ℝ y η)) :=
    contDiff_fst.inner ℝ contDiff_snd
  have hzero (i : I) (x : E) (hx : x ∉ X₀) (z ξ : E) :
      (if adj then A i z x ξ else A i x z ξ) = 0 := by
    cases adj
    · have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inl h)))
      simp only [Bool.false_eq_true, ↓reduceIte, A, hz, zero_mul, zero_smul]
    · have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inr h)))
      simp only [↓reduceIte, A, hz, mul_zero, zero_smul]
  have hJ (i : I) (dm : Bool) (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') :=
    contDiffOn_annularSourceIntegrand_localCarrierPhase adj dm
      (fun y η ↦ inner ℝ y η) (A i) π' (φ i) (lam i) (a i) hV
      isClosed_univ isOpen_univ (Subset.refl univ) hΘ.contDiffOn
      (fun _ _ _ _ ↦ mem_univ _)
      (fun k l ↦ (AmplitudeBound.matrixEntryEvaluation k l).contDiff.comp (hA i)) hπ'
      (hU.union hX) hX₀.isClosed hS.isClosed
      (fun _ h ↦ Or.inr (hXX h)) (fun _ h ↦ Or.inl (hSU h))
      (hφ i).contDiffOn (ha i) (has i) (hzero i)
  have hκ (i : I) (dm : Bool) (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') :=
    contDiffOn_annularSourceKernelObservation_of_joint adj dm
      (fun y η ↦ inner ℝ y η) (A i) π' (φ i) (lam i) (a i) hV
      (hJ i dm π' hπ') hS (has i)
  have hκξ (i : I) (ξ : E) : ContDiffOn ℝ ∞ (κ i ξ) (V ×ˢ univ) :=
    (hκ i demod π hπ).comp (f := fun q : P × E ↦ (q,ξ))
      (contDiffOn_id.prodMk contDiffOn_const) (fun q hq ↦ ⟨hq,mem_univ ξ⟩)
  have hmeas (i : I) (q : P × E) (hq : q ∈ V ×ˢ univ) :
      AEStronglyMeasurable (fun ξ ↦ κ i ξ q) volume :=
    (contDiffOn_univ.mp ((hκ i demod π hπ).comp (f := fun ξ : E ↦ (q,ξ))
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun ξ _ ↦ ⟨hq,mem_univ ξ⟩))).continuous.aestronglyMeasurable
  obtain ⟨Ckernel,hCkernel,hprofile⟩ := exists_complete_diagonal_sourceKernel_profiles_of_coordinates
    e he hV hS hX₀ χout χsource ho hs hmask hν hν1 ha₀ hB₀
    Bsymbol Bphase Pphase Csource hBsymbol hBphase hPphase
  have hbound (j N : ℕ) (i : I) (ξ : E) (q : P × E) (hq : q ∈ V ×ˢ univ)
      (v : Fin j → P × E) (hv : ∀ k, ‖v k‖ ≤ 1) :=
    hprofile (lam i) (L i) (K i) (A₀ i) (hlam i) (hL i) (hLK i) (hscale i)
      (hA₀ i) (σ i) (hσ i) (hσjets i) (φ i) (hφ i) (hφjets i)
      U X hU hX hSU hXX (hgradient i) (hsourceφ i) (a i) (ha i) (has i)
      (hfourier i) adj demod j N ξ q hq.1 v hv
  have hresult := annularKernel_sobolev_realization hV hX₀ κ hκξ hmeas
    (fun i ξ c _ x hx ↦ annularSourceKernelObservation_eq_zero_of_amplitude
      adj demod _ _ π (φ i c) (lam i) (a i c) x ξ (fun z ↦ hzero i x hx z ξ))
    (fun _ ↦ 0) (fun j ↦ j) (fun _ ↦ 0) (fun j ↦ d+1+1+j)
    Ckernel hCkernel hν hν1 lam L K A₀ hlam hL hLK hscale hA₀ (by
      intro j N i ξ q hq v hv
      apply (hbound j N i ξ q hq v hv).trans_eq
      simp only [Real.rpow_zero, pow_zero, mul_one]
      ring)
  refine ⟨hresult.1, hresult.2.2.2.1, hresult.2.2.2.2.1,
    hresult.2.2.2.2.2.1, ?_, hresult.2.2.2.2.2.2⟩
  intro i c hc
  have hφc : ContDiffOn ℝ ∞ (φ i c) U :=
    ((hφ i).comp (contDiff_const.prodMk contDiff_id)).contDiffOn
  have hac : ContDiffOn ℝ ∞ (a i c) U :=
    (ha i).comp (f := fun x : E ↦ (c,x))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ ↦ ⟨hc,mem_univ _⟩)
  have hmemc := Complement.InactiveSource.memLp_carrier_source hU (lam i) (φ i c) (a i c)
    hφc hac ((has i c hc).trans hSU)
    (hS.of_isClosed_subset (isClosed_tsupport _) (has i c hc))
  let w : H := hmemc.toLp (fun x ↦ carrier (lam i) (φ i c) x • a i c x)
  have hw : w =ᵐ[volume] fun x ↦ carrier (lam i) (φ i c) x • a i c x := hmemc.coeFn_toLp
  refine ⟨w,hw,?_⟩
  have hkcont (π' : E → ℂ) (hπ' : ContDiff ℝ ∞ π') (x : E) :
      Continuous (fun ξ ↦ annularSourceKernelObservation adj false
        (fun y η ↦ inner ℝ y η) (A i) π' (φ i c) (lam i) (a i c) x ξ) :=
    (contDiffOn_univ.mp ((hκ i false π' hπ').comp
      (f := fun ξ : E ↦ ((c,x),ξ)) (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ _ ↦ ⟨⟨hc,mem_univ _⟩,mem_univ _⟩))).continuous
  have hip (x : E) : Integrable (fun ξ ↦ annularSourceKernelObservation adj false
      (fun y η ↦ inner ℝ y η) (A i) π (φ i c) (lam i) (a i c) x ξ) := by
    apply (hresult.1 i (c,x) ⟨hc,mem_univ _⟩).norm.mono'
      (hkcont π hπ x).aestronglyMeasurable
    filter_upwards [] with ξ
    dsimp only [κ]
    cases adj <;> cases demod <;>
      simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
        norm_demodulatedForwardAnnularSourceKernel, norm_demodulatedAdjointAnnularSourceKernel,
        le_refl]
  have hphys (x z ξ : E) (hh : x ∉ X₀ ∨ z ∉ X₀) : A i x z ξ = 0 := by
    rcases hh with hx | hz
    · have he := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inl h)))
      simp only [A,he,zero_mul,zero_smul]
    · have he := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hmask (Or.inr h)))
      simp only [A,he,mul_zero,zero_smul]
  obtain ⟨Rnormal,Mnormal,hcert⟩ := hnormal i
  have hstrong : Tendsto (fun j ↦ annularGraphOrientation adj
      (fullGraphOperator (fun y η : E ↦ inner ℝ y η)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j) (A i))) w) atTop
      (𝓝 (annularGraphOrientation adj (fullGraphOperator (fun y η : E ↦ inner ℝ y η) (A i)) w)) := by
    cases adj
    · exact tendsto_canonicalGraph_frequencyCut (Nat.succ_pos d) (A i) hcert _
        complexPhysicalCutoff_contDiff le_rfl complexPhysicalCutoff_norm_le
        complexPhysicalCutoff_tendsto w
    · exact tendsto_canonicalGraph_frequencyCut_adjoint (Nat.succ_pos d) (A i) hcert _
        complexPhysicalCutoff_contDiff le_rfl complexPhysicalCutoff_norm_le
        complexPhysicalCutoff_tendsto w
  have hid := annularGraphDifference_ae_of_strong_limit adj
    (fun y η : E ↦ inner ℝ y η) hΘ (A i) (hA i) hX₀ hX₀ hphys π (lam i)
    (contDiff_physicalAnnularSelector _ _ _ _ (lam i))
    (hasCompactSupport_physicalAnnularSelector _ _ _ _ (zero_lt_one.trans_le (hlam i)))
    (φ i c) (a i c) w hw (hkcont 0 contDiff_const) hip
    complexPhysicalCutoff complexPhysicalCutoff_contDiff complexPhysicalCutoff_hasCompactSupport
    complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto hstrong
  have hcut : fullGraphOperator (fun y η : E ↦ inner ℝ y η)
      (frequencyCutFullAmplitude (fun ξ ↦ π ((lam i)⁻¹ • ξ)) (A i)) =
      maskedPhysicalPDO χout χsource (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σ i y ξ) := by
    congr 1
    funext y z ξ
    exact smul_comm _ _ _
  rw [hcut] at hid
  change (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (σ i)) w -
      annularGraphOrientation adj (maskedPhysicalPDO χout χsource
        (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σ i y ξ)) w) =ᵐ[volume] _ at hid
  apply (hresult.2.2.2.2.1 i c hc).trans
  filter_upwards [hid] with x hx
  rw [hx]
  dsimp only [κ]
  cases adj <;> cases demod <;>
    simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
      demodulatedForwardAnnularSourceKernel, demodulatedAdjointAnnularSourceKernel,
      integral_smul, one_smul]

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
