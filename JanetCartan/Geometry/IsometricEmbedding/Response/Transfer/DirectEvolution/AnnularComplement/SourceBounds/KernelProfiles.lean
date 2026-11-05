module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.JetIntegration

/-!
# Uniform literal annular kernel jets from original primitives

The fixed losses for external joint order `j` are `(d_j, ell_j, b_j, s_j) =
(0, 0, n+1+j, j)`, where `n = d+1`. Integration order `N` changes only the
constant and the gain `(K/(λ+‖ξ‖))^N`. Both masks, beta, the normalized
selector, Fourier normalization, and all output-demodulator derivatives are
retained. The source radial comparison is the actual supported geometric
input supplied by the compatible-phase/sector parent.

Consumer: the complete annular complement and its independent kernel Sobolev
deduction. Sources: `app:ch_response:lem:energy-carrier-jets`,
`app:ch_response:eq:direct-envelope-profile` and the fixed-factor transfer.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open AmplitudeJets Complement.ParameterDerivatives Complement.InactiveSource
open JanetCartan.Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The literal differentiated source kernels obey an arbitrary-order
nonstationary profile with losses fixed before `N`. All constants precede
the scales, elapsed time, frequency, carrier parameters and envelope data.
Only envelope parameter orders through `j` occur, regardless of `N`.

All analytic premises are original phase/symbol/mask/envelope profiles or
the precise supported carrier-gradient and elapsed radial comparison. The
source phase grades are derived from original two-time jets by the affine
elapsed pullback. The normalized amplitude bounds and integral interchange
are discharged, rather than assumed. Both orientations, both observations,
all annular shoulders, bounded frequencies and the unbounded tail are
included. Bounds hold at every output point using the original masks.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem exists_originalAnnularSourceKernel_profile
    (P₀ : Set P) {X₀ S : Set E} (hX₀ : IsCompact X₀) (hS : IsCompact S)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    {a₀ B₀ m M : ℝ} (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    (Pφ PΨ : ℕ → ℝ) (hPφ : ∀ k, 0 ≤ Pφ k) (hPΨ : ∀ k, 0 ≤ PΨ k)
    (BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hBΨ : ∀ m, 0 ≤ BΨ m) (hBφ : ∀ m, 0 ≤ Bφ m)
    (hO : ∀ m, 0 ≤ O m) (hT : ∀ m, 0 ≤ T m) (hB : ∀ m, 0 ≤ B m)
    (hMβ : 0 ≤ Mβ) :
    ∃ Ckernel : ℕ → ℕ → ℝ, (∀ j N, 0 ≤ Ckernel j N) ∧
      ∀ (j N : ℕ) (lam L K t A₀ : ℝ),
      1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam ^ (1 - ν) → t ∈ Icc 0 Δ → 0 ≤ A₀ →
      ∀ (ξ : E) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
        (χout χsource β π : E → ℂ) (φ : P → E → ℝ)
        (V : Set P) (U X : Set E) (OΨ Ob : Set (TwoTimePoint d))
        (hV : IsOpen V) (_hU : IsOpen U) (_hX : IsOpen X)
        (_hOΨ : IsOpen OΨ) (_hOb : IsOpen Ob)
        (_hPV : P₀ ⊆ V) (_hSU : S ⊆ U) (_hXX : X₀ ⊆ X)
        (a : P → E → F) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (has : ∀ c ∈ V, tsupport (a c) ⊆ S),
      π = (fun η => (annularSelector (a₀ / (2 * M)) (2 * B₀ / m)
        (by positivity) (by positivity) η : ℂ)) →
      tsupport χout ∪ tsupport χsource ⊆ X₀ →
      ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource →
      ‖β ξ‖ ≤ Mβ →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointPhase Ψ) OΨ) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointAmplitude b) Ob) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ OΨ) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y, 0), ξ) ∈ Ob) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X))) →
      (β ξ ≠ 0 → ∀ m y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ m (jointPhase Ψ) (elapsedPoint t ((y, 0), ξ))‖ ≤
          BΨ m * (1 + ‖ξ‖) * L ^ m) →
      (β ξ ≠ 0 → ∀ m c, c ∈ P₀ → ∀ y ∈ S ∪ X₀,
        ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, y)‖ ≤ Bφ m * L ^ m) →
      (β ξ ≠ 0 → ∀ m y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ m (jointAmplitude b) (elapsedPoint t ((y, 0), ξ))‖ ≤
          B m * L ^ m) →
      (∀ m y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ m χout y‖ ≤ O m) →
      (∀ m y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ m χsource y‖ ≤ T m) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ →
        ∀ l ≤ j, ∀ w : Fin l → P, (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        MemVectorFourierSobolev (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y => iteratedFDeriv ℝ l (fun q => a q y) c w))) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ →
        ∀ l ≤ j, ∀ w : Fin l → P, (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        vectorFourierSobolevNorm (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y => iteratedFDeriv ℝ l (fun q => a q y) c w)) ≤
              C l s * A₀ * K ^ (s + l)) →
      (β ξ ≠ 0 → ∀ c ∈ P₀, ∀ z ∈ U,
        a₀ ≤ ‖fderiv ℝ (φ c) z‖ ∧ ‖fderiv ℝ (φ c) z‖ ≤ B₀) →
      (β ξ ≠ 0 → ∀ z ∈ U,
        m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => elapsedPhase Ψ t y ξ) z‖ ∧
          ‖fderiv ℝ (fun y => elapsedPhase Ψ t y ξ) z‖ ≤ M * ‖ξ‖) →
      (β ξ ≠ 0 → ∀ c ∈ P₀, ∀ z ∈ S, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ (k + 1) (φ c) z‖ ≤ Pφ k * L ^ k) →
      (β ξ ≠ 0 → ∀ z ∈ S, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ (k + 1) (jointPhase Ψ) (elapsedPoint t ((z, 0), ξ))‖ ≤
          PΨ k * (1 + ‖ξ‖) * L ^ k) →
      ∀ (adj demod : Bool) (v : Fin j → P × E), (∀ i, ‖v i‖ ≤ 1) →
      ∀ q : P × E, q.1 ∈ P₀ →
        ‖iteratedFDeriv ℝ j (fun q : P × E =>
          annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
            (elapsedAmplitude b χout χsource β t) π (φ q.1) lam (a q.1) q.2 ξ) q v‖ ≤
          Ckernel j N * ((A₀ * (lam + ‖ξ‖) ^ j * K ^ (d + 1 + 1 + j)) *
            (K / (lam + ‖ξ‖)) ^ N) := by
  obtain ⟨D, hD, hprofile⟩ := exists_originalAnnularExternalJet_profile
    P₀ hX₀ hS hΔ hν hν1 BΨ Bφ O T B C Mβ 1
    hBΨ hBφ hO hT hB hMβ zero_le_one
  let Ckernel : ℕ → ℕ → ℝ := fun j N =>
    annularSourceKernelConstant (d + 1) S (JanetCartan.Localization.radialGapConstant a₀ B₀ * m)
      (B₀ + M) (fun k => Pφ k + PΨ k) (D j) N
  have hCkernel : ∀ j N, 0 ≤ Ckernel j N := fun j N =>
    annularSourceKernelConstant_nonneg S _ _ _ (D j) (hD j) N
  refine ⟨Ckernel, hCkernel, ?_⟩
  intro j N lam L K t A₀ hlam hL hLK hscale ht hA ξ Ψ b χout χsource β π φ
    V U X OΨ Ob hV hU hX hOΨ hOb hPV hSU hXX a ha has hπ hmask ho hs hβξ
    hΨ hb hmapΨ hmapb hφ hΨb hφb hbb hout hsource hmem hsob
    hgradient hradial hsourceφ hsourceΨ adj demod v hv q hq
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hrhs : 0 ≤ Ckernel j N * ((A₀ * (lam + ‖ξ‖) ^ j * K ^ (d + 1 + 1 + j)) *
      (K / (lam + ‖ξ‖)) ^ N) := by
    exact mul_nonneg (hCkernel j N) (by positivity)
  by_cases hx : q.2 ∈ X₀
  swap
  · have hsupport := tsupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation_subset
      adj demod Ψ b χout χsource β π φ t lam a j v q.1 ξ
    have hmask' : tsupport (if adj then χsource else χout) ⊆ X₀ := by
      cases adj
      · exact (subset_union_left.trans hmask)
      · exact (subset_union_right.trans hmask)
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hmask' (hsupport h)))
    change iteratedFDeriv ℝ j (fun q : P × E =>
      annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π (φ q.1) lam (a q.1) q.2 ξ) q v = 0 at hz
    rw [hz, norm_zero]
    exact hrhs
  by_cases hβ : β ξ = 0
  · have he : (fun q : P × E => annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π (φ q.1) lam (a q.1) q.2 ξ) = 0 := by
      funext w
      apply annularSourceKernelObservation_eq_zero_of_amplitude
      intro z
      cases adj <;> simp [elapsedAmplitude, hβ]
    rw [he]
    simpa using hrhs
  by_cases hplateau : π (lam⁻¹ • ξ) = 1
  · have he : (fun q : P × E => annularSourceKernelObservation adj demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π (φ q.1) lam (a q.1) q.2 ξ) = 0 := by
      funext w
      cases adj <;> cases demod <;>
        simp [annularSourceKernelObservation, demodulatedForwardAnnularSourceKernel,
          demodulatedAdjointAnnularSourceKernel,
          forwardAnnularSourceKernel_eq_zero_of_selector_eq_one _ _ π _ lam _ _ ξ hplateau,
          adjointAnnularSourceKernel_eq_zero_of_selector_eq_one _ _ π _ lam _ _ ξ hplateau]
    rw [he]
    simpa using hrhs
  have hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ 1 := by
    rw [hπ]
    exact norm_physicalAnnularSelector_le_one _ _ _ _ lam ξ
  have hj := hprofile j lam L K t A₀ hlam hL hLK hscale ht hA ξ Ψ b χout χsource β π φ
    V U X OΨ Ob hV hU hX hOΨ hOb hPV hSU hXX a ha has ho hs hβξ hπξ
    hΨ hb hmapΨ hmapb hφ hΨb hφb hbb hout hsource hmem hsob adj demod v hv q ⟨hq, hx⟩
  have hΘ := AmplitudeJets.PhaseProfiles.contDiffOn_elapsedPhase_fixedFrequency
    Ψ (hΨ hβ) t ξ (hmapΨ hβ)
  have hψ := contDiffOn_annularExternalPhase adj demod (elapsedPhase Ψ t) φ lam ξ hΘ (hφ hβ)
  have hmatrixMap : ∀ w ∈ X ×ˢ U,
      elapsedPoint t ((if adj then w.swap else w), ξ) ∈ Ob := by
    intro w hw
    cases adj
    · simpa only [Bool.false_eq_true, ite_false, elapsedPoint_eq] using
        hmapb hβ w.1 (Or.inr hw.1)
    · simpa only [ite_true, elapsedPoint_eq, Prod.fst_swap] using
        hmapb hβ w.2 (Or.inl hw.2)
  have hu := contDiffOn_originalAnnularExternalAmplitude adj b χout χsource β π
    t lam ξ (hb hβ) ho hs hmatrixMap ha
  rw [iteratedFDeriv_annularSourceKernelObservation_sourceNeighborhood
    adj demod (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) π φ lam a ξ
    hV hX hU hS hSU hψ hu has j v q ⟨hPV hq, hXX hx⟩]
  apply norm_annularExternalJet_sourceIntegral_le hU hS hSU adj demod
    (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) π φ a q ξ j N v
    ha₀ hB₀ hm hm1 hM1 hlam0 hL0 hLK (by positivity)
    ((hφ hβ).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hPV hq, Or.inl hz⟩)) (hΘ.mono subset_union_left)
    (fun z hz => (hgradient hβ q.1 hq z hz).1)
    (fun z hz => (hgradient hβ q.1 hq z hz).2)
    (fun z hz => (hradial hβ z hz).1) (fun z hz => (hradial hβ z hz).2)
    (by
      intro hz
      apply hplateau
      rw [hπ]
      simpa only [Complex.ofReal_one] using congrArg Complex.ofReal (sub_eq_zero.mp hz).symm)
    Pφ PΨ (D j) hPφ hPΨ (hD j) (hsourceφ hβ q.1 hq)
    (fun z hz k hk => (norm_iteratedFDeriv_elapsedPhase_source_le hOΨ Ψ (hΨ hβ) t ξ z
      (hmapΨ hβ z (Or.inl (hSU hz))) k hk).trans ((hsourceΨ hβ z hz k hk).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (add_le_add hlam le_rfl) (hPΨ k)) (pow_nonneg hL0 k)))) hj.1 hj.2.1
  intro z _ k
  simpa only [mul_assoc] using (hj.2.2 k).2 z

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
