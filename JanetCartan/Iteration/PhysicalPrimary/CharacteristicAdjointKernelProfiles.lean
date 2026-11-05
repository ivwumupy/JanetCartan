module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointSourceGap

/-!
# Complete inactive literal-adjoint kernel jets from original primitives

The same physical cutoffs, elapsed amplitude and full source multiplier are
retained. The parameter cutoff supplies an angular source gap; the original
mixed amplitude calculus supplies every normalized external jet. Direct
source integration gives arbitrary gain on the entire frequency space,
without factoring through an unrelated Fourier multiplier.

Consumer: inactive selected retarded solver and residual letters in
`app:ch_response:eq:fixed-factor-transfer`. Both carrier signs use this same
literal-adjoint theorem with their own actual source phase; its transported
graph-momentum gap is never replaced by the forward frequency gap.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential InnerProductSpace
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- All external jets of the complete inactive literal-adjoint source kernel have
fixed polynomial losses and arbitrary source gain. The premises are the
actual unmodified phase/amplitude/mask/source profiles and the dual frequency
gap, whose producer is `exists_full_source_incidence_cutoff_and_gap` followed
by `inactive_adjoint_source_dual_frequency_gap`. No kernel bound is assumed
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem exists_inactive_adjoint_sourceKernel_profile
    (P₀ : Set P) {X₀ S : Set E} (hX₀ : IsCompact X₀) (hS : IsCompact S)
    {Δ ν gap B₀ Mfreq : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1) (hgap : 0 < gap) (hMfreq : 0 ≤ Mfreq)
    (Pφ PΘ : ℕ → ℝ) (hPφ : ∀ k, 0 ≤ Pφ k) (hPΘ : ∀ k, 0 ≤ PΘ k)
    (BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hBΨ : ∀ k, 0 ≤ BΨ k) (hBφ : ∀ k, 0 ≤ Bφ k)
    (hO : ∀ k, 0 ≤ O k) (hT : ∀ k, 0 ≤ T k) (hB : ∀ k, 0 ≤ B k)
    (hMβ : 0 ≤ Mβ) :
    ∃ Ckernel : ℕ → ℕ → ℝ, (∀ j N, 0 ≤ Ckernel j N) ∧
      ∀ (j N : ℕ) (lam L K t A₀ : ℝ),
      1 ≤ lam → 1 ≤ L → L ≤ K → K ≤ lam^(1-ν) → t ∈ Icc 0 Δ → 0 ≤ A₀ →
      ∀ (ξ : E) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
        (χout χsource β : E → ℂ) (φ : P → E → ℝ)
        (V : Set P) (U X : Set E) (OΨ Ob : Set (TwoTimePoint d))
        (hV : IsOpen V), IsOpen U → IsOpen X → IsOpen OΨ → IsOpen Ob →
      P₀ ⊆ V → S ⊆ U → X₀ ⊆ X →
      ∀ (a : P → E → F) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (has : ∀ c ∈ V, tsupport (a c) ⊆ S),
      tsupport χout ∪ tsupport χsource ⊆ X₀ →
      ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource → ‖β ξ‖ ≤ Mβ →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointPhase Ψ) OΨ) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (jointAmplitude b) Ob) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y,0),ξ) ∈ OΨ) →
      (β ξ ≠ 0 → ∀ y ∈ U ∪ X, elapsedPoint t ((y,0),ξ) ∈ Ob) →
      (β ξ ≠ 0 → ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ (U ∪ X))) →
      (β ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ k (jointPhase Ψ) (elapsedPoint t ((y,0),ξ))‖ ≤
          BΨ k*(1+‖ξ‖)*L^k) →
      (β ξ ≠ 0 → ∀ k c, c ∈ P₀ → ∀ y ∈ S ∪ X₀,
        ‖iteratedFDeriv ℝ k (Function.uncurry φ) (c,y)‖ ≤ Bφ k*L^k) →
      (β ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
        ‖iteratedFDeriv ℝ k (jointAmplitude b) (elapsedPoint t ((y,0),ξ))‖ ≤ B k*L^k) →
      (∀ k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k χout y‖ ≤ O k) →
      (∀ k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k χsource y‖ ≤ T k) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ → ∀ l ≤ j, ∀ w : Fin l → P,
        (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        MemVectorFourierSobolev (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) c w))) →
      (∀ (c : P) (hc : c ∈ V), c ∈ P₀ → ∀ l ≤ j, ∀ w : Fin l → P,
        (∀ i, ‖w i‖ ≤ 1) → ∀ s : ℕ,
        vectorFourierSobolevNorm (s : ℝ)
          ((parameterSource_memLp hS hV ha has l w hc).toLp
            (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) c w)) ≤ C l s*A₀*K^(s+l)) →
      (β ξ ≠ 0 → ∀ c ∈ P₀, ∀ z ∈ U, ‖fderiv ℝ (φ c) z‖ ≤ B₀) →
       (β ξ ≠ 0 → ∀ z ∈ U, ‖fderiv ℝ (fun y ↦ elapsedPhase Ψ t y ξ) z‖ ≤ Mfreq*‖ξ‖) →
      (β ξ ≠ 0 → ∀ c ∈ P₀, ∀ z ∈ U,
        gap*(lam+‖ξ‖) ≤ ‖lam • fderiv ℝ (φ c) z-fderiv ℝ (fun y ↦ elapsedPhase Ψ t y ξ) z‖) →
      (β ξ ≠ 0 → ∀ c ∈ P₀, ∀ z ∈ S, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ (k+1) (φ c) z‖ ≤ Pφ k*L^k) →
       (β ξ ≠ 0 → ∀ z ∈ S, ∀ k, 1 ≤ k →
         ‖iteratedFDeriv ℝ (k+1) (fun y ↦ elapsedPhase Ψ t y ξ) z‖ ≤ PΘ k*‖ξ‖*L^k) →
      ∀ (demod : Bool) (v : Fin j → P × E), (∀ i, ‖v i‖ ≤ 1) →
      ∀ q : P × E, q.1 ∈ P₀ →
        ‖iteratedFDeriv ℝ j (fun q : P × E ↦
          annularSourceKernelObservation true demod (elapsedPhase Ψ t)
            (elapsedAmplitude b χout χsource β t) 0 (φ q.1) lam (a q.1) q.2 ξ) q v‖ ≤
          Ckernel j N*((A₀*(lam+‖ξ‖)^j*K^(d+1+1+j))*(K/(lam+‖ξ‖))^N) := by
  obtain ⟨D,hD,hprofile⟩ := exists_originalAnnularExternalJet_profile
    P₀ hX₀ hS hΔ hν hν1 BΨ Bφ O T B C Mβ 0
    hBΨ hBφ hO hT hB hMβ le_rfl
  let Ckernel : ℕ → ℕ → ℝ := fun j N ↦
    annularSourceKernelConstant (d+1) S gap (B₀+Mfreq) (fun k ↦ Pφ k+PΘ k) (D j) N
  have hCkernel j N : 0 ≤ Ckernel j N := annularSourceKernelConstant_nonneg S _ _ _ (D j) (hD j) N
  refine ⟨Ckernel,hCkernel,?_⟩
  intro j N lam L K t A₀ hlam hL hLK hscale ht hA ξ Ψ b χout χsource β φ
    V U X OΨ Ob hV hU hX hOΨ hOb hPV hSU hXX a ha has hmask ho hs hβξ
    hΨ hb hmapΨ hmapb hφ hΨb hφb hbb hout hsource hmem hsob hupper hupperΘ hfrequency hsourceφ hsourceΘ
    demod v hv q hq
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hrhs : 0 ≤ Ckernel j N*((A₀*(lam+‖ξ‖)^j*K^(d+1+1+j))*(K/(lam+‖ξ‖))^N) :=
    mul_nonneg (hCkernel j N) (by positivity)
  by_cases hx : q.2 ∈ X₀
  swap
  · have hsupport := tsupport_iteratedFDeriv_elapsedAnnularSourceKernelObservation_subset
      true demod Ψ b χout χsource β 0 φ t lam a j v q.1 ξ
    have hz := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (hmask (Or.inr (hsupport h))))
    change iteratedFDeriv ℝ j (fun q : P × E ↦
      annularSourceKernelObservation true demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) 0 (φ q.1) lam (a q.1) q.2 ξ) q v = 0 at hz
    rw [hz,norm_zero]
    exact hrhs
  by_cases hβ : β ξ = 0
  · have he : (fun q : P × E ↦ annularSourceKernelObservation true demod (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) 0 (φ q.1) lam (a q.1) q.2 ξ) = 0 := by
      funext w
      apply annularSourceKernelObservation_eq_zero_of_amplitude
      intro z
      simp [elapsedAmplitude,hβ]
    rw [he]
    simpa using hrhs
  have hj := hprofile j lam L K t A₀ hlam hL hLK hscale ht hA ξ Ψ b χout χsource β 0 φ
    V U X OΨ Ob hV hU hX hOΨ hOb hPV hSU hXX a ha has ho hs hβξ (by simp)
    hΨ hb hmapΨ hmapb hφ hΨb hφb hbb hout hsource hmem hsob true demod v hv q ⟨hq,hx⟩
  have hΘ := AmplitudeJets.PhaseProfiles.contDiffOn_elapsedPhase_fixedFrequency
    Ψ (hΨ hβ) t ξ (hmapΨ hβ)
  have hψ := contDiffOn_annularExternalPhase true demod (elapsedPhase Ψ t) φ lam ξ hΘ (hφ hβ)
  have hmatrixMap : ∀ w ∈ X ×ˢ U, elapsedPoint t ((w.2,w.1),ξ) ∈ Ob := by
    intro w hw
    simpa only [elapsedPoint_eq] using hmapb hβ w.2 (Or.inl hw.2)
  have hu := contDiffOn_originalAnnularExternalAmplitude true b χout χsource β 0
    t lam ξ (hb hβ) ho hs hmatrixMap ha
  rw [iteratedFDeriv_annularSourceKernelObservation_sourceNeighborhood
    true demod (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) 0 φ lam a ξ
    hV hX hU hS hSU hψ hu has j v q ⟨hPV hq,hXX hx⟩]
  apply norm_inactive_adjoint_externalJet_sourceIntegral_le hU hS hSU demod
    (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) φ a q ξ j N v
    hgap hMfreq hlam0 hL0 hLK (by positivity)
    ((hφ hβ).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz ↦ ⟨hPV hq,Or.inl hz⟩))
    (hΘ.mono subset_union_left) (hupper hβ q.1 hq) (hupperΘ hβ)
    (hfrequency hβ q.1 hq) Pφ PΘ (D j) hPφ hPΘ (hD j)
    (hsourceφ hβ q.1 hq) (hsourceΘ hβ) hj.1 hj.2.1
  intro z _ k
  simpa only [mul_assoc] using (hj.2.2 k).2 z

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
