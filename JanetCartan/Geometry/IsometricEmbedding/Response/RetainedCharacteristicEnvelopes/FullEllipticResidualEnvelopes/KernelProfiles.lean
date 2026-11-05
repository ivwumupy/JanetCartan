module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.FrozenFrequency
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.KernelProfiles

/-!
# Complete diagonal PDO source-kernel profiles

This applies the original nonstationary source estimate at each fixed physical
frequency.  The symbol may depend on the entire covector.  Only its physical
jets enter the source integral, so no transverse-frequency replacement is made.
Consumers are the elliptic, endpoint and algebraic letters of the normalized
mixed residual in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral Pseudodifferential
open DirectEvolution.AnnularComplement
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open JanetCartan.Localization

variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- At each fixed physical frequency, the auxiliary frozen primitives give
the literal complete PDO kernel in both orientations and with either output
observation.  All covector components and physical normalizations are retained
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularSourceKernelObservation_frozenFrequency
    (adj demod : Bool) (σ : E → E → Mat) (χout χsource π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    annularSourceKernelObservation adj demod
      (elapsedPhase (frozenFrequencyDiagonalPhase ξ) 0)
      (elapsedAmplitude (frozenFrequencyDiagonalAmplitude σ ξ)
        χout χsource (fun _ ↦ 1) 0) π φ lam a x ξ =
    annularSourceKernelObservation adj demod (fun y η ↦ inner ℝ y η)
      (fun y z η ↦ (χout y * χsource z) • σ y η) π φ lam a x ξ := by
  simp only [annularSourceKernelObservation_eq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  cases adj <;> simp only [annularSourceIntegrand, Bool.false_eq_true, ↓reduceIte,
    forwardAnnularSourceAmplitude, adjointAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude,
    elapsedAmplitude_frozenFrequencyDiagonalAmplitude,
    phaseOscillation, forwardCarrierSourcePhase, adjointCarrierSourcePhase,
    elapsedPhase_frozenFrequencyDiagonalPhase]

/-- Full-frequency complementary PDO kernel estimates with losses fixed
before the integration-by-parts order.  The source and symbol inputs are the
primitive profiles already supplied by the original construction; there is no
kernel or response estimate among the premises.  This theorem also supplies
the endpoint/algebraic PDO letters of the same finite residual word
(`app:ch_response:lem:energy-carrier-jets`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_complete_diagonal_sourceKernel_profiles
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
      ∀ (a : P → E → F) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (has : ∀ c ∈ V, tsupport (a c) ⊆ S),
        (∀ c (hc : c ∈ V) l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
          MemVectorFourierSobolev (s : ℝ)
            ((parameterSource_memLp hS hV ha has l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) c w))) →
        (∀ c (hc : c ∈ V) l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
          vectorFourierSobolevNorm (s : ℝ)
            ((parameterSource_memLp hS hV ha has l w hc).toLp
              (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a q y) c w)) ≤
                Csource l s * A₀ * K^(s+l)) →
      let π : E → ℂ := fun η ↦ annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) η
      ∀ (adj demod : Bool) (j N : ℕ) (ξ : E) (q : P × E), q.1 ∈ V →
      ∀ v : Fin j → P × E, (∀ k, ‖v k‖ ≤ 1) →
        ‖iteratedFDeriv ℝ j (fun q : P × E ↦
          annularSourceKernelObservation adj demod (fun y η ↦ inner ℝ y η)
            (fun y z η ↦ (χout y * χsource z) • σ y η)
            π (φ q.1) lam (a q.1) q.2 ξ) q v‖ ≤
          Ckernel j N * (A₀ * (lam+‖ξ‖)^j * K^(d+1+1+j) *
            (K/(lam+‖ξ‖))^N) := by
  obtain ⟨R,hR,hRbound⟩ := (hS.union hX₀).isBounded.exists_pos_norm_le
  let O : ℕ → ℝ := fun k ↦ cNorm (S ∪ X₀) k χout
  let T : ℕ → ℝ := fun k ↦ cNorm (S ∪ X₀) k χsource
  let B : ℕ → ℝ := fun k ↦ Bsymbol k * ‖frozenFrequencyPosition (d := d)‖^k
  have hO (k : ℕ) : 0 ≤ O k := cNorm_nonneg ..
  have hT (k : ℕ) : 0 ≤ T k := cNorm_nonneg ..
  have hB (k : ℕ) : 0 ≤ B k := mul_nonneg (hBsymbol k) (pow_nonneg (norm_nonneg _) _)
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := exists_originalAnnularSourceKernel_profile
    (d := d) (r := r) V hX₀ hS (Δ := 0) le_rfl hν hν1 ha₀ hB₀
    (m := 1) (M := 1) zero_lt_one le_rfl le_rfl
    Pphase (fun _ ↦ 0) hPphase (fun _ ↦ le_rfl)
    (fun _ ↦ R+1) Bphase O T B Csource 1
    (fun _ ↦ by linarith) hBphase hO hT hB zero_le_one
  refine ⟨Ckernel,hCkernel,?_⟩
  intro lam L K A₀ hlam hL hLK hscale hA₀ σ hσ hσjets φ hφ hφjets
    U X hU hX hSU hXX hgradient hsourceφ a ha has hmem hsob π adj demod j N ξ q hq v hv
  let Ψ := frozenFrequencyDiagonalPhase ξ
  let b := frozenFrequencyDiagonalAmplitude σ ξ
  have hΨ : ContDiff ℝ ∞ (jointPhase Ψ) :=
    contDiff_jointPhase_frozenFrequencyDiagonalPhase ξ
  have hb : ContDiff ℝ ∞ (jointAmplitude b) :=
    contDiff_jointAmplitude_frozenFrequencyDiagonalAmplitude σ hσ ξ
  have hΨjets (k : ℕ) (y : E) (hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (jointPhase Ψ) (elapsedPoint 0 ((y, 0), ξ))‖ ≤
        (R+1) * (1+‖ξ‖) * L^k := by
    exact (norm_jet_jointPhase_frozenFrequencyDiagonalPhase hR.le ξ y (hRbound y hy) k).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL))
  have hbjets (k : ℕ) (y : E) (hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (jointAmplitude b) (elapsedPoint 0 ((y, 0), ξ))‖ ≤ B k * L^k := by
    have hp := norm_jet_jointAmplitude_frozenFrequencyDiagonalAmplitude σ hσ ξ
      (elapsedPoint 0 ((y, 0), ξ)) k
    rw [frozenFrequencyPosition_elapsed] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_right (hσjets k ξ y hy)
      (pow_nonneg (norm_nonneg _) _)).trans_eq (by dsimp only [B]; ring))
  have hradial (y : E) :
      1 * ‖ξ‖ ≤ ‖fderiv ℝ (fun z ↦ elapsedPhase Ψ 0 z ξ) y‖ ∧
        ‖fderiv ℝ (fun z ↦ elapsedPhase Ψ 0 z ξ) y‖ ≤ 1 * ‖ξ‖ := by
    have he : (fun z ↦ elapsedPhase Ψ 0 z ξ) = InnerProductSpace.toDual ℝ E ξ := by
      funext z
      rw [elapsedPhase_frozenFrequencyDiagonalPhase]
      exact real_inner_comm _ _
    rw [he, (InnerProductSpace.toDual ℝ E ξ).hasFDerivAt.fderiv]
    simp
  have he : (fun q : P × E ↦ annularSourceKernelObservation adj demod
      (elapsedPhase Ψ 0) (elapsedAmplitude b χout χsource (fun _ ↦ 1) 0)
        π (φ q.1) lam (a q.1) q.2 ξ) =
      fun q : P × E ↦ annularSourceKernelObservation adj demod (fun y η ↦ inner ℝ y η)
        (fun y z η ↦ (χout y * χsource z) • σ y η)
          π (φ q.1) lam (a q.1) q.2 ξ := by
    funext q
    exact annularSourceKernelObservation_frozenFrequency adj demod σ χout χsource π
      (φ q.1) lam (a q.1) q.2 ξ
  have hk := hkernel j N lam L K 0 A₀ hlam hL hLK hscale ⟨le_rfl,le_rfl⟩ hA₀
    ξ Ψ b χout χsource (fun _ ↦ 1) π φ V U X univ univ hV hU hX
    isOpen_univ isOpen_univ (Subset.refl _) hSU hXX a ha has
    (by simp only [π,mul_one,div_one]) hmask ho hs (by simp)
    (fun _ ↦ hΨ.contDiffOn) (fun _ ↦ hb.contDiffOn) (by intros; trivial)
    (by intros; trivial) (fun _ ↦ hφ.contDiffOn) (fun _ ↦ hΨjets)
    (fun _ ↦ hφjets) (fun _ ↦ hbjets)
    (fun k y hy ↦ norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (ho.of_le (by simp)) hy le_rfl)
    (fun k y hy ↦ norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (hs.of_le (by simp)) hy le_rfl)
    (fun c hc _ l _ w hw s ↦ hmem c hc l w hw s)
    (fun c hc _ l _ w hw s ↦ hsob c hc l w hw s)
    (fun _ ↦ hgradient) (fun _ y _ ↦ hradial y) (fun _ ↦ hsourceφ)
    (fun _ y _ k hk ↦ by
      rw [norm_higher_jet_jointPhase_frozenFrequencyDiagonalPhase ξ _ hk]
      simp)
    adj demod v hv q hq
  simpa only [he] using hk

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
