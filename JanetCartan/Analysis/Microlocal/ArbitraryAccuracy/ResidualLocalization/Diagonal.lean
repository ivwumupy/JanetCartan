module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.DiagonalPhase
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ActualOperator
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ProducerRealizations

/-!
# Localization of the canonical masked physical PDO

The canonical phase and identity chart discharge all phase and chart premises
of `FiniteChain.Graph`. Primitive symbol/mask grades and finite realizations
then give Fourier membership and leakage for the SAME `maskedPhysicalPDO`,
including its literal Hilbert adjoint. Consumer: the four `directPDOSymbols`
branches in `app:ch_regular_base:eq:energy-complete-residual` and the diagonal
factors of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual
open FiniteChain.Graph KernelLimits CartesianJets PhysicalShells
open KernelEstimates KernelEstimates.NoncomparableGeometry
open PhysicalShells.Comparable PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization EvolutionLocalization.SobolevRealization
open EvolutionIntegratedLocalization Pseudodifferential
open LowBounds.FrequencyCutoff RetardedSobolev.Spaces AmplitudeBound
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => SpacetimeL2 d q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 256

/-- The full physical PDO amplitude in either literal orientation. Conjugate
transpose applies to both physical masks in their original positions; this
is the amplitude of the Hilbert adjoint, not the transpose of its symbol alone
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def orientedMaskedPDOAmplitude (backward : Bool) (χout χsource : E → ℂ)
    (c : E → E → Mat) : FullAmplitude (d + 1) q := fun x y ξ ↦
  if backward then ((χout x * χsource y) • c x ξ).conjTranspose
    else (χout x * χsource y) • c x ξ

private theorem orientedMaskedPDOAmplitude_zero_off_base (backward : Bool)
    (χout χsource : E → ℂ) (c : E → E → Mat) (x y ξ : E)
    (h : (x, y) ∉ tsupport χout ×ˢ tsupport χsource) :
    orientedMaskedPDOAmplitude backward χout χsource c x y ξ = 0 := by
  have hz : χout x * χsource y = 0 := by
    by_cases hx : x ∈ tsupport χout
    · rw [image_eq_zero_of_notMem_tsupport (fun hy ↦ h ⟨hx, hy⟩), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  simp only [orientedMaskedPDOAmplitude, hz, zero_smul, Matrix.conjTranspose_zero, ite_self]

/-- All four literal `directPDOSymbols` branches, with arbitrary real symbol
order, satisfy the
individual factor estimate in both literal orientations. All phase grades,
stationary gaps, comparable carriers, differentiated kernels, shell sums, Fourier comparison and
operator identification are derived. Only primitive full-symbol and mask
grades, their geometric carriers, and finite realization/strong-limit outputs
remain explicit. These are supplied by `ResidualCoordinates.Assembly` and the
physical `FullLowBounds` producer for each `directPDOSymbols` branch. The
closed input shoulder is required inside the output plateau. Constants and
losses precede the coefficient family and accuracy
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_directPDO_fourier_bound
    {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables E))
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (backward : Bool) (s : ℝ) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    (χout χsource : E → ℂ) (hout : HasCompactSupport χout)
    (hsource : HasCompactSupport χsource)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (hirange : ∀ p, mi p ∈ Icc (0 : ℝ) 1)
    {Ko Oo : Set (E × E)} (ho : IsBufferedLocalizer mo Ko Oo) (hKo : IsCompact Ko)
    (hdiag : tsupport mi ⊆ Ko)
    (hiAnn : ∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a b)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hplateau : ∀ x ∈ leakageOutputCarrier backward
      (tsupport χout ×ˢ tsupport χsource) (Prod.fst '' tsupport mo), ψ x = 1)
    (D : AmplitudeProfiles) :
    let Kb := tsupport χout ×ˢ tsupport χsource
    let Ki := Prod.fst '' tsupport mi
    let Z := (Prod.fst '' Kb) ×ˢ frequencyAnnulus
      (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b))
    let K := comparableJointCarrier 1 1 a b Z Kb (frequencyAnnulus a b)
    ∃ (bLoss : ℕ) (Cmq : ℕ → ℝ), (∀ N, 0 ≤ Cmq N) ∧
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∃ Mi Mo : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
    ∀ (Ac : E → Fin (d + 1) → Mat) (Bc : E → Mat)
      (W₁ : TwoTimeAmplitude d q) (bminus : E → E → Mat)
      (σ : E → Euclidean d → ℂ) (β : E → ℂ) (branch : Fin 4),
    let c := directPDOSymbols Ac Bc W₁ bminus σ β branch
    let A := orientedMaskedPDOAmplitude backward χout χsource c
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) →
    (∀ k p, p ∈ K → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      A p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ ρ ^ s * D.symbol k * L ^ (k + D.symbolOffset)) →
    (∀ y ∈ Ki, ∀ k p, p ∈ K → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      (mi (y, p.2.2.1) : ℂ)) p‖ ≤ D.inputMask k * L ^ (k + D.inputMaskOffset)) →
    (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ k,
      ‖iteratedFDeriv ℝ k (fun z : E × E ↦ A z.1 z.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low j)) ^ s * D.symbol k * L ^ (k + D.symbolOffset)) →
    (∀ x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      D.outputMask k * L ^ (k + D.outputMaskOffset)) →
    ∀ F : Set E, IsClosed F → (0 : E) ∉ F →
    (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
    ∀ χ : ℕ → E → ℂ,
    (∀ (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → B x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) B) →
    ∀ Preg : ℕ → H →L[ℂ] H,
    (∀ j (u : graphTestSpace (d + 1) q), Preg j (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        (fun x ξ ↦ inner ℝ x ξ) (frequencyCutFullAmplitude (χ j) A)
        (fun y ↦ (u.val y).ofLp)) x)) →
    let P := maskedPhysicalPDO χout χsource c
    let G := if backward then P.adjoint else P
    (∀ u, Tendsto (fun j ↦ Preg j u) atTop (𝓝 (G u))) →
    ∀ N u,
      MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (G (Mi u))) ∧
      vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (G (Mi u))) ≤
        Cmq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
          L ^ bLoss * (L / ρ) ^ N * ‖u‖ := by
  classical
  intro Kb Ki Z K
  have hKb : IsCompact Kb := hout.prod hsource
  have hKi : IsCompact Ki := his.image continuous_fst
  have hZ : IsCompact Z := (hKb.image continuous_fst).prod (isCompact_frequencyAnnulus _ _)
  have hiSupport : tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a b :=
    fun p hp ↦ ⟨⟨p, hp, rfl⟩, hiAnn p hp⟩
  have hK : IsCompact K := isCompact_comparableJointCarrier 1 1 a b hZ hKb
    (isCompact_frequencyAnnulus a b)
  obtain ⟨Gphase, Pphase, _, hphase⟩ := exists_diagonal_jointPhase_grades backward hsψ hKi hK
  obtain ⟨bLoss, Cmq, hCmq, hbound⟩ :=
    exists_graph_factor_sobolev_bound_of_primitive_grades
      (r := q) (by omega : 0 < d + 1) e eu ez backward s m
      (c := 1) (C := 1) (by norm_num) ha (I := tsupport mi) Subset.rfl hi hirange ho hKo
      J ψ hψ hsψ volume volume hJ hZ hKb hKi hiSupport
      (Prod.fst '' tsupport mo) (ho.compactSupport.image continuous_fst)
      (fun x hx ξ ↦ image_eq_zero_of_notMem_tsupport (fun hh ↦ hx ⟨(x, ξ), hh, rfl⟩))
      hplateau D (G := Gphase) (aChart := 1) (bChart := 1)
      (by norm_num) (by norm_num) Pphase (fun _ ↦ 0) (fun _ ↦ le_rfl)
  refine ⟨bLoss, fun N ↦ fourierComparisonConstant J m * Cmq N,
    fun N ↦ mul_nonneg (fourierComparisonConstant_pos J m).le (hCmq N), ?_⟩
  intro ρ L hL hLρ
  have hρ : ρ ≠ 0 := (zero_lt_one.trans_le (hL.trans hLρ)).ne'
  obtain ⟨Li, _, hMi⟩ := exists_bounded_physicalLocalizers (q := q) hρ mi hi.continuous his
  obtain ⟨Mo, hMo, _⟩ := exists_bounded_physicalLocalizers (q := q) hρ mo
    ho.smooth.continuous ho.compactSupport
  refine ⟨Li.adjoint, Mo, hMi, hMo, ?_⟩
  intro Ac Bc W₁ bminus σ β branch c A hA hsymbol hin hbase houtGrade F hF hzero hAF χ hχeq Preg hreal P G hlim N u
  let S : E → E → ℝ := fun x ξ ↦ inner ℝ x ξ
  have hS : ContDiff ℝ ∞ (Function.uncurry S) := ContDiff.inner ℝ contDiff_fst contDiff_snd
  let T := (Prod.fst '' (tsupport mi ∪ Z)) ×ˢ (Prod.snd '' (tsupport mi ∪ Z))
  have hT : IsCompact T := ((his.union hZ).image continuous_fst).prod
    ((his.union hZ).image continuous_snd)
  have hZT : Z ⊆ T := fun p hp ↦ ⟨⟨p, Or.inr hp, rfl⟩, ⟨p, Or.inr hp, rfl⟩⟩
  have hpoints : if backward then
      (∀ p ∈ tsupport mi, (p.1, (id p).2) ∈ T) ∧
        (∀ p ∈ tsupport mi, ∀ z ∈ Z, (p.1, z.2) ∈ T)
      else (∀ p ∈ tsupport mi, ((id p).1, p.2) ∈ T) ∧
        (∀ p ∈ tsupport mi, ∀ z ∈ Z, (z.1, p.2) ∈ T) := by
    have hself : ∀ p ∈ tsupport mi, p ∈ T :=
      fun p hp ↦ ⟨⟨p, Or.inl hp, rfl⟩, ⟨p, Or.inl hp, rfl⟩⟩
    cases backward
    · exact ⟨hself, fun p hp z hz ↦ ⟨⟨z, Or.inr hz, rfl⟩, ⟨p, Or.inl hp, rfl⟩⟩⟩
    · exact ⟨hself, fun p hp z hz ↦ ⟨⟨p, Or.inl hp, rfl⟩, ⟨z, Or.inr hz, rfl⟩⟩⟩
  have hchart : if backward then ReverseChartControl S id (tsupport mi) Z 1 1
      else ForwardChartControl S id (tsupport mi) Z 1 1 := by
    cases backward
    · exact diagonal_forwardChartControl _ _
    · exact diagonal_reverseChartControl _ _
  have hAbase := orientedMaskedPDOAmplitude_zero_off_base backward χout χsource c
  have hsupp (ξ : E) : tsupport (fun z : E × E ↦ A z.1 z.2 ξ) ⊆ Kb := by
    apply closure_minimal _ hKb.isClosed
    intro z hz
    by_contra hh
    exact hz (hAbase z.1 z.2 ξ hh)
  have hcarrier low j k (hc : IsComparablePair 1 1 a b ρ low j k)
      x y ξ (hAξ : A x y (ρ • ξ) ≠ 0) (hcut : graphBranchCutoff low j (ρ • ξ) ≠ 0) :
      (x, ξ) ∈ Z := by
    refine ⟨⟨(x, y), hsupp _ (subset_tsupport _ hAξ), rfl⟩, ?_⟩
    exact comparableGraphCarrier_subset (hL.trans hLρ) hc
      (tsupport_rescaled_graphBranchCutoff_subset hρ low j (subset_tsupport _ hcut))
  let Kphase : Bool → ℕ → Set (E × E) := fun low j ↦ (Prod.fst '' Kb) ×ˢ
    frequencyAnnulus (graphLower low j) (graphUpper low j)
  have hphysical low j ξ (hξ : ξ ∈ normalizedGraphCarrier ρ low j)
      z (hz : z ∈ tsupport (fun z : E × E ↦ A z.1 z.2 (ρ • ξ))) :
      (z.1, ρ • ξ) ∈ Kphase low j :=
    ⟨⟨z, hsupp _ hz, rfl⟩, (mem_normalizedGraphCarrier_iff hρ low j ξ).mp hξ⟩
  have hg (x ξ : E) : fderiv ℝ (fun t ↦ S t ξ) x = innerSL ℝ ξ := by
    have he : (fun t ↦ S t ξ) = innerSL ℝ ξ := by funext t; exact (real_inner_comm t ξ).symm
    rw [he, ContinuousLinearMap.fderiv]
  have hpbase low j ξ (_ : ξ ∈ normalizedGraphCarrier ρ low j)
      z (_ : z ∈ tsupport (fun z : E × E ↦ A z.1 z.2 (ρ • ξ)))
      k (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) (fun z : E × E ↦ S z.1 (ρ • ξ)) z‖ ≤
        ‖ρ • ξ‖ * 0 * L ^ k := by
    let l : (E × E) →L[ℝ] ℝ := (innerSL ℝ (ρ • ξ)).comp (ContinuousLinearMap.fst ℝ E E)
    have he : (fun z : E × E ↦ S z.1 (ρ • ξ)) = l := by
      funext z; exact (real_inner_comm z.1 (ρ • ξ)).symm
    rw [he, iteratedFDeriv_succ_eq_comp_right]
    simp only [ContinuousLinearMap.fderiv]
    rw [iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
    simp only [Function.comp_apply, Pi.zero_apply]
    rw [(continuousMultilinearCurryRightEquiv' ℝ k (E × E) ℝ).symm.map_zero]
    simp
  obtain ⟨Op, hOp, _, hOpReg⟩ := hbound ρ L hL hLρ S S A id univ T univ Kphase
    (fun _ ξ ↦ ξ) (fun x ξ ↦ by simp [S, inner_smul_right]) hS.continuous
    isOpen_univ hT (subset_univ _) hS.contDiffOn hZT hpoints hchart hdiag
    hA hAbase hcarrier hsymbol hin (hphase L hL).1 (hphase L hL).2
    isOpen_univ hS.contDiffOn
    (fun low j ↦ (hKb.image continuous_fst).prod (isCompact_frequencyAnnulus _ _))
    (fun _ _ ↦ subset_univ _) hphysical (fun x ξ _ ↦ hg x ξ)
    (fun x ξ _ ↦ by simp) hpbase hbase houtGrade
  have hreg := matrixRealization_physical_regularization_limit J hJ Op _ hOpReg
  have hpref := eventually_oriented_graphPrefix_realization backward S A hF hzero hAF χ hχeq Preg hreal
  have hident := eq_localized_of_finite_graph_realizations J hJ backward hρ S S hS A
    (fun _ _ _ _ ↦ rfl) hA hKb hAbase mi mo hi ho.smooth.continuous his ho.compactSupport
    Li.adjoint Mo G (matrixRealization J hJ Op) hMi hMo
    (fun j ↦ Preg (2 ^ j - 1)) hpref
    (fun u ↦ (hlim u).comp tendsto_graphShell_producer_indices) hreg
  have hu := matrixRealization_fourier_bound J hJ Op u
  have he : (1 - Mo) (G (Li.adjoint u)) = matrixRealization J hJ Op u :=
    DFunLike.congr_fun hident u
  rw [he]
  refine ⟨hu.1, hu.2.trans ?_⟩
  calc
    _ ≤ fourierComparisonConstant J m *
        (Cmq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
          L ^ bLoss * (L / ρ) ^ N) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hOp N)
        (fourierComparisonConstant_pos J m).le) (norm_nonneg u)
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
