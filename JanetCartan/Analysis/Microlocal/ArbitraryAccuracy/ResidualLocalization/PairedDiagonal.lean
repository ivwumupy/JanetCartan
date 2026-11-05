module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# The original weighted PDO branches in the physical pairing

For `app:ch_regular_base:eq:energy-complete-residual`, the coefficient `1/i`
belongs inside the physical plus pairing. Adjunction conjugates that coefficient
and transposes the whole original masked operator. The actual diagonal producer
is applied before pairing, on any already fixed realizations of the same proof
masks. This supplies the diagonal summands of the complete `hleak` estimate in
`finiteChain_observation_rapidDecayAt` (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual
open FiniteChain.Graph KernelLimits CartesianJets PhysicalShells
open KernelEstimates KernelEstimates.NoncomparableGeometry
open PhysicalShells.Comparable PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Realization LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
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

/-- The SAME literal weighted PDO and its physical plus pairing have arbitrary
accuracy in the genuine complex and real restriction scales. No successful
localized estimate is assumed: `exists_directPDO_fourier_bound` derives it from
primitive grades and finite realizations, supplied by `ResidualCoordinates.Assembly`
and `FullLowBounds`. The geometric inputs are supplied by `ProtectedMasks`.
For the algebraic solver and differentiated algebraic correction use `z = 1/i`;
for the principal and endpoint use `z = 1`. The literal adjoint conjugates `z`.
All losses and both profiles precede frequency, coefficient data and accuracy
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_weightedPhysicalPDO_restriction_bound
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
    (hieven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
    (hoeven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
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
    ∃ (bLoss : ℕ) (Cmq Creal : ℕ → ℝ),
      (∀ N, 0 ≤ Cmq N) ∧ (∀ N, 0 ≤ Creal N) ∧
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∀ Mi Mo : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
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
    ∀ (z : ℂ) (N : ℕ) (U : Set E) (hU : MeasurableSet U),
      let T := if backward then (z • P).adjoint else z • P
      (∀ u : H,
        restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u)))) ≤
          Cmq N * ‖z‖ * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bLoss * (L / ρ) ^ N * ‖u‖) ∧
      ∀ u : Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E),
        let v := l2RealPart (volume.restrict U)
          (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi (l2ComplexInclusion volume u)))))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m v ≤
          Creal N * ‖z‖ * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bLoss * (L / ρ) ^ N * ‖u‖ := by
  intro Kb Ki Z K
  obtain ⟨bLoss, CP, hCP, hP⟩ := exists_directPDO_fourier_bound e eu ez backward s m ha
    χout χsource hout hsource mi mo hi his hirange ho hKo hdiag hiAnn J hJ ψ hψ hsψ hplateau D
  obtain ⟨KC, hKC, hcomplex⟩ := exists_physicalPair_fourier_restriction_comparison d q m
  obtain ⟨KR, hKR, hreal⟩ := exists_realPhysicalPair_fourier_restriction_comparison d q m
  refine ⟨bLoss, fun N ↦ KC * CP N, fun N ↦ KR * CP N,
    fun N ↦ mul_nonneg hKC.le (hCP N), fun N ↦ mul_nonneg hKR.le (hCP N), ?_⟩
  intro ρ L hL hLρ Mi Mo hMi hMo
  obtain ⟨Mi', Mo', hMi', hMo', hP⟩ := hP ρ L hL hLρ
  have hei : Mi' = Mi := eq_of_rightLocalizer_representatives ρ mi Mi' Mi hMi' hMi
  have heo : Mo' = Mo := eq_of_leftLocalizer_representatives ρ mo Mo' Mo hMo' hMo
  subst Mi'
  subst Mo'
  intro Ac Bc W₁ bminus σ β branch c A hA hsymbol hin hbase houtGrade
    F hF hzero hAF χ hχeq Preg hrealization P G hlim z N U hU T
  have hp := hP Ac Bc W₁ bminus σ β branch hA hsymbol hin hbase houtGrade
    F hF hzero hAF χ hχeq Preg hrealization hlim N
  let w : ℂ := if backward then star z else z
  have hw : ‖w‖ = ‖z‖ := by cases backward <;> simp [w]
  have he (u : H) : (1 - Mo) (T (Mi u)) = (1 - Mo) (G (Mi (w • u))) := by
    have hT : T = w • G := by
      cases backward
      · rfl
      · simp only [T, G, w, ite_true, map_smulₛₗ, starRingEnd_apply]
    rw [hT]
    simp only [smul_apply, map_smul]
  let B := CP N * ‖z‖ * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
    L ^ bLoss * (L / ρ) ^ N
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hB : 0 ≤ B := by
    have := hCP N
    have : 0 ≤ L := zero_le_one.trans hL
    dsimp [B]
    positivity
  have hb (u : H) : MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (T (Mi u))) ∧
      vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (T (Mi u))) ≤ B * ‖u‖ := by
    rw [he]
    refine ⟨(hp (w • u)).1, (hp (w • u)).2.trans_eq ?_⟩
    rw [norm_smul, hw]
    dsimp [B]
    ring
  have hisReal := boundedRightLocalizer_star_of_even ρ mi hieven Mi hMi
  have hosReal := boundedLeftLocalizer_star_of_even hρ.ne' mo ho.smooth.continuous
    ho.compactSupport hoeven Mo hMo
  constructor
  · intro u
    obtain ⟨hm, hn⟩ := hcomplex U hU T Mi Mo hisReal hosReal B hb u
    exact ⟨hm, by simpa only [B, mul_assoc] using hn⟩
  · intro u v
    obtain ⟨hm, hn⟩ := hreal U hU T Mi Mo hisReal hosReal B hB hb u
    exact ⟨hm, by simpa only [B, mul_assoc] using hn⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
