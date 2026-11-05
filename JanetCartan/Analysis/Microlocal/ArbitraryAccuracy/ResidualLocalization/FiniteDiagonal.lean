module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PairedDiagonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerSobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# The finite diagonal part of the complete physical residual

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
set_option maxHeartbeats 6400000
set_option synthInstance.maxSize 256

private theorem oriented_physicalPair_sub_identity {α : Type*} [Fintype α]
    (F : α → H →L[ℂ] H) (backward : Bool) :
    (if backward then (physicalPairedSectorSum Finset.univ F - 1).adjoint
      else physicalPairedSectorSum Finset.univ F - 1) =
      (∑ j, ((if backward then (F j).adjoint else F j) +
        boundedConjugate (if backward then (F j).adjoint else F j))) - 1 := by
  classical
  have hpair (G : α → H →L[ℂ] H) : physicalPairedSectorSum Finset.univ G =
      ∑ j, (G j + boundedConjugate (G j)) := by
    apply ContinuousLinearMap.ext
    intro x
    change (∑ j, G j) x + star ((∑ j, G j) (star x)) =
      (∑ j, (G j + boundedConjugate (G j))) x
    simp only [sum_apply, add_apply]
    change (∑ j, G j x) + star (∑ j, G j (star x)) =
      ∑ j, (G j x + star (G j (star x)))
    rw [star_sum, Finset.sum_add_distrib]
  cases backward
  · exact congrArg (fun A : H →L[ℂ] H ↦ A - 1) (hpair F)
  · simp only [ite_true, map_sub, ContinuousLinearMap.adjoint_one,
      physicalPairedSectorSum_adjoint_eq]
    exact congrArg (fun A : H →L[ℂ] H ↦ A - 1) (hpair _)

/-- Assemble the literal finite weighted PDO sum and subtract the identity ONCE.
The four branches of `directPDOSymbols` include the principal, upper endpoint and
full algebraic derivative; the fixed `weights` retain their original coefficients.
`exists_weightedPhysicalPDO_restriction_bound` produces every paired summand from
primitive grades and realizations; `exists_identityLeakage_fourierSobolev_bound`
produces the separate identity leakage from the strict buffered diagonal plateau.
No localized estimate is a hypothesis. Both literal orientations and the real
compression use the same masks, operators and actual restriction scale. The
finite coefficient loss is chosen before accuracy and frequency. Consumer: the
PDO part of the complete residual `hleak` in `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). The remaining
elapsed correction must be added for the full residual. -/
theorem exists_finitePhysicalPDO_defect_restriction_bound
    {α ι ιu ιz : Type*} [Fintype α] [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables E))
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (backward : Bool) (s : ℝ) (m : ℕ) (weights : α → ℂ) (branches : α → Fin 4) {a b : ℝ} (ha : 0 < a)
    (χout χsource : α → E → ℂ) (hout : ∀ j, HasCompactSupport (χout j))
    (hsource : ∀ j, HasCompactSupport (χsource j))
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
    (hplateau : ∀ j, ∀ x ∈ leakageOutputCarrier backward
      (tsupport (χout j) ×ˢ tsupport (χsource j)) (Prod.fst '' tsupport mo), ψ x = 1)
    (D : α → AmplitudeProfiles) :
    let Kb := fun j ↦ tsupport (χout j) ×ˢ tsupport (χsource j)
    let Ki := Prod.fst '' tsupport mi
    let Z := fun j ↦ (Prod.fst '' Kb j) ×ˢ frequencyAnnulus
      (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b))
    let K := fun j ↦ comparableJointCarrier 1 1 a b (Z j) (Kb j) (frequencyAnnulus a b)
    ∃ (bLoss : ℕ) (Cmq Creal : ℕ → ℝ),
      (∀ N, 0 ≤ Cmq N) ∧ (∀ N, 0 ≤ Creal N) ∧
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∀ Mi Mo : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
    ∀ (Ac : α → E → Fin (d + 1) → Mat) (Bc : α → E → Mat)
      (W₁ : α → TwoTimeAmplitude d q) (bminus : α → E → E → Mat)
      (σ : α → E → Euclidean d → ℂ) (β : α → E → ℂ),
    let c := fun j ↦ directPDOSymbols (Ac j) (Bc j) (W₁ j) (bminus j) (σ j) (β j) (branches j)
    let A := fun j ↦ orientedMaskedPDOAmplitude backward (χout j) (χsource j) (c j)
    (∀ j, ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A j p.1.1 p.1.2 p.2)) →
    (∀ j k p, p ∈ K j → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      A j p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ ρ ^ s * (D j).symbol k * L ^ (k + (D j).symbolOffset)) →
    (∀ j, ∀ y ∈ Ki, ∀ k p, p ∈ K j → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      (mi (y, p.2.2.1) : ℂ)) p‖ ≤ (D j).inputMask k * L ^ (k + (D j).inputMaskOffset)) →
    (∀ j low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb j, ∀ k,
      ‖iteratedFDeriv ℝ k (fun z : E × E ↦ A j z.1 z.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low l)) ^ s * (D j).symbol k * L ^ (k + (D j).symbolOffset)) →
    (∀ j x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      (D j).outputMask k * L ^ (k + (D j).outputMaskOffset)) →
    ∀ F : α → Set E, (∀ j, IsClosed (F j)) → (∀ j, (0 : E) ∉ F j) →
    (∀ j x y ξ, ξ ∉ F j → A j x y ξ = 0) →
    ∀ χ : α → ℕ → E → ℂ,
    (∀ j (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F j → B x y ξ = 0) →
      ∀ l, frequencyCutFullAmplitude (χ j l) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff l) B) →
    ∀ Preg : α → ℕ → H →L[ℂ] H,
    (∀ j l (u : graphTestSpace (d + 1) q), Preg j l (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        (fun x ξ ↦ inner ℝ x ξ) (frequencyCutFullAmplitude (χ j l) (A j))
        (fun y ↦ (u.val y).ofLp)) x)) →
    let P := fun j ↦ maskedPhysicalPDO (χout j) (χsource j) (c j)
    let G := fun j ↦ if backward then (P j).adjoint else P j
    (∀ j u, Tendsto (fun l ↦ Preg j l u) atTop (𝓝 (G j u))) →
    let S := physicalPairedSectorSum Finset.univ (fun j ↦ weights j • P j)
    let Efull := S - ContinuousLinearMap.id ℂ H
    ∀ N (U : Set E) (hU : MeasurableSet U),
      let T := if backward then Efull.adjoint else Efull
      (∀ u : H,
        restrictL2 U ((1 - Mo) (T (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) (T (Mi u)))) ≤
          Cmq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bLoss * (L / ρ) ^ N * ‖u‖) ∧
      ∀ u : Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E),
        let v := l2RealPart (volume.restrict U)
          (restrictL2 U ((1 - Mo) (T (Mi (l2ComplexInclusion volume u)))))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m v ≤
          Creal N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bLoss * (L / ρ) ^ N * ‖u‖ := by
  classical
  intro Kb Ki Z K
  choose bj Cj Rj hCj hRj hj using fun j ↦ exists_weightedPhysicalPDO_restriction_bound
    e eu ez backward s m ha (χout j) (χsource j) (hout j) (hsource j)
    mi mo hi his hirange ho hKo hdiag hieven hoeven hiAnn J hJ ψ hψ hsψ (hplateau j) (D j)
  obtain ⟨CI, hCI, hI⟩ := IdentityDefect.exists_identityLeakage_fourierSobolev_bound
    (r := q) mi mo hi his ho.smooth ho.compactSupport ho.range (hdiag.trans ho.plateau) m
  obtain ⟨Kcomp, hKcomp, hcompare⟩ := exists_restrictionScale_fourier_comparison (d + 1) q m
  let bTotal := ∑ j, bj j
  let Ctotal := fun N ↦ (∑ j, Cj j N * ‖weights j‖) + Kcomp * CI N
  let Rpart := euclideanRealPart (ι := Fin q)
  have hCtotal N : 0 ≤ Ctotal N := add_nonneg
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hCj j N) (norm_nonneg _))
    (mul_nonneg hKcomp.le (hCI N))
  refine ⟨bTotal, Ctotal, fun N ↦ (‖Rpart‖ + 1) * Ctotal N,
    hCtotal, fun N ↦ mul_nonneg (by positivity) (hCtotal N), ?_⟩
  intro ρ L hL hLρ Mi Mo hMi hMo Ac Bc W₁ bminus σ β c A
    hA hsymbol hin hbase houtGrade F hF hzero hAF χ hχeq Preg hreal P G hlim S Efull N U hU T
  let Tj := fun j ↦ if backward then (weights j • P j).adjoint else weights j • P j
  have hb j := (hj j ρ L hL hLρ Mi Mo hMi hMo
    (Ac j) (Bc j) (W₁ j) (bminus j) (σ j) (β j) (branches j)
    (hA j) (hsymbol j) (hin j) (hbase j) (houtGrade j) (F j) (hF j) (hzero j)
    (hAF j) (χ j) (hχeq j) (Preg j) (hreal j) (hlim j) (weights j) N U hU).1
  let Gs := restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU
  let exponent : ℝ := (m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLnonneg : 0 ≤ L := zero_le_one.trans hL
  have hbTotal j : bj j ≤ bTotal := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (bj i))
    (Finset.mem_univ j)
  have hcomplex (u : H) : restrictL2 U ((1 - Mo) (T (Mi u))) ∈ Gs.level m ∧
      Gs.gradeNorm m (restrictL2 U ((1 - Mo) (T (Mi u)))) ≤
        Ctotal N * ρ ^ exponent * L ^ bTotal * (L / ρ) ^ N * ‖u‖ := by
    let v := fun j ↦ restrictL2 U ((1 - Mo) ((Tj j + boundedConjugate (Tj j)) (Mi u)))
    have hv j : v j ∈ Gs.level m ∧ Gs.gradeNorm m (v j) ≤
        Cj j N * ‖weights j‖ * ρ ^ exponent * L ^ bTotal * (L / ρ) ^ N * ‖u‖ := by
      refine ⟨(hb j u).1, (hb j u).2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg hLnonneg hρpos.le) _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (hbTotal j))
        (mul_nonneg (mul_nonneg (hCj j N) (norm_nonneg _)) (Real.rpow_nonneg hρpos.le _))
    obtain ⟨hsum, hsumBound⟩ := ResponseTransfer.gradeNorm_sum_le Gs Finset.univ v m (fun j _ ↦ (hv j).1)
    have hsum' : Gs.gradeNorm m (∑ j, v j) ≤
        (∑ j, Cj j N * ‖weights j‖) * ρ ^ exponent * L ^ bTotal * (L / ρ) ^ N * ‖u‖ := by
      apply hsumBound.trans
      simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun j _ ↦ (hv j).2)
    obtain ⟨hImem, hInorm⟩ := hI ρ L hL hLρ Mi Mo hMi hMo N (-u)
    obtain ⟨hImem', hInorm'⟩ := hcompare U hU _
      (restrictL2 U ((1 - Mo) (Mi (-u)))) hImem (restrictL2_coeFn U _).symm
    have hIbound : Gs.gradeNorm m (restrictL2 U ((1 - Mo) (Mi (-u)))) ≤
        (Kcomp * CI N) * ρ ^ exponent * L ^ bTotal * (L / ρ) ^ N * ‖u‖ := by
      apply hInorm'.trans
      apply (mul_le_mul_of_nonneg_left hInorm hKcomp.le).trans
      rw [norm_neg]
      have hpow : ρ ^ (d + 1 + m) ≤ ρ ^ exponent := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hρ
        dsimp [exponent]
        push_cast
        have := le_max_left (0 : ℝ) s
        have := Nat.cast_nonneg (α := ℝ) d
        linarith
      have hscale : ρ ^ (d + 1 + m) ≤ ρ ^ exponent * L ^ bTotal :=
        hpow.trans (le_mul_of_one_le_right (Real.rpow_nonneg hρpos.le _) (one_le_pow₀ hL))
      calc
        _ = (Kcomp * CI N) * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ := by ring
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale
              (mul_nonneg hKcomp.le (hCI N))) (pow_nonneg (div_nonneg hLnonneg hρpos.le) _))
            (norm_nonneg u)
    have he : restrictL2 U ((1 - Mo) (T (Mi u))) =
        (∑ j, v j) + restrictL2 U ((1 - Mo) (Mi (-u))) := by
      have hT : T = (∑ j, (Tj j + boundedConjugate (Tj j))) - 1 :=
        oriented_physicalPair_sub_identity (fun j ↦ weights j • P j) backward
      rw [hT]
      change restrictL2 U ((1 - Mo)
        ((∑ j, (Tj j + boundedConjugate (Tj j))) (Mi u) - Mi u)) = _
      rw [map_sub, map_sub]
      simp only [sum_apply, map_sum, map_neg, v]
      exact sub_eq_add_neg _ _
    rw [he]
    refine ⟨(Gs.level m).add_mem hsum hImem', ?_⟩
    exact (ResponseTransfer.gradeNorm_add_le Gs hsum hImem').trans
      ((add_le_add hsum' hIbound).trans_eq (by dsimp [Ctotal]; ring))
  refine ⟨hcomplex, ?_⟩
  intro u v
  obtain ⟨hm, hn⟩ := hcomplex (l2ComplexInclusion volume u)
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound Rpart hm
  refine ⟨hr, ?_⟩
  change (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m
    (Rpart.compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hr]
  apply hnr.trans
  rw [← restrictionSobolevScale_gradeNorm hU hm]
  have hu : ‖l2ComplexInclusion volume u‖ ≤ ‖u‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_right
      (l2ComplexInclusion_norm_le volume) (norm_nonneg u)).trans_eq (one_mul _))
  have hcoef : 0 ≤ Ctotal N * ρ ^ exponent * L ^ bTotal * (L / ρ) ^ N := by
    have := hCtotal N
    positivity
  have hfinal := hn.trans (mul_le_mul_of_nonneg_left hu hcoef)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfinal (show 0 ≤ ‖Rpart‖ + 1 by positivity)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
