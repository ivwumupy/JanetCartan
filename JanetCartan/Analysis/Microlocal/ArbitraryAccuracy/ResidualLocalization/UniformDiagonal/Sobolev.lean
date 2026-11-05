module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal.Shells
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.ConicLimits.Sobolev

/-! # Sobolev graph realization uniform in the selected proof masks -/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
open FourierIntegral FiniteChain.Graph KernelLimits CartesianJets PhysicalShells
open KernelEstimates KernelEstimates.NoncomparableGeometry
open PhysicalShells.Comparable PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelSobolev AmplitudeBound
open JanetCartan.RetardedSobolev.Spaces
variable {n r d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 256

/-- The original conic regularizations and their literal localized limits
have a fixed Sobolev loss before the even masks are chosen. The common mask
profile, compact input base and positive separation replace the mask-dependent
constant choices. No leakage or kernel bound is assumed: all physical shell
majorants are derived from primitive grades. Consumer: the four selected PDO
branches (`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_graph_factor_sobolev_bound_of_uniform_masks
    (hn : 0 < n) {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (eu : OrthonormalBasis ιu ℝ (Euclidean n)) (ez : OrthonormalBasis ιz ℝ (Euclidean n))
    (backward : Bool) (s : ℝ) (m : ℕ)
    {c C a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (μ ν : Measure ((Fin d → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hJ : MeasurePreserving (graphInputCoordinates J) μ volume)
    {Z Kb : Set (Euclidean n × Euclidean n)} {Ki : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKi : IsCompact Ki)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hplateau : ∀ x ∈ leakageOutputCarrier backward Kb t, ψ x = 1)
    (D : AmplitudeProfiles) {aChart bChart G : ℝ}
    (haChart : 0 ≤ aChart) (hbChart : 0 ≤ bChart) {δ : ℝ} (hδ : 0 < δ)
    (P Pbase O : ℕ → ℝ) (hPbase : ∀ d, 0 ≤ Pbase d) (hO : ∀ j, 0 ≤ O j) :
    let K := comparableJointCarrier c C a b Z Kb (frequencyAnnulus a b)
    ∃ (bLoss : ℕ) (Cmq : ℕ → ℝ), (∀ q, 0 ≤ Cmq q) ∧
    ∀ (mi mo : LocalizerSymbol n) {I Ko Oo : Set (Euclidean n × Euclidean n)},
    tsupport mi ⊆ I → ContDiff ℝ ∞ mi → (∀ p, mi p ∈ Icc (0 : ℝ) 1) →
    IsBufferedLocalizer mo Ko Oo → tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a b →
    (∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0) → (∀ j p, ‖iteratedFDeriv ℝ j mo p‖ ≤ O j) →
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
    ∀ (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
      (U T V : Set (Euclidean n × Euclidean n))
      (Kphase : Bool → ℕ → Set (Euclidean n × Euclidean n))
      (g : Euclidean n → Euclidean n → Euclidean n),
    (∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ) → Continuous (Function.uncurry S) →
    IsOpen U → IsCompact T → T ⊆ U → ContDiffOn ℝ ∞ (Function.uncurry φ) U → Z ⊆ T →
    (if backward then
      (∀ q ∈ I, (q.1, (κ q).2) ∈ T) ∧ (∀ q ∈ I, ∀ p ∈ Z, (q.1, p.2) ∈ T)
      else (∀ q ∈ I, ((κ q).1, q.2) ∈ T) ∧ (∀ q ∈ I, ∀ p ∈ Z, (p.1, q.2) ∈ T)) →
    (if backward then ReverseChartControl φ κ I Z aChart bChart
      else ForwardChartControl φ κ I Z aChart bChart) →
    (∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1 - mo q), δ ≤ dist (κ q) q') →
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n => A p.1.1 p.1.2 p.2) →
    (∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0) →
    (∀ low j k, IsComparablePair c C a b ρ low j k → ∀ u z ξ,
      A u z (ρ • ξ) ≠ 0 → graphBranchCutoff low j (ρ • ξ) ≠ 0 → (u, ξ) ∈ Z) →
    (∀ d p, p ∈ K → ‖iteratedFDeriv ℝ d (fun p : JointVariables (Euclidean n) =>
      A p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ ρ ^ s * D.symbol d * L ^ (d + D.symbolOffset)) →
    (∀ y ∈ Ki, ∀ d p, p ∈ K → ‖iteratedFDeriv ℝ d (fun p : JointVariables (Euclidean n) =>
      (mi (y, p.2.2.1) : ℂ)) p‖ ≤ D.inputMask d * L ^ (d + D.inputMaskOffset)) →
    (∀ x ∈ tsupport ψ, ∀ y ∈ Ki, ∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
    (∀ x ∈ tsupport ψ, ∀ y ∈ Ki, ∀ p ∈ K, ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (jointPhase backward φ x y) p‖ ≤ P d * L ^ d) →
    IsOpen V → ContDiffOn ℝ ∞ (Function.uncurry S) V →
    (∀ low j, IsCompact (Kphase low j)) → (∀ low j, Kphase low j ⊆ V) →
    (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      (z.1, ρ • ξ) ∈ Kphase low j) →
    (∀ u ξ, (u, ξ) ∈ V → fderiv ℝ (fun t => S t ξ) u = innerSL ℝ (g u ξ)) →
    (∀ u ξ, (u, ξ) ∈ V → c * ‖ξ‖ ≤ ‖g u ξ‖ ∧ ‖g u ξ‖ ≤ C * ‖ξ‖) →
    (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (fun z : Euclidean n × Euclidean n => S z.1 (ρ • ξ)) z‖ ≤
        ‖ρ • ξ‖ * Pbase d * L ^ d) →
    (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ d,
      ‖iteratedFDeriv ℝ d (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low j)) ^ s * D.symbol d * L ^ (d + D.symbolOffset)) →
    (∀ x ζ d, ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤
      D.outputMask d * L ^ (d + D.outputMaskOffset)) →
    ∃ T : Fin r → Fin r → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      (∀ q, ‖matrixOperator T‖ ≤ Cmq q *
        ρ ^ ((m : ℝ) + (max 0 s + (3 * n : ℕ))) * L ^ bLoss * (L / ρ) ^ q) ∧
      (∀ (f : Fin r → Test d) (a : Fin r),
        ((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
          (zeroIndex d m) =ᵐ[ν] fun p =>
            (∫ y, (∑' q : ℕ × ℕ,
              regularizedJointKernel backward S A
                (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
                (graphCutoff q.1) (outputCutoff q.2) (J (p.2, p.1)) y).mulVec
                (physicalTestField J f y)) a) ∧
      ∀ (f : Fin r → Test d) (a : Fin r), ∀ᵐ p ∂ν,
        Tendsto (fun q : Finset ℕ × Finset ℕ =>
          leftLocalizer 1 (fun z => (∑ k ∈ q.2, outputCutoff k z.2) *
            (1 - mo (z.1, ρ⁻¹ • z.2)))
            ((if backward then reverseGraphOperator else graphOperator) S
              (fun u z ξ => ((∑ j ∈ q.1, graphCutoff j ξ) : ℂ) • A u z ξ)
              (rightLocalizer 1 (fun z => mi (z.1, ρ⁻¹ • z.2))
                (physicalTestField J f))) (J (p.2, p.1)) a) atTop
          (𝓝 (((matrixOperator T (WithLp.toLp 2 (fun b => ofTest 0 μ (f b)))) a).val
            (zeroIndex d m) p)) := by
  classical
  intro K
  have hproducer (l : ℕ) := exists_physical_kernel_majorants_of_uniform_masks (r := r)
    (c := c) (C := C) (b := b) (G := G) hn e eu ez backward s l hc ha
    (tsupport ψ) hZ hKb hKi D haChart hbChart hδ P Pbase O hPbase hO
  choose bLoss Cq C₀ hCq hC₀ hproducer using hproducer
  let loss := ∑ l ∈ Finset.range (m + 1), bLoss l
  let supportFactor := compactSupportFactor μ ν
    ((fun y : (Fin d → ℝ) × ℝ => J (y.2, y.1)) ⁻¹' Ki)
    (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))
  let Cmq := fun q => (r : ℝ) * r *
    jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l => Cq l q) m * supportFactor
  have hsupport : 0 ≤ supportFactor := compactSupportFactor_nonneg _ _ _ _
  have hCmq q : 0 ≤ Cmq q := by
    apply mul_nonneg _ hsupport
    exact mul_nonneg (by positivity)
      (jetMajorant_nonneg J (cutoffDerivativeProfile_nonneg hψ hsψ)
        (fun l _ => hCq l q))
  refine ⟨loss, Cmq, hCmq, ?_⟩
  intro mi mo I Ko Oo hi hiSmooth hiRange ho hiSupport hmt hmoJoint ρ L hL hLρ S φ A κ U T V Kphase g hscale hSc hU hT hTU hφ hZT
    hpoints hchart hsep hA hbase hcarrier hsymbol hin hupper hp
    hV hSV hKphase hKV hphysical hg hcomp hpbase hAbase hout
  have hρ := hL.trans hLρ
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hprod l := hproducer l mi mo hi hiSmooth hiRange ho hiSupport hmoJoint ρ L hL hLρ S φ A κ U T V Kphase g hscale hSc
    hU hT hTU hφ hZT hpoints hchart hsep hA hbase hcarrier hsymbol hin hupper hp
    hV hSV hKphase hKV hphysical hg hcomp hpbase hAbase hout
  choose B B₀ hB hB₀ hsB hsB₀ hsumB hsumB₀ hbB hb₀ hsmooth using hprod
  have hiZero : ∀ y η, (y, η) ∉ Ki ×ˢ frequencyAnnulus a b → mi (y, η) = 0 := by
    intro y η hy
    exact image_eq_zero_of_notMem_tsupport (fun hh => hy (hiSupport hh))
  let carriers j k := physicalInputCarriers
    (cutoffPairCarriers A mi Kb Ki (frequencyAnnulus a b) hKb hKi
      (isCompact_frequencyAnnulus a b) hbase hiZero j k) hρ0.ne'
  have hmi : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => mi (p.1, ρ⁻¹ • p.2)) :=
    hiSmooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hmo : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => mo (p.1, ρ⁻¹ • p.2)) :=
    ho.smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hmoBound : ∀ x ξ, |mo (x, ρ⁻¹ • ξ)| ≤ 1 := by
    intro x ξ
    rw [abs_of_nonneg (ho.range _).1]
    exact (ho.range _).2
  have hgraded q l (hl : l ≤ m) : (∑' α, B l q α) ≤
      Cq l q * ρ ^ ((l : ℝ) + (max 0 s + (3 * n : ℕ))) *
        L ^ loss * (L / ρ) ^ q * 1 := by
    rw [mul_one]
    apply (hsumB l q).trans
    have hloss : bLoss l ≤ loss :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (bLoss i))
        (Finset.mem_range.mpr (by omega))
    have hC := hCq l q
    gcongr
  have hex (j : ℕ) : ∃ S' : Euclidean n → Euclidean n → ℝ,
      ContDiff ℝ ∞ (Function.uncurry S') ∧
      ∀ u z ξ, A u z ξ ≠ 0 → graphCutoff j ξ ≠ 0 → S' u ξ = S u ξ := by
    obtain ⟨F, hF, _, _, _, he⟩ := JanetCartan.NormalComparison.exists_contDiff_localization
      hV ((hKphase false j).union (hKphase true j))
      (union_subset (hKV false j) (hKV true j)) hSV
    refine ⟨fun u ξ => F (u, ξ), hF, ?_⟩
    intro u z ξ ha hg'
    exact (he (u, ξ) (by
      by_cases hh : highGraphCutoff j ξ = 0
      · have hl : lowGraphCutoff j ξ ≠ 0 := by
          intro hl
          exact hg' (by simp [graphCutoff, hh, hl])
        exact Or.inr (physicalBranch_support_of_normalized hρ0.ne' A true j
          (hphysical true j) u z ξ ha hl)
      · exact Or.inl (physicalBranch_support_of_normalized hρ0.ne' A false j
          (hphysical false j) u z ξ ha hh))).eq_of_nhds
  choose Sext hsExt hext using hex
  obtain ⟨Op, hnorm, hsum, hjet, hphys, hlim⟩ :=
    ConicLimits.exists_graph_factor_sobolev_bound_uniform (m := m) J backward S A
      (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
      graphCutoff outputCutoff ψ carriers hSc (hsmooth 0) Sext hsExt hext hA hmi hmo
      contDiff_graphCutoff contDiff_outputCutoff zero_notMem_tsupport_graphCutoff hψ hsψ μ ν hJ
      (fun q l α => B l q α) (fun q l _ => hB l q) (fun q l _ => hsB l q)
      (fun q j k x hx y l _ v hv => hbB l j k x hx y q v hv)
      (B₀ 0) (hsB₀ 0) (hb₀ 0) abs_sum_outputCutoff_le_one tendsto_sum_outputCutoff
      1 hmoBound t ht (fun x hx ξ => hmt x hx (ρ⁻¹ • ξ)) hplateau
      (D := fun q l => Cq l q) (fun q l _ => hCq l q) hρ (zero_le_one.trans hL)
      (show (0 : ℝ) ≤ 1 by norm_num) (max 0 s + (3 * n : ℕ)) loss hgraded
  refine ⟨Op, ?_, hphys, hlim⟩
  intro q
  convert hnorm q using 1
  dsimp [Cmq, supportFactor, carriers,
    physicalInputCarriers, cutoffPairCarriers]
  ring


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
