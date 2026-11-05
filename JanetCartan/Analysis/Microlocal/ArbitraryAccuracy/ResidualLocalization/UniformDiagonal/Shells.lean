module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal.Comparable
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Assembly.Estimates

/-! # Physical shell summation uniform over the selected proof masks -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable KernelEstimates.NoncomparableGeometry
variable {n r : ℕ}
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 256

private theorem scale_bound_mono {ρ L C D e E : ℝ} {b B q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hCD : C ≤ D)
    (he : e ≤ E) (hb : b ≤ B) :
    C * ρ ^ e * L ^ b * (L / ρ) ^ q ≤ D * ρ ^ E * L ^ B * (L / ρ) ^ q := by
  have hρ0 := zero_lt_one.trans_le hρ
  have hL0 := zero_le_one.trans hL
  have hD := hC.trans hCD
  gcongr

/-- Summable physical graph/output kernel majorants uniform in the selected
proof masks. The common compact carriers, positive buffer and joint mask
profile precede the masks; symbol orders, original radial cutoffs and both
literal orientations are preserved. Consumer: the uniform PDO Sobolev
realization (`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_physical_kernel_majorants_of_uniform_masks
    (hn : 0 < n) {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (eu : OrthonormalBasis ιu ℝ (Euclidean n)) (ez : OrthonormalBasis ιz ℝ (Euclidean n))
    (backward : Bool) (s : ℝ) (m : ℕ)
    {c C a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (X : Set (Euclidean n))
    {Z Kb : Set (Euclidean n × Euclidean n)} {Ki : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKi : IsCompact Ki)
    (D : AmplitudeProfiles) {aChart bChart δ G : ℝ}
    (haChart : 0 ≤ aChart) (hbChart : 0 ≤ bChart) (hδ : 0 < δ)
    (P Pbase O : ℕ → ℝ) (hPbase : ∀ d, 0 ≤ Pbase d) (hO : ∀ j, 0 ≤ O j) :
    let K := comparableJointCarrier c C a b Z Kb (frequencyAnnulus a b)
    ∃ (bLoss : ℕ) (Cq : ℕ → ℝ) (C₀ : ℝ), (∀ q, 0 ≤ Cq q) ∧ 0 ≤ C₀ ∧
    ∀ (mi mo : LocalizerSymbol n) {I Ko Oo : Set (Euclidean n × Euclidean n)},
    tsupport mi ⊆ I → ContDiff ℝ ∞ mi → (∀ p, mi p ∈ Icc (0 : ℝ) 1) →
    IsBufferedLocalizer mo Ko Oo → tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a b →
    (∀ j p, ‖iteratedFDeriv ℝ j mo p‖ ≤ O j) →
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
    (∀ x ∈ X, ∀ y ∈ Ki, ∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
    (∀ x ∈ X, ∀ y ∈ Ki, ∀ p ∈ K, ∀ d, 1 ≤ d →
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
    ∃ (J : ℕ → ℕ × ℕ → ℝ) (J₀ : ℕ × ℕ → ℝ),
      (∀ q p, 0 ≤ J q p) ∧ (∀ p, 0 ≤ J₀ p) ∧
      (∀ q, Summable (J q)) ∧ Summable J₀ ∧
      (∀ q, (∑' p, J q p) ≤ Cq q * ρ ^ ((m : ℝ) + (max 0 s + (3 * n : ℕ))) *
        L ^ bLoss * (L / ρ) ^ q) ∧
      ((∑' p, J₀ p) ≤ C₀ * ρ ^ (max 0 s + (3 * n : ℕ)) * L ^ bLoss) ∧
      (∀ j k x, x ∈ X → ∀ y q (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (graphCutoff j) (outputCutoff k) t y) x v‖ ≤ J q (j,k)) ∧
      (∀ j k x y, ‖KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphCutoff j) (outputCutoff k) x y‖ ≤ J₀ (j,k)) ∧
      ∀ j k, ContDiff ℝ ∞ (Function.uncurry (KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphCutoff j) (outputCutoff k))) := by
  classical
  intro K
  obtain ⟨Bc, Bc₀, hBc, hBc₀, hcBound⟩ := exists_supported_comparable_pair_constants_of_uniform_masks
    (r := r) (G := G) e backward s m c C a b ha X
    hZ hKb hKi (isCompact_frequencyAnnulus a b) D haChart hbChart hδ P O hO
  obtain ⟨Nm, Bm, hBm, hmBound⟩ := exists_conicPhysicalPair_bound_of_primitive_grades
    (r := r) (C := C) (b := b) eu ez backward hc (show (0 : ℝ) ≤ 1 by norm_num) ha hKb
    Pbase D.symbol D.outputMask hPbase D.symbol_nonneg D.outputMask_nonneg
    s 0 0 0 D.outputMaskOffset D.symbolOffset m
  obtain ⟨N₀, B₀, hB₀, hzeroBound⟩ := exists_conicPhysicalPair_bound_of_primitive_grades
    (r := r) (C := C) (b := b) eu ez backward hc (show (0 : ℝ) ≤ 1 by norm_num) ha hKb
    Pbase D.symbol D.outputMask hPbase D.symbol_nonneg D.outputMask_nonneg
    s 0 0 0 D.outputMaskOffset D.symbolOffset 0
  obtain ⟨M, hM, hmass⟩ := exists_graphPairWeight_mass hn c C b ha
  let dc := D.outputMaskOffset + D.inputMaskOffset + D.symbolOffset
  let dm := 0 + (m + D.outputMaskOffset) + D.symbolOffset + Nm + 2
  let d₀ := 0 + (0 + D.outputMaskOffset) + D.symbolOffset + N₀ + 2
  let loss := (m + dc) + dm + d₀
  let Bq := fun q => Bc q + Bm q
  let Bzero := Bc₀ + B₀ 0
  have hBq q : 0 ≤ Bq q := add_nonneg (hBc q) (hBm q)
  have hBzero : 0 ≤ Bzero := add_nonneg hBc₀ (hB₀ 0)
  refine ⟨loss, fun q => Bq q * M, Bzero * M,
    fun q => mul_nonneg (hBq q) hM, mul_nonneg hBzero hM, ?_⟩
  intro mi mo I Ko Oo hi hiSmooth hiRange ho hiSupport hmoJoint ρ L hL hLρ S φ A κ U T V Kphase g hscale hS hU hT hTU hφ hZT
    hpoints hchart hgap hA hbase hcarrier hsymbol hin hupper hp
    hV hSV hKphase hKV hphysical hg hcomp hpbase hAbase hout
  have hρ := hL.trans hLρ
  have hρ0 := zero_lt_one.trans_le hρ
  have hL0 := zero_le_one.trans hL
  let E : ℝ := max 0 s + (3 * n : ℕ)
  let F := fun q => Bq q * ρ ^ ((m : ℝ) + E) * L ^ loss * (L / ρ) ^ q
  let F₀ := Bzero * ρ ^ E * L ^ loss
  have hF q : 0 ≤ F q := by
    have := hBq q
    dsimp [F]
    positivity
  have hF₀ : 0 ≤ F₀ := by dsimp [F₀]; positivity
  have hiZero : ∀ y η, (y, η) ∉ Ki ×ˢ frequencyAnnulus a b → mi (y, η) = 0 := by
    intro y η hy
    exact image_eq_zero_of_notMem_tsupport (fun hh => hy (hiSupport hh))
  have hiFreq y : tsupport (fun η => mi (y, η)) ⊆ frequencyAnnulus a b := by
    apply closure_minimal _ (isCompact_frequencyAnnulus a b).isClosed
    intro η hη
    exact (hiSupport (subset_tsupport _ hη)).2
  have hiNorm y η : ‖mi (y, η)‖ ≤ (ρ ^ (0 : ℝ) * 1) * L ^ (0 : ℕ) := by
    simpa only [Real.rpow_zero, one_mul, pow_zero, Real.norm_eq_abs,
      abs_of_nonneg (hiRange (y, η)).1] using (hiRange (y, η)).2
  have hoGrade k x ζ d : ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤
      ((2 : ℝ) ^ k) ^ (0 : ℝ) * D.outputMask d * L ^ (d + D.outputMaskOffset) := by
    simpa only [Real.rpow_zero, one_mul] using hout x ζ d
  let cg j k := cutoffPairCarriers A mi Kb Ki (frequencyAnnulus a b)
    hKb hKi (isCompact_frequencyAnnulus a b) hbase hiZero j k
  let cb (low : Bool) j k :
      KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k) :=
    { cg j k with compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j }
  have hmi : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => mi (p.1, ρ⁻¹ • p.2)) :=
    hiSmooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hmo : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => mo (p.1, ρ⁻¹ • p.2)) :=
    ho.smooth.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))
  have hsmooth low j k : ContDiff ℝ ∞ (Function.uncurry
      (KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k))) := by
    apply contDiff_regularizedJointKernel_of_conicPhase backward S A _ _ _ _
      (physicalInputCarriers (cb low j k) hρ0.ne') hV (hKphase low j) (hKV low j) hSV
      (physicalBranch_support_of_normalized hρ0.ne' A low j (hphysical low j))
      hA hmi hmo (contDiff_graphBranchCutoff low j) (contDiff_outputCutoff k)
    cases low
    · exact zero_notMem_tsupport_highGraphCutoff j
    · exact zero_notMem_tsupport_lowGraphCutoff j
  have hE : s + (3 * n : ℕ) ≤ E := by dsimp [E]; linarith [le_max_right (0 : ℝ) s]
  have hnE : (n : ℝ) ≤ E := by
    dsimp [E]
    have := le_max_left (0 : ℝ) s
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnmE : (n : ℝ) ≤ (m : ℝ) + E := by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hsmoothOutput low j k y : ContDiff ℝ ∞ (fun t =>
      KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) t y) :=
    (hsmooth low j k).comp (f := fun t : Euclidean n => (t, y))
      (contDiff_id.prodMk contDiff_const)
  have hbranch low j k :
      (∀ x ∈ X, ∀ y q (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
          F q * regimePairWeight n c C a b ρ low (j,k)) ∧
      (∀ x y, ‖KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
          F₀ * regimePairWeight n c C a b ρ low (j,k)) := by
    rcases comparable_or_separated c C a b ρ low j k with hpair | hsep
    · have hh := hcBound mi mo hi hiSmooth ho hiSupport hmoJoint ρ L hL hLρ low j k hpair S φ κ U T hscale hS hU hT hTU
        hφ hZT hpoints hchart hgap A hA hbase (hcarrier low j k hpair)
        hsymbol hin hupper hp
      simp only [comparableAmplitudeProfiles, AmplitudeProfiles.offset, Nat.zero_add] at hh
      have hw : regimePairWeight n c C a b ρ low (j,k) = 1 := by
        simp only [regimePairWeight, hpair, ↓reduceIte]
      simp only [hw, mul_one]
      constructor
      · intro x hx y q v hv
        apply (hh.1 x hx y q v hv).trans
        change Bc q * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) * L ^ (m + dc) *
          (L / ρ) ^ q ≤ F q
        exact scale_bound_mono hρ hL (hBc q) (le_add_of_nonneg_right (hBm q))
          (by linarith) (by dsimp [loss]; omega)
      · intro x y
        apply (hh.2 x y).trans
        change Bc₀ * ρ ^ (s + (3 * n : ℕ)) * L ^ dc ≤ F₀
        simpa only [pow_zero, mul_one] using
          (scale_bound_mono (q := 0) hρ hL hBc₀ (le_add_of_nonneg_right (hB₀ 0)) hE
            (show dc ≤ loss by dsimp [loss]; omega))
    · have hpair : ¬ IsComparablePair c C a b ρ low j k := fun hh => hh hsep
      have hw : regimePairWeight n c C a b ρ low (j,k) = pairWeight low n j k := by
        simp only [regimePairWeight, hpair, ↓reduceIte]
      simp only [hw]
      have hm := hmBound ρ L hρ hL S A mi mo low j k
      have hz := hzeroBound ρ L hρ hL S A mi mo low j k
      constructor
      · intro x _ y q v hv
        have hh := hm x y V (Kphase low j) g hV (hKphase low j) (hKV low j) hSV
          (hphysical low j) hA hiSmooth ho.smooth hbase (hiFreq y) hsep hg hcomp
          (hpbase low j) (hAbase low j) (fun η _ => hiNorm y η)
          (fun ζ _ d => hoGrade k x ζ d) (cb low j k) q v hv
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (pairWeight_nonneg low n j k)
        rw [← Real.rpow_natCast]
        exact scale_bound_mono hρ hL (hBm q) (le_add_of_nonneg_left (hBc q)) hnmE
          (show dm ≤ loss by dsimp [loss]; omega)
      · intro x y
        have hh := hz x y V (Kphase low j) g hV (hKphase low j) (hKV low j) hSV
          (hphysical low j) hA hiSmooth ho.smooth hbase (hiFreq y) hsep hg hcomp
          (hpbase low j) (hAbase low j) (fun η _ => hiNorm y η)
          (fun ζ _ d => hoGrade k x ζ d) (cb low j k) 0 (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i)
        simp only [iteratedFDeriv_zero_apply, pow_zero, mul_one] at hh
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (pairWeight_nonneg low n j k)
        rw [← Real.rpow_natCast]
        simpa only [pow_zero, mul_one] using
          (scale_bound_mono (q := 0) hρ hL (hB₀ 0) (le_add_of_nonneg_left hBc₀) hnE
            (show d₀ ≤ loss by dsimp [loss]; omega))
  let J := fun q p => F q * graphPairWeight n c C a b ρ p
  let J₀ := fun p => F₀ * graphPairWeight n c C a b ρ p
  obtain ⟨hw, hwsum⟩ := hmass ρ hρ
  refine ⟨J, J₀, (fun q p => mul_nonneg (hF q) (graphPairWeight_nonneg ..)),
    (fun p => mul_nonneg hF₀ (graphPairWeight_nonneg ..)),
    (fun q => hw.mul_left (F q)), hw.mul_left F₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    dsimp [J]
    rw [tsum_mul_left]
    apply (mul_le_mul_of_nonneg_left hwsum (hF q)).trans_eq
    dsimp [F, E]
    ring
  · dsimp [J₀]
    rw [tsum_mul_left]
    apply (mul_le_mul_of_nonneg_left hwsum hF₀).trans_eq
    dsimp [F₀, E]
    ring
  · intro j k x hx y q v hv
    rw [iteratedFDeriv_physicalGraphCutoff_split backward S A _ _ j k hS hA.continuous
      hmi.continuous hmo.continuous (physicalInputCarriers (cg j k) hρ0.ne') y
      (fun low => hsmoothOutput low j k y) m x v]
    exact (norm_add_le _ _).trans ((add_le_add
      ((hbranch false j k).1 x hx y q v hv)
      ((hbranch true j k).1 x hx y q v hv)).trans_eq (by dsimp [J, graphPairWeight]; ring))
  · intro j k x y
    rw [regularizedJointKernel_graphCutoff_split backward S A _ _ j k hS hA.continuous
      hmi.continuous hmo.continuous (physicalInputCarriers (cg j k) hρ0.ne') x y]
    exact (norm_add_le _ _).trans ((add_le_add
      ((hbranch false j k).2 x y) ((hbranch true j k).2 x y)).trans_eq
        (by dsimp [J₀, graphPairWeight]; ring))
  · intro j k
    have he : Function.uncurry (KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphCutoff j) (outputCutoff k)) =
        Function.uncurry (KernelLimits.regularizedJointKernel backward S A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff false j) (outputCutoff k)) +
        Function.uncurry (KernelLimits.regularizedJointKernel backward S A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff true j) (outputCutoff k)) := by
      funext p
      exact regularizedJointKernel_graphCutoff_split backward S A _ _ j k hS hA.continuous
        hmi.continuous hmo.continuous (physicalInputCarriers (cg j k) hρ0.ne') p.1 p.2
    rw [he]
    exact (hsmooth false j k).add (hsmooth true j k)


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
