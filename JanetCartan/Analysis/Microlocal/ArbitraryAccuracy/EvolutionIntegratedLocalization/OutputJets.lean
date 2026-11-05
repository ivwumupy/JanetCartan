module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.AmplitudeGrades
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.BufferedJets

/-!
# Joint elapsed grades of the actual output jets

The output-derivative step of `app:ch_regular:eq:chain-tail` uses Graph's
literal differentiated integrand. The derivative variables here include
elapsed time, both amplitude positions and all three covectors. The
two-time amplitude bounds are supplied by `AmplitudeGrades`, including the
fixed elapsed extension cutoff. No per-time estimate is substituted for a
joint estimate. The same closed input and complementary output supports
work for every output order and both literal orientations.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The actual demodulated output jet, with the fixed elapsed extension
cutoff. This is the amplitude under the differentiated half-space integral
in `app:ch_regular:eq:chain-tail`. -/
def cutElapsedOutputJetAmplitude (backward : Bool) (ρ : ℝ) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (m : ℕ) (v : Fin m → Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) : Matrix (Fin q) (Fin q) ℂ :=
  θ p.1 • outputJetAmplitude backward ρ (elapsedPhase Ψ p.1)
    (orientedElapsedAmplitude backward b χout χsource β p.1) mi mo χA χo x y m v p.2

/-- The exact output-jet formula extracts `ρ^m` and retains every physical
mask and the complete output-symbol jet, including its identity contribution
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem cutElapsedOutputJetAmplitude_eq_scaled_symbolJet
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (m : ℕ) (v : Fin m → Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1))) :
    cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v p =
      ρ ^ m • (graphOutputSymbolJet ρ mo x m v p.2.2.2.2 •
        (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          χA χo 0 y p)) := by
  unfold cutElapsedOutputJetAmplitude
  rw [outputJetAmplitude_eq_scaled_symbolJet backward hρ _ _ mi mo χA χo x y m v ho]
  rw [smul_comm (θ p.1) (ρ ^ m : ℝ), smul_comm (θ p.1)]
  rfl

private def elapsedOutputCovectorProjection :
    (ℝ × JointVariables (Euclidean (d + 1))) →L[ℝ] Euclidean (d + 1) :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))

private theorem norm_elapsedOutputCovectorProjection_le :
    ‖elapsedOutputCovectorProjection (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p.2.2.2.2‖ ≤ 1 * ‖p‖
  simpa only [one_mul] using (norm_snd_le p.2.2.2).trans
    ((norm_snd_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p)))

/-- Joint smoothness of the actual output jet, including elapsed time,
follows from the output-independent masked amplitude and the original
output symbol. The original phase cancels exactly in the demodulation
(`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_cutElapsedOutputJetAmplitude
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p)) (m : ℕ) (v : Fin m → Euclidean (d + 1)) :
    ContDiff ℝ ∞
      (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v) := by
  simp_rw [funext (cutElapsedOutputJetAmplitude_eq_scaled_symbolJet
    backward hρ Ψ b χout χsource β mi mo χA χo θ x y ho m v)]
  exact (((contDiff_graphOutputSymbolJet ρ ho x m v).comp
    (elapsedOutputCovectorProjection (d := d)).contDiff).smul ha).const_smul (ρ ^ m : ℝ)

/-- Primitive output-mask grades and the joint elapsed-amplitude grades
give all joint derivatives of the output jet. The amplitude premise is
produced by `norm_iteratedFDeriv_cut_jointElapsedAmplitude_le` with zero
output mask; it is not an integrated estimate. The fixed offset is
`m + bo + ba`, independent of integration accuracy
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_cutElapsedOutputJetAmplitude_le
    (backward : Bool) {ρ S L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (ha : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y p))
    {W O A : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bo ba m : ℕ) (v : Fin m → Euclidean (d + 1)) (hv : ∀ i, ‖v i‖ ≤ 1)
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hw : ∀ k, ‖iteratedFDeriv ℝ k outputJointWave (0, p.2.2.2.2)‖ ≤ W k)
    (hmo : ∀ k, ‖iteratedFDeriv ℝ k mo (x, p.2.2.2.2)‖ ≤ O k * L ^ (k + bo))
    (hab : ∀ k, ‖iteratedFDeriv ℝ k (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ w.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        χA χo 0 y w) p‖ ≤ S * A k * L ^ (k + ba)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j
      (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v) p‖ ≤
      (ρ ^ m * S) *
        derivativeConvolution (fun k ↦ derivativeConvolution W (fun i ↦ 1 + O i) (m + k)) A j *
        L ^ (j + ((m + bo) + ba)) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  let g := graphOutputSymbolJet ρ mo x m v
  let π := elapsedOutputCovectorProjection (d := d)
  have hsg : ContDiff ℝ ∞ g := contDiff_graphOutputSymbolJet ρ ho x m v
  have hG k : 0 ≤ derivativeConvolution W (fun i ↦ 1 + O i) (m + k) :=
    derivativeConvolution_nonneg hW (fun i ↦ by linarith [hO i]) _
  have hg k : ‖iteratedFDeriv ℝ k (g ∘ π) p‖ ≤
      derivativeConvolution W (fun i ↦ 1 + O i) (m + k) * L ^ (k + (m + bo)) := by
    have hb k := (norm_iteratedFDeriv_rescaled_graphMask_le ho hρ x k
      (0, p.2.2.2.2)).trans (by simpa only [smul_zero, add_zero] using hmo k)
    have h := norm_iteratedFDeriv_graphOutputSymbolJet_le ρ ho x hW hO hL bo m k v hv
      p.2.2.2.2 hw hb
    simpa only [one_pow, one_mul, mul_one] using
      norm_iteratedFDeriv_comp_linear_le_grades hsg π zero_le_one
        norm_elapsedOutputCovectorProjection_le hG (S := 1) zero_le_one (zero_le_one.trans hL)
        (m + bo) p k (by simpa [g, π, elapsedOutputCovectorProjection] using h)
  have hb := norm_iteratedFDeriv_smul_le_amplitude_grades (hsg.comp π.contDiff)
    ha hG (zero_le_one.trans hL) (m + bo) ba p hg hab j
  have he := funext (cutElapsedOutputJetAmplitude_eq_scaled_symbolJet
    backward hρ0.ne' Ψ b χout χsource β mi mo χA χo θ x y ho m v)
  have hprod : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      graphOutputSymbolJet ρ mo x m v w.2.2.2.2 •
        (θ w.1 • jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          χA χo 0 y w)) := (hsg.comp π.contDiff).smul ha
  rw [he, iteratedFDeriv_const_smul_apply' (a := (ρ ^ m : ℝ))
    (hprod.contDiffAt.of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (pow_nonneg hρ0.le m)]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hρ0.le m)).trans_eq (by ring)

/-- The same compact output-independent carrier controls every joint
elapsed output jet (`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_cutElapsedOutputJetAmplitude_subset
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (m : ℕ) (v : Fin m → Euclidean (d + 1)) :
    tsupport (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo
      χA χo θ x y m v) ⊆
    tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0) χA χo 0 y p) := by
  rw [funext (cutElapsedOutputJetAmplitude_eq_scaled_symbolJet
    backward hρ Ψ b χout χsource β mi mo χA χo θ x y ho m v)]
  exact (tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_right _ _)

/-- Output differentiation preserves the closed source shoulders and the
closed support of the full output complement in the JOINT elapsed variables.
Thus the same diagonal and zero-energy buffers apply to every differentiated
kernel; no arbitrary-energy fixed-time protection is inferred
(`app:ch_regular:lem:finite-chain`). -/
theorem cutElapsedOutputJetAmplitude_tsupport_input_complement
    (backward : Bool) (ρ : ℝ) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    (m : ℕ) (v : Fin m → Euclidean (d + 1))
    {p : ℝ × JointVariables (Euclidean (d + 1))}
    (hp : p ∈ tsupport (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β
      mi mo χA χo θ x y m v)) :
    (y, p.2.2.2.1) ∈ tsupport mi ∧
      (x, p.2.2.2.2) ∈ tsupport (fun z ↦ 1 - mo z) := by
  apply closure_minimal (s := Function.support (cutElapsedOutputJetAmplitude
    backward ρ Ψ b χout χsource β mi mo χA χo θ x y m v))
    (t := {p : ℝ × JointVariables (Euclidean (d + 1)) |
      (y, p.2.2.2.1) ∈ tsupport mi ∧
        (x, p.2.2.2.2) ∈ tsupport (fun z ↦ 1 - mo z)}) ?_ ?_ hp
  · intro w hw
    have hn : outputJetAmplitude backward ρ (elapsedPhase Ψ w.1)
        (orientedElapsedAmplitude backward b χout χsource β w.1)
        mi mo χA χo x y m v w.2 ≠ 0 := by
      intro hz
      exact hw (by simp only [cutElapsedOutputJetAmplitude, hz, smul_zero])
    exact outputJetAmplitude_tsupport_input_complement backward ρ _ _ mi mo χA χo x y
      ho m v (subset_tsupport _ hn)
  · exact ((isClosed_tsupport mi).preimage (by fun_prop)).inter
      ((isClosed_tsupport (fun z ↦ 1 - mo z)).preimage (by fun_prop))

/-- The common compact carrier intersected with the actual closed input
shoulders and full output complement. Its boundary and interior gaps are
supplied by the geometric buffer deductions, uniformly in output order
(`app:ch_regular:eq:chain-tail`). -/
def elapsedOutputJetCarrier (K : Set (ℝ × JointVariables (Euclidean (d + 1))))
    (mi mo : LocalizerSymbol (d + 1)) (x y : Euclidean (d + 1)) :
    Set (ℝ × JointVariables (Euclidean (d + 1))) :=
  K ∩ {p | (y, p.2.2.2.1) ∈ tsupport mi ∧
    (x, p.2.2.2.2) ∈ tsupport (fun z ↦ 1 - mo z)}

/-- The buffered carrier is compact even though the identity contribution
in `1-mo` has unbounded support (`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_elapsedOutputJetCarrier
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (mi mo : LocalizerSymbol (d + 1)) (x y : Euclidean (d + 1)) :
    IsCompact (elapsedOutputJetCarrier K mi mo x y) :=
  hK.inter_right (((isClosed_tsupport mi).preimage (by fun_prop)).inter
    ((isClosed_tsupport (fun z ↦ 1 - mo z)).preimage (by fun_prop)))

/-- Every output order has support in the same buffered compact carrier.
Consumer: the two-branch differentiated half-space bound in
`app:ch_regular:eq:chain-tail`. -/
theorem tsupport_cutElapsedOutputJetAmplitude_subset_bufferedCarrier
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Ψ : TwoTimePhase d)
    (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : Euclidean (d + 1) → ℝ)
    (θ : ℝ → ℂ) (x y : Euclidean (d + 1)) (ho : ContDiff ℝ ∞ mo)
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))}
    (hs : tsupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0) χA χo 0 y p) ⊆ K)
    (m : ℕ) (v : Fin m → Euclidean (d + 1)) :
    tsupport (cutElapsedOutputJetAmplitude backward ρ Ψ b χout χsource β mi mo
      χA χo θ x y m v) ⊆ elapsedOutputJetCarrier K mi mo x y := by
  intro p hp
  exact ⟨hs (tsupport_cutElapsedOutputJetAmplitude_subset backward hρ Ψ b χout χsource β
    mi mo χA χo θ x y ho m v hp),
    cutElapsedOutputJetAmplitude_tsupport_input_complement backward ρ Ψ b χout χsource β
      mi mo χA χo θ x y ho m v hp⟩

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
