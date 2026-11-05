module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputDerivatives
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades.MixedJets

/-!
# Primitive grades for graph output jets

The consumer is the differentiated joint integral in `app:ch_regular:eq:chain-tail`.
The joint output-symbol grades include base and covector derivatives. Leibniz
and mixed-jet estimates derive the full differentiated amplitude bound; its
fixed grade offset is independent of the integration order.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral Retarded.KernelDecay
variable {n r : ℕ}

/-- Fixed Fourier character in the output increment and normalized covector
(`app:ch_regular:eq:joint-kernel-phase`). -/
def outputJointWave (p : Euclidean n × Euclidean n) : ℂ :=
  Complex.exp ((inner ℝ p.1 p.2 : ℝ) * Complex.I)

/-- Smoothness of the fixed output Fourier character (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_outputJointWave : ContDiff ℝ ∞ (outputJointWave (n := n)) :=
  Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_fst.inner ℝ contDiff_snd)).mul contDiff_const)

/-- Compact normalized output covectors give one profile before the frequency,
external bases and derivative orders are chosen (`app:ch_regular:eq:chain-tail`). -/
theorem exists_outputJointWave_profile {K : Set (Euclidean n)} (hK : IsCompact K) :
    ∃ W : ℕ → ℝ, (∀ j, 0 ≤ W j) ∧ ∀ j ξ, ξ ∈ K →
      ‖iteratedFDeriv ℝ j outputJointWave (0, ξ)‖ ≤ W j := by
  have hb j := hK.exists_bound_of_continuousOn
    (((contDiff_outputJointWave (n := n)).iteratedFDeriv_right (m := ∞) (i := j)
      (by simp)).continuous.comp
      ((continuous_const (y := (0 : Euclidean n))).prodMk continuous_id)).continuousOn
  choose C hC using hb
  exact ⟨fun j => max 0 (C j), fun j => le_max_left _ _,
    fun j ξ hξ => (hC j ξ hξ).trans (le_max_right _ _)⟩

/-- The normalized scalar jet after extracting `ρ^m` from the actual output
jet (`app:ch_regular:eq:chain-tail`). -/
def graphOutputSymbolJet (ρ : ℝ) (mo : LocalizerSymbol n) (x : Euclidean n)
    (m : ℕ) (v : Fin m → Euclidean n) (ξ : Euclidean n) : ℂ :=
  iteratedFDeriv ℝ m (fun t => outputJointWave (t, ξ) *
    (1 - (mo (x + ρ⁻¹ • t, ξ) : ℂ))) 0 v

set_option maxHeartbeats 800000 in
/-- Smoothness of the residual scalar output jet (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_graphOutputSymbolJet (ρ : ℝ) {mo : LocalizerSymbol n}
    (ho : ContDiff ℝ ∞ mo) (x : Euclidean n) (m : ℕ) (v : Fin m → Euclidean n) :
    ContDiff ℝ ∞ (graphOutputSymbolJet ρ mo x m v) := by
  have hs : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n =>
      outputJointWave p * (1 - (mo (x + ρ⁻¹ • p.1, p.2) : ℂ))) :=
    contDiff_outputJointWave.mul (contDiff_const.sub
      (Complex.ofRealCLM.contDiff.comp (ho.comp
        ((contDiff_const.add (contDiff_fst.const_smul ρ⁻¹)).prodMk contDiff_snd))))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Euclidean n) ℂ v).contDiff.comp
    ((contDiff_outputJet hs m).comp (contDiff_const.prodMk contDiff_id))

/-- Every covector derivative of the scalar output jet follows from primitive
joint symbol grades and the fixed wave profile. The identity in `1-mo` is
retained (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_graphOutputSymbolJet_le (ρ : ℝ)
    {mo : LocalizerSymbol n} (ho : ContDiff ℝ ∞ mo) (x : Euclidean n)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    {L : ℝ} (hL : 1 ≤ L) (bo m j : ℕ) (v : Fin m → Euclidean n)
    (hv : ∀ i, ‖v i‖ ≤ 1) (ξ : Euclidean n)
    (hw : ∀ k, ‖iteratedFDeriv ℝ k outputJointWave (0, ξ)‖ ≤ W k)
    (hb : ∀ k, ‖iteratedFDeriv ℝ k (fun p : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • p.1, p.2) : ℂ)) (0, ξ)‖ ≤ O k * L ^ (k + bo)) :
    ‖iteratedFDeriv ℝ j (graphOutputSymbolJet ρ mo x m v) ξ‖ ≤
      derivativeConvolution W (fun k => 1 + O k) (m + j) * L ^ (j + (m + bo)) := by
  let o : Euclidean n × Euclidean n → ℂ := fun p => (mo (x + ρ⁻¹ • p.1, p.2) : ℂ)
  have hso : ContDiff ℝ ∞ o := Complex.ofRealCLM.contDiff.comp
    (ho.comp ((contDiff_const.add (contDiff_fst.const_smul ρ⁻¹)).prodMk contDiff_snd))
  have hs := contDiff_outputJointWave.mul ((contDiff_const (c := (1 : ℂ))).sub hso)
  apply (norm_iteratedFDeriv_outputJet_apply_le hs m j v hv 0 ξ).trans
  have hw' k : ‖iteratedFDeriv ℝ k outputJointWave (0, ξ)‖ ≤
      1 * W k * L ^ (k + 0) := by
    simpa using (hw k).trans (le_mul_of_one_le_right (hW k) (one_le_pow₀ hL))
  have hc k := norm_iteratedFDeriv_one_sub_le_grades hso (S := 1) le_rfl hL bo
    (0, ξ) (fun k => by simpa using hb k) k
  have h := norm_iteratedFDeriv_mul_le_grades contDiff_outputJointWave
    (contDiff_const.sub hso) hW (fun k => by linarith [hO k])
    zero_le_one zero_le_one (zero_le_one.trans hL) 0 bo (0, ξ) hw' hc (m + j)
  simpa only [one_mul, zero_add, Nat.add_assoc, Nat.add_comm m j] using h

private def outputCovectorProjection : JointVariables (Euclidean n) →L[ℝ] Euclidean n :=
  (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
    ((ContinuousLinearMap.snd ℝ (Euclidean n) _).comp (ContinuousLinearMap.snd ℝ _ _))

private theorem norm_outputCovectorProjection_le : ‖outputCovectorProjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p.2.2.2‖ ≤ 1 * ‖p‖
  simpa only [one_mul] using
    (norm_snd_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p))

/-- Explicit Leibniz profile of all the differentiated full-amplitude factors
(`app:ch_regular:eq:chain-tail`). -/
def AmplitudeProfiles.outputJetProfile (D : AmplitudeProfiles) (W O : ℕ → ℝ)
    (m : ℕ) : ℕ → ℝ :=
  derivativeConvolution (fun j => derivativeConvolution W (fun k => 1 + O k) (m + j))
    D.productProfile

/-- The output-jet constants are nonnegative (`app:ch_regular:eq:chain-tail`). -/
theorem AmplitudeProfiles.outputJetProfile_nonneg (D : AmplitudeProfiles)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j) (m j : ℕ) :
    0 ≤ D.outputJetProfile W O m j :=
  derivativeConvolution_nonneg
    (fun _ => derivativeConvolution_nonneg hW (fun k => by linarith [hO k]) _)
    D.productProfile_nonneg j

/-- Smoothness of the actual demodulated jet follows without phase regularity:
the output phase cancels exactly (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_outputJetAmplitude (backward : Bool) {ρ S L : ℝ} (hρ : ρ ≠ 0)
    (φ : Euclidean n → Euclidean n → ℝ) {A : FullAmplitude n r}
    {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ} (x y : Euclidean n)
    {D : AmplitudeProfiles} {K : Set (JointVariables (Euclidean n))}
    (ha : HasAmplitudeGrades D ρ S L A mi (fun _ => 0) χA χo 0 y K)
    (ho : ContDiff ℝ ∞ mo) (m : ℕ) (v : Fin m → Euclidean n) :
    ContDiff ℝ ∞ (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v) := by
  have he : outputJetAmplitude backward ρ φ A mi mo χA χo x y m v =
      ρ ^ m • (fun p => graphOutputSymbolJet ρ mo x m v p.2.2.2 •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) := by
    funext p
    exact outputJetAmplitude_eq_scaled_symbolJet backward hρ φ A mi mo χA χo x y m v ho p
  rw [he]
  exact (((contDiff_graphOutputSymbolJet ρ ho x m v).comp
    (outputCovectorProjection (n := n)).contDiff).smul ha.contDiff_jointAmplitude).const_smul (ρ ^ m : ℝ)

/-- Full grades of the actual output jet, proved from the primitive factors.
The symbol scale `S` can be `ρ^s` for any real order, including negative orders.
The output order contributes `ρ^m` and a fixed grade offset `m+bo`; neither
fixed loss depends on the integration order (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_outputJetAmplitude_le (backward : Bool) {ρ S L : ℝ}
    (hρ : 0 < ρ) (hL : 1 ≤ L) (φ : Euclidean n → Euclidean n → ℝ)
    {A : FullAmplitude n r} {mi mo : LocalizerSymbol n} {χA χo : Euclidean n → ℝ}
    (x y : Euclidean n) {D : AmplitudeProfiles} {K : Set (JointVariables (Euclidean n))}
    (ha : HasAmplitudeGrades D ρ S L A mi (fun _ => 0) χA χo 0 y K)
    (ho : ContDiff ℝ ∞ mo) {W O : ℕ → ℝ}
    (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bo m : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (p : JointVariables (Euclidean n)) (hp : p ∈ K)
    (hw : ∀ k, ‖iteratedFDeriv ℝ k outputJointWave (0, p.2.2.2)‖ ≤ W k)
    (hb : ∀ k, ‖iteratedFDeriv ℝ k (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ O k * L ^ (k + bo)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v) p‖ ≤
      (ρ ^ m * S) * D.outputJetProfile W O m j * L ^ (j + ((m + bo) + D.offset)) := by
  let g := graphOutputSymbolJet ρ mo x m v
  let π := outputCovectorProjection (n := n)
  have hsg : ContDiff ℝ ∞ g := contDiff_graphOutputSymbolJet ρ ho x m v
  have hG k : 0 ≤ derivativeConvolution W (fun i => 1 + O i) (m + k) :=
    derivativeConvolution_nonneg hW (fun i => by linarith [hO i]) _
  have hg k : ‖iteratedFDeriv ℝ k (g ∘ π) p‖ ≤
      derivativeConvolution W (fun i => 1 + O i) (m + k) * L ^ (k + (m + bo)) := by
    have h := norm_iteratedFDeriv_graphOutputSymbolJet_le ρ ho x hW hO hL bo m k v hv
      p.2.2.2 hw hb
    simpa only [one_pow, one_mul, mul_one] using
      norm_iteratedFDeriv_comp_linear_le_grades hsg π zero_le_one
        norm_outputCovectorProjection_le hG (S := 1) zero_le_one (zero_le_one.trans hL)
        (m + bo) p k (by simpa [g, π, outputCovectorProjection] using h)
  have hab := norm_iteratedFDeriv_smul_le_amplitude_grades (hsg.comp π.contDiff)
    ha.contDiff_jointAmplitude hG (zero_le_one.trans hL) (m + bo) D.offset p hg
    (fun k => ha.norm_iteratedFDeriv_jointAmplitude_le hL p hp k) j
  have he : outputJetAmplitude backward ρ φ A mi mo χA χo x y m v =
      ρ ^ m • (fun p => (g ∘ π) p • jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) := by
    funext p
    exact outputJetAmplitude_eq_scaled_symbolJet backward hρ.ne' φ A mi mo χA χo x y m v ho p
  have hprod : ContDiff ℝ ∞ (fun p => (g ∘ π) p •
      jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p) :=
    (hsg.comp π.contDiff).smul ha.contDiff_jointAmplitude
  rw [he, iteratedFDeriv_const_smul_apply (hprod.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_of_nonneg (pow_nonneg hρ.le m)]
  exact (mul_le_mul_of_nonneg_left hab (pow_nonneg hρ.le m)).trans_eq (by
    dsimp only [AmplitudeProfiles.outputJetProfile]; ring)

/-- Output jets retain the carrier of the output-independent amplitude.
This covers source shoulders and either orientation without any compactness
assumption on the complementary output mask (`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_outputJetAmplitude_subset (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (ho : ContDiff ℝ ∞ mo) (m : ℕ) (v : Fin m → Euclidean n) :
    tsupport (outputJetAmplitude backward ρ φ A mi mo χA χo x y m v) ⊆
      tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) := by
  have he : outputJetAmplitude backward ρ φ A mi mo χA χo x y m v = fun p =>
      iteratedFDeriv ℝ m (fun t =>
        Complex.exp ((inner ℝ t (ρ • p.2.2.2) : ℂ) * Complex.I) *
          (1 - (mo (x + t, p.2.2.2) : ℂ))) 0 v •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p := by
    funext p
    exact outputJetAmplitude_eq_symbolJet backward ρ φ A mi mo χA χo x y m v ho p
  rw [he]
  exact tsupport_smul_subset_right _ _

/-- The mixed-jet premise for the normalized output mask is controlled by the
primitive mask jet: rescaling its base by `ρ⁻¹` is a contraction for `ρ ≥ 1`.
Thus the hypothesis in the output decay estimate requires no derivative bound
on a composed amplitude (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_rescaled_graphMask_le {mo : LocalizerSymbol n}
    (ho : ContDiff ℝ ∞ mo) {ρ : ℝ} (hρ : 1 ≤ ρ) (x : Euclidean n)
    (j : ℕ) (p : Euclidean n × Euclidean n) :
    ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) p‖ ≤
      ‖iteratedFDeriv ℝ j mo (x + ρ⁻¹ • p.1, p.2)‖ := by
  let a : (Euclidean n × Euclidean n) →L[ℝ] Euclidean n × Euclidean n :=
    (ρ⁻¹ • ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).prod
      (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n))
  have ha : ‖a‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖(ρ⁻¹ • q.1, q.2)‖ ≤ 1 * ‖q‖
    rw [one_mul, Prod.norm_def, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hρ))]
    exact max_le ((mul_le_of_le_one_left (norm_nonneg _)
      (inv_le_one_of_one_le₀ hρ)).trans (norm_fst_le q)) (norm_snd_le q)
  let g : Euclidean n × Euclidean n → ℝ := fun q => mo ((x, 0) + q)
  have hg : ContDiff ℝ ∞ g := ho.comp (contDiff_const.add contDiff_id)
  have he : (fun t : Euclidean n × Euclidean n => (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) =
      Complex.ofRealLI ∘ (g ∘ a) := by
    funext q
    simp [g, a]
  rw [he, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (hg.comp a.contDiff).contDiffAt (by simp), a.iteratedFDeriv_comp_right hg p (by simp)]
  apply ((iteratedFDeriv ℝ j g (a p)).norm_compContinuousLinearMap_le (fun _ => a)).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (a p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ha))
    _ = _ := by dsimp [g]; rw [iteratedFDeriv_comp_add_left]; simp [a]

/-- The Fourier-character profile required by the joint kernel estimate is
produced from its compact carrier, independently of all scale parameters
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_outputJointWave_profile_on_jointCarrier
    {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K) :
    ∃ W : ℕ → ℝ, (∀ j, 0 ≤ W j) ∧ ∀ p ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2)‖ ≤ W j := by
  obtain ⟨W, hW, hb⟩ := exists_outputJointWave_profile
    (hK.image (show Continuous (fun p : JointVariables (Euclidean n) => p.2.2.2)
      from continuous_snd.snd.snd))
  exact ⟨W, hW, fun p hp j => hb j _ ⟨p, hp, rfl⟩⟩

end JanetCartan.FiniteChain.Graph.KernelEstimates
