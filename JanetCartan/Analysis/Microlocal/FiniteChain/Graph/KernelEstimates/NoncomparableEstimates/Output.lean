module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Base

/-!
# Output derivatives with unequal graph frequencies

Only output-base derivatives of the mask enter `app:ch_regular:eq:chain-tail`.
Their normalization uses the larger physical radius `R`, while the mask's
covector argument and the input mask remain normalized by `ρ`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open FourierIntegral Retarded.KernelDecay
variable {n : ℕ}

/-- The fixed wave profile on a compact set of larger-radius normalized
output covectors (`app:ch_regular:eq:chain-tail`). -/
theorem exists_baseWave_profile {K : Set (Euclidean n)} (hK : IsCompact K) :
    ∃ W : ℕ → ℝ, (∀ j, 0 ≤ W j) ∧ ∀ j ξ, ξ ∈ K →
      ‖iteratedFDeriv ℝ j (fun t => outputJointWave (t, ξ)) 0‖ ≤ W j := by
  have hc j : Continuous (fun ξ : Euclidean n =>
      iteratedFDeriv ℝ j (fun t => outputJointWave (t, ξ)) 0) :=
    ((contDiff_outputJet (contDiff_outputJointWave (n := n)) j).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hb j := hK.exists_bound_of_continuousOn (hc j).continuousOn
  choose C hC using hb
  exact ⟨fun j => max 0 (C j), fun j => le_max_left _ _,
    fun j ξ hξ => (hC j ξ hξ).trans (le_max_right _ _)⟩

/-- Rescaling only the output base is a contraction when `R ≥ 1`. In particular
there is no derivative of the frequency argument (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_rescaled_baseMask_le {mo : LocalizerSymbol n}
    (ho : ContDiff ℝ ∞ mo) {R : ℝ} (hR : 1 ≤ R) (x ξ : Euclidean n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun t => (mo (x + R⁻¹ • t, ξ) : ℂ)) 0‖ ≤
      ‖iteratedFDeriv ℝ k (fun t => mo (t, ξ)) x‖ := by
  let g : Euclidean n → ℂ := fun t => (mo (x + t, ξ) : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp
    (ho.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const))
  change ‖iteratedFDeriv ℝ k (fun t => g (R⁻¹ • t)) 0‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (hg.of_le (by simp))]
  dsimp only
  rw [smul_zero, norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity) _)]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR))).trans_eq
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘ (fun t => mo (x + t, ξ))) 0‖ = _
  have hs : ContDiff ℝ ∞ (fun t => mo (x + t, ξ)) :=
    ho.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const)
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp)]
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun t => mo (t, ξ)) k x (0 : Euclidean n)
  rw [add_zero] at ht
  rw [ht]

/-- The actual scalar output jet costs `R^m`, with a fixed `m+bo` grade loss.
The Fourier character is evaluated at `ρ/R` times the input-normalized output
covector. Thus its compact profile is uniform on larger-frequency shells
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_physical_outputJet_le (ρ : ℝ) {R L So : ℝ}
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hSo : 1 ≤ So)
    {mo : LocalizerSymbol n} (ho : ContDiff ℝ ∞ mo) (x ξ : Euclidean n)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bo m : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hw : ∀ j, ‖iteratedFDeriv ℝ j
      (fun t => outputJointWave (t, (ρ / R) • ξ)) 0‖ ≤ W j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j (fun t => mo (t, ξ)) x‖ ≤ So * O j * L ^ (j + bo)) :
    ‖iteratedFDeriv ℝ m (fun t =>
      Complex.exp ((inner ℝ t (ρ • ξ) : ℂ) * Complex.I) *
        (1 - (mo (x + t, ξ) : ℂ))) 0 v‖ ≤
      R ^ m * So * derivativeConvolution W (fun j => 1 + O j) m * L ^ (m + bo) := by
  let w : Euclidean n → ℂ := fun t => outputJointWave (t, (ρ / R) • ξ)
  let o : Euclidean n → ℂ := fun t => (mo (x + R⁻¹ • t, ξ) : ℂ)
  let g : Euclidean n → ℂ := fun t => w t * (1 - o t)
  have hsw : ContDiff ℝ ∞ w := contDiff_outputJointWave.comp (contDiff_id.prodMk contDiff_const)
  have hso : ContDiff ℝ ∞ o := Complex.ofRealCLM.contDiff.comp
    (ho.comp ((contDiff_const.add (contDiff_id.const_smul R⁻¹)).prodMk contDiff_const))
  have hsg : ContDiff ℝ ∞ g := hsw.mul (contDiff_const.sub hso)
  have hw' j : ‖iteratedFDeriv ℝ j w 0‖ ≤ 1 * W j * L ^ (j + 0) := by
    simpa using (hw j).trans (le_mul_of_one_le_right (hW j) (one_le_pow₀ hL))
  have ho' j := (norm_rescaled_baseMask_le ho hR x ξ j).trans (hb j)
  have hc j := norm_iteratedFDeriv_one_sub_le_grades hso hSo hL bo 0 ho' j
  have hp := norm_iteratedFDeriv_mul_le_grades hsw (contDiff_const.sub hso)
    hW (fun j => by linarith [hO j]) zero_le_one (zero_le_one.trans hSo)
    (zero_le_one.trans hL) 0 bo 0 hw' hc m
  have hn : ‖iteratedFDeriv ℝ m g 0 v‖ ≤
      So * derivativeConvolution W (fun j => 1 + O j) m * L ^ (m + bo) := by
    apply ((iteratedFDeriv ℝ m g 0).le_opNorm v).trans
    apply (mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i))).trans
    simpa [g] using hp
  have hR0 : R ≠ 0 := (zero_lt_one.trans_le hR).ne'
  have he : (fun t => Complex.exp ((inner ℝ t (ρ • ξ) : ℂ) * Complex.I) *
      (1 - (mo (x + t, ξ) : ℂ))) = fun t => g (R • t) := by
    funext t
    dsimp [g, w, o, outputJointWave]
    rw [inv_smul_smul₀ hR0]
    congr 3
    simp only [inner_smul_right, real_inner_smul_left]
    field_simp
  rw [he, iteratedFDeriv_comp_const_smul R (hsg.of_le (by simp))]
  simp only [smul_zero, smul_apply, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hR) m)]
  exact (mul_le_mul_of_nonneg_left hn (pow_nonneg (zero_le_one.trans hR) m)).trans_eq (by ring)

/-- Product of primitive regularizer values, the input mask value, and the
proved output-base jet bound. No frequency derivative occurs, including at
source shoulders or bounded smaller frequencies (`app:ch_regular:eq:chain-tail`). -/
theorem norm_outputFrequencyFactor_le (ρ : ℝ) {R L So I Ca Co : ℝ}
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hSo : 1 ≤ So)
    (_hI : 0 ≤ I) (hCa : 0 ≤ Ca) (hCo : 0 ≤ Co)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (ho : ContDiff ℝ ∞ mo) {W O : ℕ → ℝ}
    (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    (bi ba bc bo m : ℕ) (v : Fin m → Euclidean n) (hv : ∀ i, ‖v i‖ ≤ 1)
    (w : Euclidean n × Euclidean n × Euclidean n)
    (hi : ‖mi (y, w.2.1)‖ ≤ I * L ^ bi)
    (ha : ‖χA (ρ • w.1)‖ ≤ Ca * L ^ ba)
    (hc : ‖χo (ρ • w.2.2)‖ ≤ Co * L ^ bc)
    (hw : ∀ j, ‖iteratedFDeriv ℝ j
      (fun t => outputJointWave (t, (ρ / R) • w.2.2)) 0‖ ≤ W j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j (fun t => mo (t, w.2.2)) x‖ ≤ So * O j * L ^ (j + bo)) :
    ‖outputFrequencyFactor ρ mi mo χA χo x y m v w‖ ≤
      (Ca * Co * I * derivativeConvolution W (fun j => 1 + O j) m) *
        (R ^ m * So) * L ^ (ba + bc + bi + (m + bo)) := by
  have hj := norm_physical_outputJet_le ρ hR hL hSo ho x w.2.2 hW hO bo m v hv hw hb
  have hL0 := zero_le_one.trans hL
  unfold outputFrequencyFactor
  simp only [norm_mul, Complex.norm_real]
  have hac := mul_le_mul ha hc (norm_nonneg _) (mul_nonneg hCa (pow_nonneg hL0 _))
  have hai := mul_le_mul hac hi (norm_nonneg _)
    (mul_nonneg (mul_nonneg hCa (pow_nonneg hL0 _)) (mul_nonneg hCo (pow_nonneg hL0 _)))
  apply (mul_le_mul hj hai (by positivity) (by
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (zero_le_one.trans hSo))
      (derivativeConvolution_nonneg hW (fun j => by linarith [hO j]) _)) (pow_nonneg hL0 _))).trans_eq
  simp only [pow_add]
  ring

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
