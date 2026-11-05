module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks

/-!
# Primitive joint elapsed-amplitude grades

The derivative variables include elapsed time, both physical bases and all
three covectors. The consumer is `norm_integral_regularizedElapsedKernel_le`,
the compact-frequency kernel step of `app:ch_regular:eq:chain-tail`.
The actual symbol, physical masks, multiplier, proof masks and frequency
cutoffs are multiplied by the existing Leibniz estimates. Every fixed grade
offset is added once, independently of accuracy. Adjoint grades follow by
literal conjugate transpose of the full masked symbol.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Primitive two-time symbol evaluated at the actual elapsed coordinates
and physical covector. The normalized variable is not substituted for the
physical frequency (`app:ch_regular:eq:high-amplitude`). -/
def normalizedElapsedSymbol (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (p : ℝ × JointVariables (Euclidean (d + 1))) : Matrix (Fin q) (Fin q) ℂ :=
  b (p.2.1.1 0) (p.2.1.1 0 - p.1) (spatialPart p.2.1.1)
    (spatialPart (ρ • p.2.2.1))

/-- Multiplying the actual two-time symbol by the two physical masks and
the Fourier multiplier gives joint elapsed grades with one fixed total
offset. Both orientations have the same bound, by literal adjunction
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_orientedElapsedAmplitude_le
    (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (ht : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦ χout p.2.1.1))
    (hs : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦ χsource p.2.1.2))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦ β (ρ • p.2.2.1)))
    (hb : ContDiff ℝ ∞ (normalizedElapsedSymbol ρ b))
    {T U G B : ℕ → ℝ} (hT : ∀ j, 0 ≤ T j) (hU : ∀ j, 0 ≤ U j) (hG : ∀ j, 0 ≤ G j)
    {S L : ℝ} (hL : 0 ≤ L) (bt bs bg bb : ℕ)
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hbt : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      χout w.2.1.1) p‖ ≤ T j * L ^ (j + bt))
    (hbs : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      χsource w.2.1.2) p‖ ≤ U j * L ^ (j + bs))
    (hbg : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      β (ρ • w.2.2.1)) p‖ ≤ G j * L ^ (j + bg))
    (hbb : ∀ j, ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ b) p‖ ≤
      S * B j * L ^ (j + bb)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      orientedElapsedAmplitude backward b χout χsource β w.1 w.2.1.1 w.2.1.2
        (ρ • w.2.2.1)) p‖ ≤
      S * derivativeConvolution T (derivativeConvolution U (derivativeConvolution G B)) k *
        L ^ (k + (bt + (bs + (bg + bb)))) := by
  have hgb j := norm_iteratedFDeriv_smul_le_amplitude_grades hg hb hG hL bg bb p hbg hbb j
  have hsgb j := norm_iteratedFDeriv_smul_le_amplitude_grades hs (hg.smul hb)
    hU hL bs (bg + bb) p hbs hgb j
  have hall := norm_iteratedFDeriv_smul_le_amplitude_grades ht (hs.smul (hg.smul hb))
    hT hL bt (bs + (bg + bb)) p hbt hsgb k
  have hf : (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      χout w.2.1.1 • (χsource w.2.1.2 • (β (ρ • w.2.2.1) • normalizedElapsedSymbol ρ b w))) =
      (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
        elapsedAmplitude b χout χsource β w.1 w.2.1.1 w.2.1.2 (ρ • w.2.2.1)) := by
    funext w
    simp only [elapsedAmplitude, normalizedElapsedSymbol, smul_smul, mul_assoc]
  change ‖iteratedFDeriv ℝ k (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
    χout w.2.1.1 • (χsource w.2.1.2 • (β (ρ • w.2.2.1) • normalizedElapsedSymbol ρ b w))) p‖ ≤ _ at hall
  rw [hf] at hall
  cases backward
  · exact hall
  · simpa only [orientedElapsedAmplitude, ↓reduceIte,
      norm_iteratedFDeriv_transport_conjTranspose] using hall

private theorem norm_localized_product_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (D : AmplitudeProfiles) {g o i m : V → ℂ} {a : V → F}
    (hg : ContDiff ℝ ∞ g) (ho : ContDiff ℝ ∞ o) (hi : ContDiff ℝ ∞ i)
    (hm : ContDiff ℝ ∞ m) (ha : ContDiff ℝ ∞ a)
    {S L : ℝ} (hL : 1 ≤ L) (p : V)
    (hbg : ∀ j, ‖iteratedFDeriv ℝ j g p‖ ≤ D.graphCutoff j * L ^ (j + D.graphCutoffOffset))
    (hbo : ∀ j, ‖iteratedFDeriv ℝ j o p‖ ≤ D.outputCutoff j * L ^ (j + D.outputCutoffOffset))
    (hbi : ∀ j, ‖iteratedFDeriv ℝ j i p‖ ≤ D.inputMask j * L ^ (j + D.inputMaskOffset))
    (hbm : ∀ j, ‖iteratedFDeriv ℝ j m p‖ ≤ D.outputMask j * L ^ (j + D.outputMaskOffset))
    (hba : ∀ j, ‖iteratedFDeriv ℝ j a p‖ ≤ S * D.symbol j * L ^ (j + D.symbolOffset)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w ↦ (g w * o w * (1 - m w) * i w) • a w) p‖ ≤
      S * D.productProfile k * L ^ (k + D.offset) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hco j : 0 ≤ 1 + D.outputMask j := by linarith [D.outputMask_nonneg j]
  have hcomp j := norm_iteratedFDeriv_one_sub_le_grades hm
    (S := 1) le_rfl hL D.outputMaskOffset p (fun k ↦ by simpa using hbm k) j
  have hgo j := norm_iteratedFDeriv_mul_le_grades hg ho
    D.graphCutoff_nonneg D.outputCutoff_nonneg (S := 1) (T := 1)
    zero_le_one zero_le_one hL0 D.graphCutoffOffset D.outputCutoffOffset p
    (fun k ↦ by simpa using hbg k) (fun k ↦ by simpa using hbo k) j
  have hgo' := derivativeConvolution_nonneg D.graphCutoff_nonneg D.outputCutoff_nonneg
  have hgom j := norm_iteratedFDeriv_mul_le_grades (hg.mul ho) (contDiff_const.sub hm)
    hgo' hco (S := 1) (T := 1) zero_le_one zero_le_one hL0
    (D.graphCutoffOffset + D.outputCutoffOffset) D.outputMaskOffset p
    (fun k ↦ by simpa using hgo k) hcomp j
  have hgom' := derivativeConvolution_nonneg hgo' hco
  have hmask j := norm_iteratedFDeriv_mul_le_grades
    ((hg.mul ho).mul (contDiff_const.sub hm)) hi hgom' D.inputMask_nonneg
    (S := 1) (T := 1) zero_le_one zero_le_one hL0
    ((D.graphCutoffOffset + D.outputCutoffOffset) + D.outputMaskOffset) D.inputMaskOffset p
    (fun k ↦ by simpa using hgom k) (fun k ↦ by simpa using hbi k) j
  exact norm_iteratedFDeriv_smul_le_amplitude_grades
    (((hg.mul ho).mul (contDiff_const.sub hm)).mul hi) ha
    (derivativeConvolution_nonneg hgom' D.inputMask_nonneg) hL0
    (((D.graphCutoffOffset + D.outputCutoffOffset) + D.outputMaskOffset) + D.inputMaskOffset)
    D.symbolOffset p (fun j ↦ by simpa using hmask j) hba k

/-- All proof-localizer and frequency-cutoff factors are included in the
joint elapsed grade. The input symbol is the full masked symbol bounded by
`norm_iteratedFDeriv_orientedElapsedAmplitude_le`; it is never replaced by a
successful integrated estimate (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_jointElapsedAmplitude_le
    (D : AmplitudeProfiles) (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (hg : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (χA (ρ • w.2.2.1) : ℂ)))
    (ho : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (χo (ρ • w.2.2.2.2) : ℂ)))
    (hi : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (mi (y, w.2.2.2.1) : ℂ)))
    (hm : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (mo (x, w.2.2.2.2) : ℂ)))
    (ha : ContDiff ℝ ∞ (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      orientedElapsedAmplitude backward b χout χsource β w.1 w.2.1.1 w.2.1.2 (ρ • w.2.2.1)))
    {S L : ℝ} (hL : 1 ≤ L) (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hbg : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (χA (ρ • w.2.2.1) : ℂ)) p‖ ≤ D.graphCutoff j * L ^ (j + D.graphCutoffOffset))
    (hbo : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (χo (ρ • w.2.2.2.2) : ℂ)) p‖ ≤ D.outputCutoff j * L ^ (j + D.outputCutoffOffset))
    (hbi : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (mi (y, w.2.2.2.1) : ℂ)) p‖ ≤ D.inputMask j * L ^ (j + D.inputMaskOffset))
    (hbm : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      (mo (x, w.2.2.2.2) : ℂ)) p‖ ≤ D.outputMask j * L ^ (j + D.outputMaskOffset))
    (hba : ∀ j, ‖iteratedFDeriv ℝ j (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      orientedElapsedAmplitude backward b χout χsource β w.1 w.2.1.1 w.2.1.2 (ρ • w.2.2.1)) p‖ ≤
        S * D.symbol j * L ^ (j + D.symbolOffset)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y) p‖ ≤
      S * D.productProfile k * L ^ (k + D.offset) := by
  unfold jointElapsedAmplitude jointAmplitude
  simpa only [Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one] using
    norm_localized_product_le D hg ho hi hm ha hL p hbg hbo hbi hbm hba k

/-- Joint elapsed smoothness is derived from the original normalized symbol
and the actual masks/cutoffs. Literal conjugate transpose preserves this
smoothness and never exchanges the two amplitude positions
(`app:ch_regular:eq:high-amplitude`). -/
theorem contDiff_jointElapsedAmplitude
    (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (hb : ContDiff ℝ ∞ (normalizedElapsedSymbol ρ b))
    (hout : ContDiff ℝ ∞ χout) (hsource : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo) :
    ContDiff ℝ ∞ (jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y) := by
  change Euclidean (d + 1) × Euclidean (d + 1) → ℝ at mi mo
  have ht : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      χout p.2.1.1 * χsource p.2.1.2 * β (ρ • p.2.2.1)) := by fun_prop
  have hfull : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      elapsedAmplitude b χout χsource β p.1 p.2.1.1 p.2.1.2 (ρ • p.2.2.1)) :=
    ht.smul hb
  have hA : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 (ρ • p.2.2.1)) := by
    cases backward
    · exact hfull
    · let L : Matrix (Fin q) (Fin q) ℂ ≃ₗᵢ[ℝ] Matrix (Fin q) (Fin q) ℂ :=
        { Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ with
          norm_map' := Matrix.frobenius_norm_conjTranspose }
      exact L.contDiff.comp hfull
  have hm : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      χA (ρ • p.2.2.1) * χo (ρ • p.2.2.2.2) *
        (1 - mo (x, p.2.2.2.2)) * mi (y, p.2.2.2.1)) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hm).smul hA

/-- The fixed extension cutoff adds no derivative-scale offset. Its profile
is convolved once with the already derived joint amplitude profile. This
discharges the extended-amplitude grade needed in
`norm_integral_regularizedElapsedKernel_le`
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_cut_jointElapsedAmplitude_le
    (backward : Bool) (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ)
    (ha : ContDiff ℝ ∞ (jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y))
    {Z A : ℕ → ℝ} (hZ : ∀ j, 0 ≤ Z j) {S L : ℝ} (hL : 1 ≤ L) (b₀ : ℕ)
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hz : ∀ j, ‖iteratedFDeriv ℝ j θ p.1‖ ≤ Z j)
    (hab : ∀ j, ‖iteratedFDeriv ℝ j
      (jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y) p‖ ≤
        S * A j * L ^ (j + b₀)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ w.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y w) p‖ ≤
        S * derivativeConvolution Z A k * L ^ (k + b₀) := by
  have hc (j : ℕ) : ‖iteratedFDeriv ℝ j
      (fun w : ℝ × JointVariables (Euclidean (d + 1)) ↦ θ w.1) p‖ ≤ Z j * L ^ (j + 0) := by
    let π : (ℝ × JointVariables (Euclidean (d + 1))) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ _ _
    have hb' : ‖iteratedFDeriv ℝ j θ (π p)‖ ≤ 1 * Z j * L ^ (j + 0) := by
      simpa only [π, ContinuousLinearMap.coe_fst', one_mul, Nat.add_zero] using
        (hz j).trans (le_mul_of_one_le_right (hZ j) (one_le_pow₀ hL))
    have hh := norm_iteratedFDeriv_comp_linear_le_grades hθ π zero_le_one
      (ContinuousLinearMap.norm_fst_le ℝ _ _) hZ zero_le_one (zero_le_one.trans hL) 0 p j hb'
    simpa only [π, Function.comp_def, ContinuousLinearMap.coe_fst', one_pow, mul_one,
      one_mul] using hh
  simpa only [zero_add, Function.comp_def] using norm_iteratedFDeriv_smul_le_amplitude_grades
    (hθ.comp contDiff_fst) ha hZ (zero_le_one.trans hL) 0 b₀ p hc hab k

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
