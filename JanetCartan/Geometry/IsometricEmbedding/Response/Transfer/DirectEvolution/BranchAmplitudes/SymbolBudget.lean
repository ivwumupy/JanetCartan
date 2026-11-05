module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Support

/-!
# Source-symbol budgets for the actual joint-transfer branches

This connects the literal expressions of `new:eq:carrier-ibp` to the full
two-position graph calculus, at the original covector `ξ = λ θ`. Only local
primitive-field jets are required. All expression jets and support conditions
for the modified matrix amplitude are proved. `CoefficientJets` supplies the
phase coefficient budgets; the original annular amplitude jets come from the
sector's `EvolutionIntegral.SymbolBudgets`. Their joint-field instantiation,
the graph realization and Sobolev assembly remain explicit consumer obligations.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open CompactTransfer IsometricEmbedding.Response.NearCarrier
open FourierIntegral FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open SourceExpansion NearCarrierSymbol

variable {n : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]

/-- The fixed coordinate and finite Leibniz constant for a literal branch.
It precedes the coefficient scale, frequency, fields and carrier parameter.
Source: the low-calculus step of `app:ch_response:eq:direct-envelope-profile`. -/
def termLowConstant (t : JointTransferTerm n P M ι)
    (Pj : Option ((Euclidean n × P) × ι) → ℕ → ℝ) (N : ℕ) : ℝ :=
  (max 1 ‖normalizedSliceLinear (n := n) (P := P)‖) ^ N * t.amplitude.lowJetConstant Pj N

omit [FiniteDimensional ℝ P] [Fintype ι] in
/-- Nonnegativity of the actual finite branch constant. -/
theorem termLowConstant_nonneg (t : JointTransferTerm n P M ι)
    (Pj : Option ((Euclidean n × P) × ι) → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j) (N : ℕ) :
    0 ≤ termLowConstant t Pj N :=
  mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    (t.amplitude.lowJetConstant_nonneg Pj hPj N)

/-- Every normalized matrix jet required by the low graph calculus costs
`L^(q-j)` for the ACTUAL branch containing `j` original input derivatives.
The same fixed reserve works at every joint output/parameter order. Bounds
are assumed only for the primitive fields, on the original local box.
Source: `new:eq:carrier-coefficient` and the count after `new:eq:carrier-ibp`. -/
theorem norm_lowJet_normalizedTermAmplitude_le
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {α : (Euclidean n × P) → CarrierVariables n → M}
    {U : Set (Euclidean n × P)} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) (c : P)
    (hs : ∀ p, normalizedSlice c p ∈ tsupport (Function.uncurry α) →
      normalizedSlice c p ∈ U ×ˢ D)
    (Pj : Option ((Euclidean n × P) × ι) → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    (N R : ℕ) (hR : N + 2 < R) {L : ℝ} (hL : 1 ≤ L)
    (hjet : ∀ i j, j ≤ N + (es.length - t.datumWord.length) → ∀ q ∈ U ×ˢ D,
      ‖iteratedFDeriv ℝ j (jointAmplitudeFields b f w₀ α i) q‖ ≤
        Pj i j * L ^ (j + 2 - R))
    {j : ℕ} (hj : j ≤ N) (p : Point n) :
    ‖iteratedFDeriv ℝ j (normalizedTermAmplitude b f w₀ α t c) p‖ ≤
      termLowConstant t Pj N * L ^ (es.length - t.datumWord.length) := by
  have hconst := termLowConstant_nonneg t Pj hPj N
  have hpow : 0 ≤ L ^ (es.length - t.datumWord.length) :=
    pow_nonneg (zero_le_one.trans hL) _
  by_cases hp : p ∈ tsupport (normalizedTermAmplitude b f w₀ α t c)
  · have hpU := hs p (tsupport_normalizedTermAmplitude_subset b f w₀ α es t ht c hp)
    have hfields := contDiffOn_jointAmplitudeFields b hα hA
    have hlocal := contDiffOn_amplitudeExpression (hU.prod hD) _ hfields t.amplitude
    have hcount := jointTransferTerms_order_budget b es t ht
    have hb := norm_lowJet_evaluate_on_open_le (hU.prod hD) _ hfields Pj hPj
      t.amplitude N R (es.length - t.datumWord.length) hR (by omega) hL hpU
      (fun i l hl => hjet i l hl _ hpU) hj
    have hcoord : ‖normalizedSliceLinear (n := n) (P := P)‖ ^ j ≤
        (max 1 ‖normalizedSliceLinear (n := n) (P := P)‖) ^ N :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    apply (norm_iteratedFDeriv_matrixSlice_le (hU.prod hD) hlocal c hpU j).trans
    have h := mul_le_mul hb hcoord (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (t.amplitude.lowJetConstant_nonneg Pj hPj N) hpow)
    convert h using 1
    dsimp only [termLowConstant]
    ring
  · have hz : iteratedFDeriv ℝ j (normalizedTermAmplitude b f w₀ α t c) p = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hp (support_iteratedFDeriv_subset j h)
    rw [hz, norm_zero]
    exact mul_nonneg hconst hpow

variable {r : ℕ}
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The actual restored amplitude of each IBP term satisfies the full source
symbol bound, including the order `p = -1` gain. Both masks and beta/high-pass
remain in `α`; the annular support bound also concerns only `α`. The exponent
is proved from the enumeration, not assumed. No modified-amplitude estimate
or operator estimate is a premise. Source: `app:ch_response:eq:direct-envelope-profile`.
-/
theorem hasFullSourceSymbolBound_jointTransferTerm
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {α : (Euclidean n × P) → CarrierVariables n → Mat}
    {U : Set (Euclidean n × P)} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) (c : P)
    (hs : ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) →
      normalizedSlice c q ∈ U ×ˢ D)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hsfreq : ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius)
    (Pj : Option ((Euclidean n × P) × ι) → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    (N R : ℕ) (hR : N + 2 < R) {L lam : ℝ} (hL : 1 ≤ L) (hlam : 1 ≤ lam)
    (hjet : ∀ i j, j ≤ N + (es.length - t.datumWord.length) → ∀ q ∈ U ×ˢ D,
      ‖iteratedFDeriv ℝ j (jointAmplitudeFields b f w₀ α i) q‖ ≤
        Pj i j * L ^ (j + 2 - R)) (p : ℤ) :
    HasFullSourceSymbolBound
      (ModifiedLow.modifiedAmplitude lam p (normalizedTermAmplitude b f w₀ α t c)) N
      (((1 + radius) ^ N * termLowConstant t Pj N) * lam ^ p *
        L ^ (es.length - t.datumWord.length)) := by
  have hsm := contDiff_normalizedTermAmplitude b hU hD hα hA es t ht c hs
  have hnorm (j : ℕ) (hj : j ≤ N) (q : Point n) :=
    norm_lowJet_normalizedTermAmplitude_le b hU hD hα hA es t ht c hs
      Pj hPj N R hR hL hjet hj q
  have hp : 0 ≤ lam ^ p := (zpow_pos (zero_lt_one.trans_le hlam) p).le
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have hsupport : ∀ q ∈ tsupport ((lam ^ p) • normalizedTermAmplitude b f w₀ α t c),
      ‖q.2‖ ≤ radius := by
    intro q hq
    exact hsfreq q (tsupport_normalizedTermAmplitude_subset b f w₀ α es t ht c
      (tsupport_smul_subset_right (fun _ => lam ^ p) _ hq))
  have hsymbol := hasFullSourceSymbolBound_of_normalized_jets
    (ModifiedLow.contDiff_modifiedAmplitude lam p hsm) hlam hradius
    (mul_nonneg hp (mul_nonneg (termLowConstant_nonneg t Pj hPj N)
      (pow_nonneg (zero_le_one.trans hL) _))) N
    (support_physicalAmplitudeOfNormalized hlampos hsupport)
    (fun j hj q => by
      rw [ModifiedLow.normalizedField_modifiedAmplitude hlampos.ne' p,
        iteratedFDeriv_const_smul_apply (hsm.of_le (by simp)).contDiffAt,
        norm_smul, Real.norm_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (hnorm j hj q) hp)
  convert hsymbol using 1
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
