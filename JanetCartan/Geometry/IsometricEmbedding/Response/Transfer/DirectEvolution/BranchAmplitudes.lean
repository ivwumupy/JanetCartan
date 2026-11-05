module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.PrimitiveFields
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.SymbolBudget
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Kernel

/-!
# Actual carrier branch symbols from primitive phase and amplitude jets

The local joint IBP expressions are converted to the normalized two-position
matrix amplitudes consumed by the SAME original full graph calculus.
The coefficient producer, local-to-global smoothness, full support and
fixed low-reserve estimate are instantiated. Only primitive phase/amplitude
jets, critical matching, the averaged-Hessian inverse gap and original support
geometry remain inputs. This is the symbol step of
`app:ch_response:eq:direct-envelope-profile`, not its Sobolev conclusion.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open CompactTransfer FourierIntegral SourceExpansion

variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Primitive phase and original-amplitude jets produce the source-symbol
bound of every actual ordered transfer branch. The constant is chosen before
the reserve, scales, order `p`, phase, critical map, amplitude and parameter.
For a branch with `j` original input derivatives and total order `q`, it costs
exactly `C * λ^p * L^(q-j)`. No transferred-amplitude estimate is assumed.

The same result applies to the forward and literal reversed carrier phase;
the original graph geometry and strong/Sobolev assembly are separate steps.
Source: `new:eq:carrier-coefficient`, `app:ch_response:eq:direct-envelope-profile`.
-/
theorem exists_jointTransferTerm_symbol_constant
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P Mat ι)
    (ht : t ∈ jointTransferTerms b es) (N : ℕ)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (R : ℕ), N + 2 < R → ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam →
      ∀ (p : ℤ) (f : (Euclidean n × P) → CarrierVariables n → ℝ)
        (w₀ : (Euclidean n × P) → CarrierVariables n)
        (α : (Euclidean n × P) → CarrierVariables n → Mat)
        (U : Set (Euclidean n × P)) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → Convex ℝ D →
      ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U D →
      (∀ q ∈ U, gradient (f q) (w₀ q) = 0) →
      (∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) →
      (∀ q ∈ U, ∀ w ∈ D, ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B) →
      (∀ j ≤ N + (es.length - t.datumWord.length) + 2, ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L ^ (j - R)) →
      ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D) →
      (∀ j ≤ N + (es.length - t.datumWord.length), ∀ q ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - R)) →
      ∀ c : P,
      (∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) →
        normalizedSlice c q ∈ U ×ˢ D) →
      (∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
      ContDiff ℝ ∞ (normalizedTermAmplitude b f w₀ α t c) ∧
        HasFullSourceSymbolBound
          (ModifiedLow.modifiedAmplitude lam p (normalizedTermAmplitude b f w₀ α t c)) N
          (C * lam ^ p * L ^ (es.length - t.datumWord.length)) := by
  obtain ⟨Pj, hPj, hfields⟩ := exists_jointAmplitudeFields_jet_profile
    (n := n) (E := Euclidean n × P) (M := Mat) (ι := ι) Aphase Aamp hphase hamp hB
  refine ⟨(1 + radius) ^ N * termLowConstant t Pj N,
    mul_nonneg (pow_nonneg (by linarith) _) (termLowConstant_nonneg t Pj hPj N), ?_⟩
  intro R hR L lam hL hlam p f w₀ α U D hU hD hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet c hs hsfreq
  have hA := contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hu
  refine ⟨contDiff_normalizedTermAmplitude b hU hD hα hA es t ht c hs, ?_⟩
  exact hasFullSourceSymbolBound_jointTransferTerm b hU hD hα hA es t ht c hs hradius hsfreq
    Pj hPj N R hR hL hlam
    (hfields R (by omega) L hL (N + (es.length - t.datumWord.length)) b f w₀ α U D
      hU hD hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet) p

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
