module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.KernelJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Cutoff

/-!
# A smaller selector for the actual complementary parameter jets

The auxiliary cutoff in `app:ch_response:thm:response-literal-transfer` is
constructed from the original plateau radius. It is used solely to express
an already differentiated amplitude in `complementaryAmplitude` form for the
published graph-decay theorems. The resulting amplitude is exactly unchanged.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral

/-- Smooth normalized selector supported strictly inside the original plateau,
equal to one through one quarter of its radius.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def auxiliaryComplementSelector (n : ℕ) (g : ℝ) (hg : 0 < g) : Euclidean n → ℂ :=
  fun δ ↦ (internalEnvelopeCutoff n (g / 4) (by positivity)).symbol δ

/-- The smaller selector is genuinely smooth
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_auxiliaryComplementSelector (n : ℕ) (g : ℝ) (hg : 0 < g) :
    ContDiff ℝ ∞ (auxiliaryComplementSelector n g hg) :=
  Complex.ofRealCLM.contDiff.comp (internalEnvelopeCutoff n (g / 4) (by positivity)).smooth

/-- The smaller selector has a frequency-independent plateau
(`app:ch_response:thm:response-literal-transfer`). -/
theorem auxiliaryComplementSelector_eq_one (n : ℕ) (g : ℝ) (hg : 0 < g)
    (δ : Euclidean n) (hδ : ‖δ‖ ≤ g / 4) :
    auxiliaryComplementSelector n g hg δ = 1 := by
  simp only [auxiliaryComplementSelector,
    (internalEnvelopeCutoff n (g / 4) (by positivity)).one_on_ball δ hδ, Complex.ofReal_one]

/-- The support of the smaller selector lies in the original open plateau.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_lt_of_auxiliaryComplementSelector_ne_zero (n : ℕ) (g : ℝ) (hg : 0 < g)
    (δ : Euclidean n) (hδ : auxiliaryComplementSelector n g hg δ ≠ 0) : ‖δ‖ < g := by
  have hhalf : ‖δ‖ < g / 2 := by
    by_contra hn
    apply hδ
    have hzero := (internalEnvelopeCutoff n (g / 4) (by positivity)).zero_outside δ
      (show 2 * (g / 4) ≤ ‖δ‖ by linarith [le_of_not_gt hn])
    simp only [auxiliaryComplementSelector, hzero, Complex.ofReal_zero]
  linarith

/-- The auxiliary selector has the physical-frequency plateau required by
the graph estimates. Its construction introduces no unit-frequency `2π` change.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem auxiliaryComplementSelector_physical_plateau (n : ℕ) (g : ℝ) (hg : 0 < g)
    {ρ : ℝ} (hρ : 0 < ρ) (δ : Euclidean n) (hδ : ‖δ‖ < (g / 4) * ρ) :
    auxiliaryComplementSelector n g hg (ρ⁻¹ • δ) = 1 := by
  apply auxiliaryComplementSelector_eq_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact ((inv_mul_lt_iff₀ hρ).2 (by linarith)).le

/-- Every actual carrier/selector jet is exactly a complete complementary
amplitude for the constructed smaller selector. This discharges the support
adapter needed to apply the published forward and reverse graph estimates.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryAmplitude_auxiliaryComplementSelector_jet
    {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : FullAmplitude n r) (q : Euclidean n → ℂ) (ζ : P → Euclidean n)
    (ψ : P → Euclidean n → Euclidean n → ℝ) (ρ : ℝ)
    {g : ℝ} (hg : 0 < g) (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) :
    complementaryAmplitude (complementaryCarrierJet A q ζ ψ ρ k v c)
        (ζ c) ρ (fun δ ↦ auxiliaryComplementSelector n g hg (ρ⁻¹ • δ)) =
      complementaryCarrierJet A q ζ ψ ρ k v c :=
  complementaryAmplitude_complementaryCarrierJet A q _ ζ ψ ρ hq
    (norm_lt_of_auxiliaryComplementSelector_ne_zero n g hg) hζ k v

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
