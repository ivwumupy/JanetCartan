module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic

/-!
# Output support after recovery of the identity

The complementary regularized kernels need not have compact output support.
The support argument for `app:ch_regular:eq:chain-tail` applies to `g - Mout g`
after Fourier reconstruction of the identity. The lemmas here prove precisely
that support statement; they do not assert convergence of the regularizations.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}

/-- A left localizer vanishes outside the output base carrier of its symbol,
for any input (`app:ch_regular:eq:chain-tail`). -/
theorem leftLocalizer_zero_off_output (ρ : ℝ) (mo : LocalizerSymbol n)
    (g : Euclidean n → Fin r → ℂ) (t : Set (Euclidean n))
    (hm : ∀ x ∉ t, ∀ ζ, mo (x, ζ) = 0) (x : Euclidean n) (hx : x ∉ t) :
    leftLocalizer ρ mo g x = 0 := by
  simp [leftLocalizer, graphOperator, hm x hx]

/-- Compact support of the actual left output, supplied entirely by the output
symbol's base support (`app:ch_regular:eq:chain-tail`). -/
theorem leftLocalizer_hasCompactSupport (ρ : ℝ) (mo : LocalizerSymbol n)
    (g : Euclidean n → Fin r → ℂ) (t : Set (Euclidean n)) (ht : IsCompact t)
    (hm : ∀ x ∉ t, ∀ ζ, mo (x, ζ) = 0) :
    HasCompactSupport (leftLocalizer ρ mo g) :=
  HasCompactSupport.intro ht (leftLocalizer_zero_off_output ρ mo g t hm)

/-- The recovered identity-minus-localizer output has compact support in the
union of the datum's support and the output-symbol base. This is the support
statement used after Fourier inversion in `app:ch_regular:eq:chain-tail`;
it makes no compact-support assertion about finite identity regularizations. -/
theorem complementaryOutput_hasCompactSupport (ρ : ℝ) (mo : LocalizerSymbol n)
    (g : Euclidean n → Fin r → ℂ) (hg : HasCompactSupport g)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hm : ∀ x ∉ t, ∀ ζ, mo (x, ζ) = 0) :
    HasCompactSupport (g - leftLocalizer ρ mo g) :=
  hg.sub (leftLocalizer_hasCompactSupport ρ mo g t ht hm)

end JanetCartan.FiniteChain.Graph.KernelLimits
