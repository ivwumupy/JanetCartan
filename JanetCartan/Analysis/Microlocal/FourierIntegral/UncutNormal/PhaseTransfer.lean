module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.NormalGeometry

/-!
# The full cross symbol is unchanged by the supported phase extension

The common auxiliary phase used to realize both graphs leaves the exact
zero-extended symbol unchanged, including both physical positions and the
physical-to-cycle conversion. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open LowBounds NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Phase extension on the supported convex chart preserves the literal cycle
cross symbol. Invertibility is not required outside that chart. Consumer: the
simultaneous uncut graph construction, for
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cycleCrossNormalSymbol_phase_congr
    {X D : Set E} {S S' : E → E → ℝ} (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (hX : IsOpen X) (hcX : Convex ℝ X)
    (he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D))
    (hA : ∀ x u, x ∉ X → A x u = 0) (hB : ∀ x u, x ∉ X → B x u = 0) :
    cycleCrossNormalSymbol D S' A B η J = cycleCrossNormalSymbol D S A B η J := by
  funext ξ z
  rw [cycleCrossNormalSymbol_eq_pairedBuffered X D S' A B η J hA hB,
    cycleCrossNormalSymbol_eq_pairedBuffered X D S A B η J hA hB,
    bufferedNormalDomain_phase_congr hX hcX he]

end JanetCartan.FourierIntegral.UncutNormal
