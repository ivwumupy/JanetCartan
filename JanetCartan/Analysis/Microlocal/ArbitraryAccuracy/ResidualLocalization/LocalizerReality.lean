module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Realization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints
/-!
# Real bounded proof localizers

Even real proof symbols commute with physical complex conjugation in their
original left and right quantizations, including the physical Fourier
normalization. These identities let the complete-residual estimates pass to
`S + conjugate(S)` without changing masks (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral FiniteChain.Graph RegularSector.Realization
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
set_option maxHeartbeats 800000
private theorem scalarGraph_star (a : E → E → E → ℝ)
    (ha : ∀ x y η, a x y (-η) = a x y η) (f : E → Fin r → ℂ) (x : E) :
    graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ (a x y ξ : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) (fun y ↦ star (f y)) x =
    star (graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ (a x y ξ : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) f x) := by
  have hosc (η y : E) : graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) x y (-η) =
      star (graphOscillation (fun x ξ : E ↦ inner ℝ x ξ) x y η) := by
    simp only [graphOscillation, inner_neg_right, Complex.star_def, ← Complex.exp_conj,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  have hint (f : E → Fin r → ℂ) : (∫ x, star (f x)) = star (∫ x, f x) :=
    (starL' ℝ : (Fin r → ℂ) ≃L[ℝ] (Fin r → ℂ)).integral_comp_comm f
  simp only [graphOperator, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [star_smul]
  have hn : star (((2 * Real.pi) ^ n : ℂ)⁻¹) = ((2 * Real.pi) ^ n : ℂ)⁻¹ := by simp
  rw [hn, ← hint, ← integral_neg_eq_self]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [← hint]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [hosc, ha, star_smul, Complex.star_def, Complex.conj_ofReal]

private theorem scalarGraph_eq_of_ae_input (a : E → E → E → ℝ)
    {f g : E → Fin r → ℂ} (hfg : f =ᵐ[volume] g) (x : E) :
    graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ (a x y ξ : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) f x =
    graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ (a x y ξ : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) g x := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Frequency reflection proves reality of the original right quantization,
with its source base intact (`app:ch_regular:lem:finite-chain`). -/
theorem rightLocalizer_star_of_even (ρ : ℝ) (mi : LocalizerSymbol n)
    (heven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ)) (f : E → Fin r → ℂ) (x : E) :
    rightLocalizer ρ mi (fun y ↦ star (f y)) x = star (rightLocalizer ρ mi f x) := by
  exact scalarGraph_star (fun _ y ξ ↦ mi (y, ρ⁻¹ • ξ))
    (fun _ y ξ ↦ by simpa only [smul_neg] using heven y (ρ⁻¹ • ξ)) f x

/-- The same bounded right localizer commutes with conjugation on all data.
The only premise identifying it is its actual physical representative, as
produced by the localization theorems (`app:ch_regular:eq:chain-tail`). -/
theorem boundedRightLocalizer_star_of_even (ρ : ℝ) (mi : LocalizerSymbol n)
    (heven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ)) (Mi : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) (u : H) :
    Mi (star u) = star (Mi u) := by
  have he : (fun y ↦ ((star u) y).ofLp) =ᵐ[volume] (fun y ↦ star ((u y).ofLp)) := by
    filter_upwards [Lp.coeFn_star u] with y hy
    exact congrArg WithLp.ofLp hy
  have hc x := scalarGraph_eq_of_ae_input (fun _ y ξ ↦ mi (y, ρ⁻¹ • ξ)) he x
  apply Lp.ext
  filter_upwards [hMi (star u), hMi u, Lp.coeFn_star (Mi u)] with x hx hy hz
  rw [hx, hz, Pi.star_apply, hy]
  change WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ ((star u) y).ofLp) x) = _
  rw [show rightLocalizer ρ mi (fun y ↦ ((star u) y).ofLp) x =
    rightLocalizer ρ mi (fun y ↦ star ((u y).ofLp)) x from hc x,
    rightLocalizer_star_of_even ρ mi heven]
  rfl

/-- The literal left realization is real as well. Its bounded adjoint is
identified with the right quantization; adjunction commutes with whole-factor
conjugation. This retains the actual output mask and its position, rather
than assuming a commutation with a residual (`app:ch_regular:eq:chain-tail`). -/
theorem boundedLeftLocalizer_star_of_even {d : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (mo : LocalizerSymbol (d + 1)) (hmo : Continuous mo) (hcompact : HasCompactSupport mo)
    (heven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
    (Mo : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean (d + 1))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean (d + 1))))
    (hMo : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) (u) :
    Mo (star u) = star (Mo u) := by
  have hr := IdentityDefect.rightLocalizer_adjoint_ae_of_leftLocalizer hρ mo hmo hcompact Mo hMo
  have hstar := boundedRightLocalizer_star_of_even ρ mo heven Mo.adjoint hr
  have he : boundedConjugate Mo.adjoint = Mo.adjoint := by
    ext1 v
    change star (Mo.adjoint (star v)) = Mo.adjoint v
    rw [hstar, star_star]
  have h := congrArg (fun T ↦ T.adjoint) he
  rw [boundedConjugate_adjoint, ContinuousLinearMap.adjoint_adjoint] at h
  have hv := congrArg (fun T ↦ T (star u)) h
  change star (Mo (star (star u))) = Mo (star u) at hv
  simpa only [star_star] using hv.symm

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
