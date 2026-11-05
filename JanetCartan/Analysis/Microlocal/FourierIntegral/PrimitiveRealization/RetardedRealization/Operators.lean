module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.RetardedRealization.LowBounds

/-!
# Bounded characteristic integration on graph L²

The operator extends the already published literal graph-test map. Its bound
is derived from the fixed cutoffs and time strip, not assumed.
Source: `app:ch_regular_base:eq:characteristic-integral`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FourierIntegral.RetardedRealization

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The quantitative low bound for the existing graph-test map, with the
literal factor `i`. Consumer: `graphRetardedOperator_graphTestToLp`;
source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem graphRetardedTest_norm_le (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hK : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b})
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hbi : ∀ x, |χin x| ≤ Cin) (hbo : ∀ x, |χout x| ≤ Cout)
    (u : graphTestSpace (d + 1) r) :
    ‖graphTestToLp (graphRetardedTest t a χin χout hin hout hK u)‖ ≤
      (Cout * Cin * (b - a)) * ‖graphTestToLp u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert graphRetardedTest_energy_le t a b hab χin χout hin hout hK hsout
    hCin hCout hbi hbo u using 1
  ring

/-- A uniform bound chosen before the data from only the two fixed compact
cutoffs and the time interval (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem exists_graphRetardedTest_bound (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hKi : HasCompactSupport χin) (hKo : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : graphTestSpace (d + 1) r,
      ‖graphTestToLp (graphRetardedTest t a χin χout hin hout hKo u)‖ ≤
        C * ‖graphTestToLp u‖ := by
  obtain ⟨Cin, hCin, hbi⟩ := Retarded.exists_cutoff_bound χin hin.continuous hKi
  obtain ⟨Cout, hCout, hbo⟩ := Retarded.exists_cutoff_bound χout hout.continuous hKo
  exact ⟨Cout * Cin * (b - a), by positivity,
    graphRetardedTest_norm_le t a b hab χin χout hin hout hKo hsout hCin hCout hbi hbo⟩

/-- The bounded extension of the literal `i` times lower integral on the SAME
Euclidean vector L² as the graph. Its identification below requires the actual
strip support, which proves the bound needed for extension.
Source: `app:ch_regular_base:eq:characteristic-integral`. -/
def graphRetardedOperator (t : Fin (d + 1)) (a : ℝ) (χin χout : E → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hKo : HasCompactSupport χout) : H →L[ℂ] H :=
  (graphTestToLp.comp (graphRetardedTestLinearMap t a χin χout hin hout hKo)).extendOfNorm
    graphTestToLp

/-- Exact realization of every existing graph test. All low-bound premises
are discharged from the fixed cutoffs and strip; no realization is an input.
Source: `app:ch_regular_base:eq:characteristic-integral`. -/
theorem graphRetardedOperator_graphTestToLp
    (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hKi : HasCompactSupport χin) (hKo : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b})
    (u : graphTestSpace (d + 1) r) :
    graphRetardedOperator t a χin χout hin hout hKo (graphTestToLp u) =
      graphTestToLp (graphRetardedTest t a χin χout hin hout hKo u) := by
  obtain ⟨C, _, hb⟩ := exists_graphRetardedTest_bound (r := r)
    t a b hab χin χout hin hout hKi hKo hsout
  exact LinearMap.extendOfNorm_eq denseRange_graphTestToLp ⟨C, hb⟩ u

/-- The concrete operator has the explicit cutoff/interval norm bound.
Source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem norm_graphRetardedOperator_le
    (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hKo : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b})
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hbi : ∀ x, |χin x| ≤ Cin) (hbo : ∀ x, |χout x| ≤ Cout) :
    ‖graphRetardedOperator (r := r) t a χin χout hin hout hKo‖ ≤ Cout * Cin * (b - a) :=
  LinearMap.opNorm_extendOfNorm_le denseRange_graphTestToLp (by positivity)
    (graphRetardedTest_norm_le t a b hab χin χout hin hout hKo hsout hCin hCout hbi hbo)

/-- The extension is uniquely determined by the literal action on the graph
tests (`app:ch_regular_base:eq:characteristic-integral`). -/
theorem graphRetardedOperator_unique
    (t : Fin (d + 1)) (a b : ℝ) (hab : a ≤ b)
    (χin χout : E → ℝ) (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hKi : HasCompactSupport χin) (hKo : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ {x | x t ∈ Icc a b}) (J : H →L[ℂ] H)
    (hJ : ∀ u : graphTestSpace (d + 1) r, J (graphTestToLp u) =
      graphTestToLp (graphRetardedTest t a χin χout hin hout hKo u)) :
    J = graphRetardedOperator t a χin χout hin hout hKo := by
  apply ContinuousLinearMap.ext
  apply congrFun
  exact denseRange_graphTestToLp.equalizer J.continuous
    (graphRetardedOperator t a χin χout hin hout hKo).continuous
    (funext (fun u ↦ (hJ u).trans
      (graphRetardedOperator_graphTestToLp t a b hab χin χout hin hout hKi hKo hsout u).symm))

end JanetCartan.FourierIntegral.RetardedRealization
