module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily.Buffered
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic

/-!
# Joint common inverses for the literal full and transverse phase charts

The inverse-family conclusion of `app:ch_seed:prop:seed-phase-charts`, conditional
on joint quotient smoothness and the two quarter-gap/value comparison inputs.
The maps below only regroup the arguments of the published `Comparison` maps.
The full map retains the Hilbert spacetime norm before applying `ofLp`; the
data coordinates use the same product norm as the frozen triangular map.

The parameter sets are **open neighborhoods** of the desired closed boxes,
with epsilon as their first coordinate. Thus smoothness is ambient at epsilon
zero and at both endpoints. `BufferedPhaseInverse.contDiffAt_on_box` records
this explicitly. All physical and spectator variables remain independent.

Actual phase/carrier construction, joint forward smoothness on these open
extensions, and uniform derivative/value comparison are producer obligations
(`QuotientSmoothness`, `Comparison`, and `JacobianBounds`); this module does
not assert they hold for an unconstructed Hamilton phase. Inverse tame estimates
are the separate `InverseEstimates` task. The parent full-phase chart and
compatible-geometry constructions must instantiate every displayed hypothesis.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The literal full map in `app:ch_seed:prop:seed-phase-charts`, with parameters
`(epsilon, spectator, x, x')` and data `(z₁, eta)`. -/
def fullChartFamily (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (q : ℝ × P × WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) (u : ℝ × E) : ℝ × E :=
  Comparison.fullChart S ζ q.1 q.2.1 q.2.2.1 q.2.2.2 u

/-- The literal transverse map in `app:ch_seed:prop:seed-phase-charts`, with
parameters `(epsilon, spectator, t, z₁, y, y')` and data `eta`. The time is
fixed along each transverse segment, but varies jointly in the inverse family. -/
def transverseChartFamily (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (q : ℝ × P × ℝ × ℝ × E × E) (η : E) : E :=
  Comparison.transverseChart S ζ q.1 q.2.1 q.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2
    (q.2.2.2.1, η)

/-- Common inverses of the exact full quotient chart, from joint smoothness
of the Hilbert-space two-point gradient and the literal normalized comparisons
(`app:ch_seed:prop:seed-phase-charts`). The constants and compact core are fixed
before choosing the phase, carrier, and parameter family. -/
theorem exists_fullChart_inverseFamily
    {K D₁ D : Set (ℝ × E)} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : (ℝ × E) ≃L[ℝ] (ℝ × E)) {f₀ : (ℝ × E) → (ℝ × E)}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D, ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
      (fderiv ℝ f₀ x) - ContinuousLinearMap.id ℝ (ℝ × E)‖ ≤ 1 / 4) :
    ∃ c > 0, ∃ δ > 0, ∃ V L : Set (ℝ × E),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
        (U : Set (ℝ × P × WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)))
        (O : Set (ℝ × E)), IsOpen U → IsOpen O → D ⊆ O →
        ContDiffOn ℝ ∞ (fun q :
          (ℝ × P × WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E)) × (ℝ × E) ↦
          Comparison.modulationChart S ζ q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
          (U ×ˢ O) →
        (∀ p ∈ U, ∀ u ∈ D, ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
          (fderiv ℝ (fullChartFamily S ζ p) u - fderiv ℝ f₀ u)‖ ≤ 1 / 4) →
        (∀ p ∈ U, ∀ u ∈ K, ‖fullChartFamily S ζ p u - f₀ u‖ ≤ δ) →
        BufferedPhaseInverse (fullChartFamily S ζ) U K D₁ D V L δ c G := by
  obtain ⟨c, hc, δ, hδ, V, L, hV, hVc, hLc, hLV, hs⟩ :=
    exists_common_smooth_phase_inverses
      (P := ℝ × P × WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E))
      hK hD₁ hK₁ h₁D hD G hf₀ hgap₀
  refine ⟨c, hc, δ, hδ, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro S ζ U O hU hO hDO hmod hgap hvalue
  apply hs (fullChartFamily S ζ) U O hU hO hDO _ hgap hvalue
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff.comp_contDiffOn hmod

/-- Common inverses of the exact transverse quotient chart on a fixed eta box
(`app:ch_seed:prop:seed-phase-charts`). The frozen map is the identity, so its
quarter gap is proved here; the perturbation quarter gap and value error remain
the literal comparison inputs. All six groups of parameters vary jointly. -/
theorem exists_transverseChart_inverseFamily
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D) :
    ∃ c > 0, ∃ δ > 0, ∃ V L : Set E,
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
        (U : Set (ℝ × P × ℝ × ℝ × E × E)) (O : Set E),
        IsOpen U → IsOpen O → D ⊆ O →
        ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily S ζ)) (U ×ˢ O) →
        (∀ p ∈ U, ∀ η ∈ D, ‖fderiv ℝ (transverseChartFamily S ζ p) η -
          ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) →
        (∀ p ∈ U, ∀ η ∈ K, ‖transverseChartFamily S ζ p η - η‖ ≤ δ) →
        BufferedPhaseInverse (transverseChartFamily S ζ) U K D₁ D V L δ c
          (ContinuousLinearEquiv.refl ℝ E) := by
  obtain ⟨c, hc, δ, hδ, V, L, hV, hVc, hLc, hLV, hs⟩ :=
    exists_common_smooth_phase_inverses (P := ℝ × P × ℝ × ℝ × E × E)
      hK hD₁ hK₁ h₁D hD (ContinuousLinearEquiv.refl ℝ E) (f₀ := id)
      (fun _ _ ↦ differentiableAt_id) (by intro x _; simp)
  refine ⟨c, hc, δ, hδ, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro S ζ U O hU hO hDO hf hgap hvalue
  apply hs (transverseChartFamily S ζ) U O hU hO hDO hf _ hvalue
  simpa using hgap

end JanetCartan.FullPhaseCharts
