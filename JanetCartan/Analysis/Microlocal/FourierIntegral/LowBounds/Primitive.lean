module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CutoffJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut

/-!
# The source-independent low L² theorem from uncut primitive data

This completes the operator construction in Step 1 of
`app:ch_regular_base:thm:actual-calculus`, conditional on the original phase,
inverse-chart and symbol data. The reserve is `primitiveNormalReserve n`,
namely `2 * (n + 1)`. The constant is chosen before the amplitude, its size,
the frequency cutoff, and the shell index. All cutoff jets, transformed normal
budgets, compact normal identities, and limiting operators are derived.

The geometric hypotheses have the following actual producers:
* `jc-hamilton-phase` and `jc-compatible-phase-geometry`: the measurable
  source chart, segment differentiability and integrability, the actual
  averaged-gradient derivative, injectivity, inverse equations, determinant
  gap, linear frequency growth, bounded physical box, open buffered domain,
  smooth original Jacobian and its normalized jets, and forward continuity.
* `jc-normal-inverse-coefficients`: smoothness, range inclusion, and normalized
  finite jets of the actual inverse map.
* The consuming `jc-finite-fio-calculus`, `jc-regular-sector`, and response
  tasks: the original continuous symbol, its order-zero shell jets, fixed
  compact output support and source-chart support, polynomial domination,
  and closed carrier image strictly inside the inverse chart.

Every field of `AveragedGradientChart`, `PrimitiveNormalGeometry`, and the
uncut `PrimitiveNormalShellInputs` remains an explicit primitive hypothesis.
In particular this theorem does not instantiate the paper's Hamilton family
or prove the full finite calculus. It requires no homogeneity or phase
smoothness at zero. Physical covectors and the factor `(2π)^(-n)` are those
of the existing literal `graphOperator` on Euclidean Lebesgue L².
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The unique bounded pure type-I graph from original uncut primitive data,
with a bound linear in the amplitude size (including size zero). The same
operator realizes compact smooth and Schwartz tests; its actual compact
graphs and literal adjoints converge strongly, with exact right-frequency
factorizations. Physical source cutting gives the literal full amplitude and
the reversed adjoint composition, with the same bound.

The consumer must instantiate the primitive geometry and symbol hypotheses
listed in the module documentation. No cutoff-amplitude estimate, transformed
normal estimate, operator identity, or limiting map is assumed. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1, and
`app:ch_regular_base:eq:actual-normal-kernel`--`actual-normal-amplitude`. -/
theorem exists_graphL2_of_primitive_inputs (hn : 0 < n) (R M L : ℝ)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) :
    ∃ C > 0, ∀ (X D : Set E) (S : E → E → ℝ) (A : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n))
      (a : ℝ), 0 ≤ a → AveragedGradientChart S X D η J δ →
      PrimitiveNormalGeometry X D S A A η J W K →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖)) →
      (∀ l, PrimitiveNormalShellInputs A A η J ((2 : ℝ)^l)
        (primitiveNormalReserve n) M L δ a a
        (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)) →
      ∀ (hS : Continuous (Function.uncurry S)) (hA : Continuous (Function.uncurry A))
        (Kout : Set E) (hKout : IsCompact Kout)
        (hsA : ∀ x η, x ∉ Kout → A x η = 0),
      (∀ x u, x ∉ X ∨ u ∉ D → A x u = 0) →
      ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A A) →
      ∀ (P : ℝ) (k : ℕ), (∀ x η, ‖A x η‖ ≤ P * (1 + ‖η‖ ^ k)) →
      let Tj : ℕ → H →L[ℂ] H := fun j ↦ compactVectorGraph hS
        (cutAmplitude_entry_continuous hA j)
        (cutAmplitude_entry_hasCompactSupport hKout hsA j)
      ∃ T : H →L[ℂ] H, ‖T‖ ≤ C * a ∧ ‖T.adjoint‖ ≤ C * a ∧
        (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
            (graphTestToSchwartz u) x)) ∧
        (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) ∧
        (∀ f : H, Tendsto (fun j ↦ Tj j f) atTop (𝓝 (T f))) ∧
        (∀ f : H, Tendsto (fun j ↦ (Tj j).adjoint f) atTop (𝓝 (T.adjoint f))) ∧
        (∀ j, Tj j = T.comp (multiplier j)) ∧
        (∀ j, (Tj j).adjoint = (multiplier j).comp T.adjoint) ∧
        (∀ (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hb : ∀ x, ‖χ x‖ ≤ 1),
          let Tc := T.comp (sourceCutMultiplier χ hχ.continuous hb)
          ‖Tc‖ ≤ C * a ∧ ‖Tc.adjoint‖ ≤ C * a ∧
          Tc.adjoint = (sourceCutMultiplier χ hχ.continuous hb).comp T.adjoint ∧
          ∀ u : graphTestSpace n r, Tc (graphTestToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun x y η ↦ (χ y : ℂ) • A x η)
              (graphTestToSchwartz u) x)) ∧
        ∀ U : H →L[ℂ] H, (∀ u : graphTestSpace n r, U (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
            (graphTestToSchwartz u) x)) → U = T := by
  obtain ⟨C, hC, hlimit⟩ := exists_graphL2_of_primitive_cutoffs (r := r) hn R M L hδ
  obtain ⟨Kcut, hKcut, hcut⟩ := exists_cutAmplitude_primitiveNormalShellInputs
    (n := n) (r := r) hF
  refine ⟨C * Kcut, mul_pos hC hKcut, ?_⟩
  intro X D S A η J W K V a ha chart geometry hR hgrowth jets hS hA Kout hKout hsA
    hcarrier hforward P k hpolynomial
  dsimp only
  obtain ⟨V', _, hjets⟩ := hcut X D S η J M L δ chart hgrowth A a V ha jets
  obtain ⟨T, hT, hTa, htest, hschwartz, hstrong, hadjoint, huniq⟩ :=
    hlimit X D S A η J W K V' (Kcut * a) (mul_nonneg hKcut.le ha) chart geometry
      hR hjets hS hA Kout hKout hsA hcarrier hforward P k hpolynomial
  have hnorm : ‖T‖ ≤ C * Kcut * a := by simpa only [mul_assoc] using hT
  refine ⟨T, hnorm, ?_, htest, hschwartz, hstrong, hadjoint,
    compactVectorGraph_cut_eq_comp hS hA hKout hsA T hschwartz,
    compactVectorGraph_cut_adjoint_eq_comp hS hA hKout hsA T hschwartz, ?_, huniq⟩
  · simpa only [mul_assoc] using hTa
  · intro χ hχ hb
    exact ⟨(norm_sourceCutGraph_le T χ hχ.continuous hb).trans hnorm,
      (norm_sourceCutGraph_adjoint_le T χ hχ.continuous hb).trans hnorm,
      sourceCutGraph_adjoint T χ hχ.continuous hb,
      sourceCutGraph_ae_graphOperator S A T htest χ hχ hb⟩

end JanetCartan.FourierIntegral.LowBounds
