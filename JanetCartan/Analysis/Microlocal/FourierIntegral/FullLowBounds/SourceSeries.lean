module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientOperators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.AdjointSeries

/-!
# Literal source-series assembly and strong adjoint convergence

For `app:ch_regular_base:thm:actual-calculus`, Step 1, assemble the coefficient
graphs supplied by `CoefficientOperators`. Both strong limits use the same
source series. The final uniform construction discharges every coefficient
operator hypothesis using the original primitive geometry and full-symbol jets.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds NormalComparison FrequencyCutoff AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Assemble the actual coefficient graphs into the single literal full
source series.  The regularized terms are the same compact vector graphs from
the coefficient construction, so the theorem supplies the strong forward and
adjoint limits and the literal full-amplitude test realization through
`exists_literalSourceFourierExpansion`. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem exists_literalSourceFourierExpansion_of_coefficientGraphs
    (hn : 0 < n) {R ℓ : ℝ} (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {B : ℝ} (hb : HasFullSourceSymbolBound A
      (primitiveNormalReserve n + lowReserve n) B)
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    {Kout : Set E} (hKout : IsCompact Kout)
    (hscoef : ∀ k x ξ, x ∉ Kout → matrixCoefficient ℓ A k x ξ = 0)
    (c C : ℝ) (hc : 1 ≤ c) (hC : 0 < C)
    (hcoeff : ∀ k : Fin n → ℤ, ∃ T : H →L[ℂ] H,
      ‖T‖ ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
        coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n)) ∧
      ‖T.adjoint‖ ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
        coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n)) ∧
      (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S
          (fun z _ ξ ↦ matrixCoefficient ℓ A k z ξ)
          (graphTestToSchwartz u) x)) ∧
      (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S
          (fun z _ ξ ↦ matrixCoefficient ℓ A k z ξ) u x)) ∧
      (∀ f : H, Tendsto (fun l ↦ compactVectorGraph hS.continuous
        (cutAmplitude_entry_continuous
          (contDiff_matrixCoefficient A hA ℓ k).continuous l)
        (cutAmplitude_entry_hasCompactSupport hKout (hscoef k) l) f) atTop (𝓝 (T f))) ∧
      coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n) ≤
        ((r : ℝ)^2 * coefficientConstant n (lowReserve n) ℓ * B *
          decayWeight (lowReserve n) k)) :
    ∃ G : (Fin n → ℤ) → H →L[ℂ] H,
    ∃ β : SourceCutoff n R ℓ, ∃ U : H →L[ℂ] H, ∃ Ureg : ℕ → H →L[ℂ] H,
      HasSum (fun k ↦ (G k).comp (sourceModulation β k)) U ∧
      HasSum (fun k ↦ (sourceModulation β k).adjoint.comp (G k).adjoint) U.adjoint ∧
      ‖U‖ ≤ sourceOperatorConstant n r ℓ
        (C * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c) *
          fullSourceSymbolSeminorm A (primitiveNormalReserve n + lowReserve n) ∧
      ‖U.adjoint‖ ≤ sourceOperatorConstant n r ℓ
        (C * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c) *
          fullSourceSymbolSeminorm A (primitiveNormalReserve n + lowReserve n) ∧
      (∀ j, ‖Ureg j‖ ≤ sourceOperatorConstant n r ℓ
        (C * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c) *
          fullSourceSymbolSeminorm A (primitiveNormalReserve n + lowReserve n)) ∧
      (∀ j u, Ureg j (graphTestToLp u) =ᵐ[volume]
        graphTestOutput S (fun x y η ↦ complexPhysicalCutoff j η • A x y η) u) ∧
      (∀ u, Tendsto (fun j ↦ Ureg j u) atTop (𝓝 (U u))) ∧
      (∀ u, Tendsto (fun j ↦ (Ureg j).adjoint u) atTop (𝓝 (U.adjoint u))) ∧
      (∀ u, U (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
      (∀ u, MemLp (graphTestOutput S A u) 2 volume) ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Integrable (fun x ↦ inner ℂ (graphTestOutput S A u x) (w x)) ∧
        inner ℂ (graphTestToLp u) (U.adjoint w) =
          ∫ x, inner ℂ (graphTestOutput S A u x) (w x)) ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Tendsto (fun j ↦ ∫ x,
          inner ℂ (graphTestOutput S
            (fun x y η ↦ complexPhysicalCutoff j η • A x y η) u x) (w x))
          atTop (𝓝 (inner ℂ (graphTestToLp u) (U.adjoint w)))) ∧
      ∀ W : H →L[ℂ] H,
        (∀ u, W (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) → W = U := by
  choose G hG using hcoeff
  let hAc : ∀ k, Continuous (Function.uncurry (matrixCoefficient ℓ A k)) :=
    fun k ↦ (contDiff_matrixCoefficient A hA ℓ k).continuous
  let Creg : ℕ → (Fin n → ℤ) → H →L[ℂ] H := fun j k ↦
    compactVectorGraph hS.continuous (cutAmplitude_entry_continuous (hAc k) j)
      (cutAmplitude_entry_hasCompactSupport hKout (hscoef k) j)
  let G0 : ℝ := C * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c
  have hfull : HasFullSourceSymbolBound A
      (primitiveNormalReserve n + lowReserve n) (fullSourceSymbolSeminorm A
        (primitiveNormalReserve n + lowReserve n)) :=
    hasFullSourceSymbolBound_seminorm hb
  have hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k)
      (primitiveNormalReserve n) b → ‖G k‖ ≤ G0 * b := by
    intro k b hbk
    rcases hG k with ⟨hTk, _, _, _, _, _⟩
    have hs := coefficientSymbolSeminorm_le_of_bound hbk
    have hnonneg : 0 ≤ G0 := by
      dsimp [G0]
      exact mul_nonneg hC.le
        (normalizedCoefficientJetConstant_pos (n := n)
          (primitiveNormalReserve n) hc).le
    have hjet : 0 ≤ normalizedCoefficientJetConstant n (primitiveNormalReserve n) c :=
      (normalizedCoefficientJetConstant_pos (n := n) (primitiveNormalReserve n)
        hc).le
    have hsb : normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
        coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n) ≤
        normalizedCoefficientJetConstant n (primitiveNormalReserve n) c * b := by
      exact (mul_le_mul_of_nonneg_left hs hjet)
    calc
      ‖G k‖ ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
          coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n)) := hTk
      _ ≤ G0 * b := by
        dsimp [G0]
        calc
          C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
            coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n))
              ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c * b) :=
                mul_le_mul_of_nonneg_left hsb hC.le
          _ = C * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c * b := by ring
  have hreg : ∀ j k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k)
      (primitiveNormalReserve n) b → ‖Creg j k‖ ≤ G0 * b := by
    intro j k b hbk
    rcases hG k with ⟨hTk, _, _, hsch, _, _⟩
    have hs := coefficientSymbolSeminorm_le_of_bound hbk
    have heq := compactVectorGraph_cut_eq_comp hS.continuous (hAc k) hKout (hscoef k)
      (G k) hsch j
    dsimp [Creg]
    rw [heq]
    calc
      ‖(G k).comp (multiplier j)‖ ≤ ‖G k‖ * ‖multiplier j‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖G k‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_multiplier_le j)
      _ ≤ G0 * b := hgraph k b hbk
  have hreal : ∀ j k (u : graphTestSpace n r), Creg j k (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x _ η ↦ complexPhysicalCutoff j η •
        matrixCoefficient ℓ A k x η) u := by
    intro j k u
    rw [← schwartzVectorToLp_graphTestToSchwartz u]
    have hu : (graphTestToSchwartz u : E → Fin r → ℂ) =
        (fun y ↦ (u.val y).ofLp) := by
      funext y
      rfl
    have hgo : graphTestOutput S
        (fun x y η ↦ complexPhysicalCutoff j η • matrixCoefficient ℓ A k x η) u =
        (fun x ↦ WithLp.toLp 2 (graphOperator S
          (fun x y η ↦ complexPhysicalCutoff j η • matrixCoefficient ℓ A k x η)
          (fun y ↦ (u.val y).ofLp) x)) := rfl
    rw [hgo]
    simpa [Creg, cutAmplitude, hu] using
      compactVectorGraph_schwartz_ae hS.continuous
        (cutAmplitude_entry_continuous (hAc k) j)
        (cutAmplitude_entry_hasCompactSupport hKout (hscoef k) j)
        (graphTestToSchwartz u)
  have hlim : ∀ k u, Tendsto (fun j ↦ Creg j k u) atTop (𝓝 (G k u)) := by
    intro k u
    rcases hG k with ⟨_, _, _, _, hstrong, _⟩
    simpa [Creg] using hstrong u
  have hadjlim : ∀ k u, Tendsto (fun j ↦ (Creg j k).adjoint u) atTop
      (𝓝 ((G k).adjoint u)) := by
    intro k u
    exact compactVectorGraph_cut_adjoint_tendsto_of_realizes hS.continuous (hAc k)
      hKout (hscoef k) (G k) (hG k).2.2.2.1 u
  obtain ⟨β, U, Ureg, hsum, hasum, hU, hUa, hUr, hr, ht, hfull, hmem, hp, hpl, huniq⟩ :=
    exists_literalSourceFourierExpansion (n := n) (r := r) hn hℓ hRcell A hs hA
      (primitiveNormalReserve n) hfull S hS
      (fun j ↦ complexPhysicalCutoff j)
      (fun j ↦ complexPhysicalCutoff_contDiff j)
      (fun j ↦ complexPhysicalCutoff_hasCompactSupport j)
      (fun j η ↦ complexPhysicalCutoff_norm_le j η)
      (fun η ↦ complexPhysicalCutoff_tendsto η)
      G Creg G0 hgraph hreg hreal hlim
  have hUeq : U = sourceOperatorSeries β G :=
    hsum.unique (hasSum_sourceOperatorTerm hn hℓ hRcell A hs hA
      (primitiveNormalReserve n) hb β G G0 hgraph)
  have hUreq : ∀ j, Ureg j = sourceOperatorSeries β (Creg j) := by
    intro j
    exact sourceOperatorSeries_regularized_unique hn hℓ hRcell A hs hA
      (primitiveNormalReserve n) hb β (Creg j) G0 (hreg j) S hS
      (complexPhysicalCutoff j) (complexPhysicalCutoff_contDiff j)
      (complexPhysicalCutoff_hasCompactSupport j) (hreal j) (Ureg j) (hr j)
  refine ⟨G, β, U, Ureg, hsum, hasum, hU, hUa, hUr, hr, ht, ?_,
    hfull, hmem, hp, hpl, huniq⟩
  intro u
  simp_rw [hUeq, hUreq]
  exact tendsto_sourceOperatorSeries_adjoint_apply hn hℓ hRcell A hs hA
    (primitiveNormalReserve n) hb β G G0 hgraph Creg hreg hadjlim u

end JanetCartan.FourierIntegral.FullLowBounds
