module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Limit

/-!
# Source Fourier reduction for full graph amplitudes

`app:ch_regular_base:thm:actual-calculus`, Step 1, on the original Euclidean
Lebesgue spaces. Actual coefficients use physical modes `2π k / ℓ`; one smooth
cutoff is constructed inside the enlarged cell. Joint coefficient bounds retain
the physical covector weights, Frobenius norms, and derivatives of every source
cutoff in the full amplitude. The single reserve `N=n+2` is fixed before `μ`.

`exists_sourceFourierExpansion` assembles the operator-norm source series and
the SAME literal full-amplitude regularizations. The final
`exists_literalSourceFourierExpansion` identifies their limit with the original
full-amplitude test integral and its literal Hilbert adjoint pairing, and proves
uniqueness of this bounded realization. Its analytic inputs are only
source-independent graph operators, their low bounds, a bounded exhausting
compact-frequency cutoff, test realizations, and coefficient-wise strong
regularization convergence. The phase/normal construction in
`jc-hamilton-phase`, `jc-compatible-phase-geometry`, and `jc-finite-fio-calculus`
must produce those inputs. This conditional reduction does not establish the
unconditional finite FIO calculus or Theorem 1.1. Source integration by parts
proves the full frequency-cutoff removal from the primitive derivative bound;
no full-amplitude convergence or full graph estimate is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

set_option maxHeartbeats 800000 in
/-- The full source Fourier reduction in
`app:ch_regular_base:thm:actual-calculus`, Step 1. The constructed operator is the
unique strong test limit of the literal full-amplitude regularizations, and its
adjoint is both the norm sum of the reversed adjoint terms and the limit of the
literal adjoint test pairings. No full-amplitude operator bound, reconstruction
identity, or source coefficient decay is assumed. The consumers
`jc-finite-fio-calculus`, `jc-response-near-carrier`, and `jc-response-complement`
must instantiate the explicit source-independent analytic inputs. The cutoff
exhaustion certifies the interpretation as a full oscillatory regularization;
the summation argument itself works for any common cutoff family. -/
theorem exists_sourceFourierExpansion (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hθc : ∀ j, HasCompactSupport (θ j))
    (_hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1))
    (C : (Fin n → ℤ) → H →L[ℂ] H)
    (Creg : ℕ → (Fin n → ℤ) → H →L[ℂ] H) (G : ℝ)
    (hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖C k‖ ≤ G * b)
    (hreg : ∀ j k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖Creg j k‖ ≤ G * b)
    (hreal : ∀ j k (u : graphTestSpace n r), Creg j k (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x _ η ↦ θ j η • matrixCoefficient ℓ A k x η) u)
    (hlim : ∀ k u, Tendsto (fun j ↦ Creg j k u) atTop (𝓝 (C k u))) :
    ∃ β : SourceCutoff n R ℓ, ∃ T : H →L[ℂ] H, ∃ Treg : ℕ → H →L[ℂ] H,
      HasSum (fun k ↦ (C k).comp (sourceModulation β k)) T ∧
      HasSum (fun k ↦ (sourceModulation β k).adjoint.comp (C k).adjoint) T.adjoint ∧
      ‖T‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n) ∧
      ‖T.adjoint‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n) ∧
      (∀ j, ‖Treg j‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n)) ∧
      (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
        graphTestOutput S (fun x y η ↦ θ j η • A x y η) u) ∧
      (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u))) ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Tendsto (fun j ↦ ∫ x,
          inner ℂ (graphTestOutput S (fun x y η ↦ θ j η • A x y η) u x) (w x))
          atTop (𝓝 (inner ℂ (graphTestToLp u) (T.adjoint w)))) ∧
      ∀ W : H →L[ℂ] H,
        (∀ u : graphTestSpace n r,
          Tendsto (fun j ↦ Treg j (graphTestToLp u)) atTop (𝓝 (W (graphTestToLp u)))) →
        W = T := by
  obtain ⟨β⟩ := nonempty_sourceCutoff (n := n) hℓ hR
  have hb' := hasFullSourceSymbolBound_seminorm hb
  let T := sourceOperatorSeries β C
  let Treg := fun j ↦ sourceOperatorSeries β (Creg j)
  have ht (u : H) : Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u)) :=
    tendsto_sourceOperatorSeries_apply hn hℓ hR A hs hA μ hb β C G hgraph Creg hreg hlim u
  refine ⟨β, T, Treg,
    hasSum_sourceOperatorTerm hn hℓ hR A hs hA μ hb β C G hgraph,
    hasSum_sourceOperatorTerm_adjoint hn hℓ hR A hs hA μ hb β C G hgraph,
    norm_sourceOperatorSeries_le hn hℓ hR A hs hA μ hb' β C G hgraph,
    norm_sourceOperatorSeries_adjoint_le hn hℓ hR A hs hA μ hb' β C G hgraph,
    (fun j ↦ norm_sourceOperatorSeries_le hn hℓ hR A hs hA μ hb' β (Creg j) G (hreg j)),
    (fun j ↦ sourceOperatorSeries_regularized_coeFn hn hℓ hR A hs hA μ hb β
      (Creg j) G (hreg j) S hS (θ j) (hθ j) (hθc j) (hreal j)), ht, ?_, ?_⟩
  · intro u w
    have hi := (ht (graphTestToLp u)).inner (𝕜 := ℂ) (tendsto_const_nhds (x := w))
    rw [← ContinuousLinearMap.adjoint_inner_right] at hi
    apply hi.congr
    intro j
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact sourceOperatorSeries_regularized_adjoint_pairing hn hℓ hR A hs hA μ hb β
      (Creg j) G (hreg j) S hS (θ j) (hθ j) (hθc j) (hreal j) u w
  · intro W hW
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer W.continuous T.continuous
    funext u
    exact tendsto_nhds_unique (hW u) (ht (graphTestToLp u))

set_option maxHeartbeats 800000 in
/-- Exact source reduction of the original full graph and its literal Hilbert
adjoint, with the single reserve `N=n+2` fixed before the joint order `μ`.
The coefficients are `matrixCoefficient ℓ A k`, the modes have physical frequency
`2π k / ℓ`, and the integral still uses Euclidean Lebesgue input data.

This completes the conditional deduction in
`app:ch_regular_base:thm:actual-calculus`, Step 1: both series converge in operator
norm, the full operator realizes `graphTestOutput S A`, and the actual adjoint
represents its integrable test pairing. Since the realization uses the original
full amplitude, all its physical and covector cutoffs remain unchanged.
The consumers `jc-finite-fio-calculus`, `jc-response-near-carrier`, and
`jc-response-complement` must supply the source-independent low graph bounds,
compact-frequency realizations, and coefficient-wise strong limits, together
with the stated primitive smoothness, support, jet and frequency-cutoff data.
Neither a full-amplitude graph bound nor its cutoff convergence is assumed. -/
theorem exists_literalSourceFourierExpansion (hn : 0 < n) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hθc : ∀ j, HasCompactSupport (θ j)) (hθb : ∀ j η, ‖θ j η‖ ≤ 1)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1))
    (C : (Fin n → ℤ) → H →L[ℂ] H)
    (Creg : ℕ → (Fin n → ℤ) → H →L[ℂ] H) (G : ℝ)
    (hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖C k‖ ≤ G * b)
    (hreg : ∀ j k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖Creg j k‖ ≤ G * b)
    (hreal : ∀ j k (u : graphTestSpace n r), Creg j k (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x _ η ↦ θ j η • matrixCoefficient ℓ A k x η) u)
    (hlim : ∀ k u, Tendsto (fun j ↦ Creg j k u) atTop (𝓝 (C k u))) :
    ∃ β : SourceCutoff n R ℓ, ∃ T : H →L[ℂ] H, ∃ Treg : ℕ → H →L[ℂ] H,
      HasSum (fun k ↦ (C k).comp (sourceModulation β k)) T ∧
      HasSum (fun k ↦ (sourceModulation β k).adjoint.comp (C k).adjoint) T.adjoint ∧
      ‖T‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n) ∧
      ‖T.adjoint‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n) ∧
      (∀ j, ‖Treg j‖ ≤ sourceOperatorConstant n r ℓ G * fullSourceSymbolSeminorm A (μ + lowReserve n)) ∧
      (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
        graphTestOutput S (fun x y η ↦ θ j η • A x y η) u) ∧
      (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u))) ∧
      (∀ u, T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
      (∀ u, MemLp (graphTestOutput S A u) 2 volume) ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Integrable (fun x ↦ inner ℂ (graphTestOutput S A u x) (w x)) ∧
        inner ℂ (graphTestToLp u) (T.adjoint w) =
          ∫ x, inner ℂ (graphTestOutput S A u x) (w x)) ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Tendsto (fun j ↦ ∫ x,
          inner ℂ (graphTestOutput S (fun x y η ↦ θ j η • A x y η) u x) (w x))
          atTop (𝓝 (inner ℂ (graphTestToLp u) (T.adjoint w)))) ∧
      ∀ W : H →L[ℂ] H,
        (∀ u, W (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) → W = T := by
  obtain ⟨β, T, Treg, hsum, hadj, hT, hTa, hTr, hr, ht, hp, _⟩ :=
    exists_sourceFourierExpansion hn hℓ hR A hs hA μ hb S hS θ hθ hθc hθlim
      C Creg G hgraph hreg hreal hlim
  have hfull (u : graphTestSpace n r) :
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u :=
    graphTestOutput_eq_of_strong_source_regularization_limit hn A hs hA μ hb S hS
      θ hθ hθc hθb hθlim T Treg u (fun j ↦ hr j u) (ht (graphTestToLp u))
  refine ⟨β, T, Treg, hsum, hadj, hT, hTa, hTr, hr, ht, hfull, ?_, ?_, hp, ?_⟩
  · intro u
    exact (Lp.memLp (T (graphTestToLp u))).ae_eq (hfull u)
  · intro u w
    have he : (fun x ↦ inner ℂ (T (graphTestToLp u) x) (w x)) =ᵐ[volume]
        (fun x ↦ inner ℂ (graphTestOutput S A u x) (w x)) :=
      (hfull u).mono fun x hx ↦ congrArg (fun v ↦ inner ℂ v (w x)) hx
    refine ⟨(L2.integrable_inner (𝕜 := ℂ) (T (graphTestToLp u)) w).congr he, ?_⟩
    rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
    exact integral_congr_ae he
  · intro W hW
    apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer W.continuous T.continuous
    funext u
    exact Lp.ext ((hW u).trans (hfull u).symm)

end JanetCartan.FourierIntegral.SourceExpansion
