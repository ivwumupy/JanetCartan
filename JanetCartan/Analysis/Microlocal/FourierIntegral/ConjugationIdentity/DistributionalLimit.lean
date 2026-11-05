module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.Compact
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Limits of the literal conjugation pairings

The local limit of `app:ch_regular_base:eq:direct-graph-identity`, conditional on
convergence of all three actual regularized terms. The stronger theorem
`twoTermGraph_distributional_conjugation` in `WeakConjugation` instead assumes
convergence of the undifferentiated graph and proves the weak differentiation
step using `WeakOutput`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- A local distributional limit of the exact compact-frequency identities in
`app:ch_regular_base:eq:direct-graph-identity`. Each limiting distribution is
the limit of the actual regularized term, not a formal residual field. The
hypotheses provide integrability of the right-hand Schwartz pairings and
convergence of all three literal pairings. This does not yet identify `F` with
the distributional physical operator applied to the limit of the undifferentiated
graph. That identification requires weak output integration by parts. The
conclusion is local to the output chart `O`. -/
theorem twoTermGraph_pairing_limit
    (H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : ℕ → Euclidean n → ℂ) (O : Set (Euclidean n)) (t : Fin n)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    (hreg : ∀ k, TwoTermGraphRegularization H B S U (χ k) O t)
    (F G R : 𝓢'(Euclidean n, Fin r → ℂ))
    (hGint : ∀ (k : ℕ) (φ : 𝓢(Euclidean n, ℂ)), Integrable (fun x ↦ φ x •
      graphOperator S (fun z _ η ↦ χ k η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x))
    (hRint : ∀ (k : ℕ) (φ : 𝓢(Euclidean n, ℂ)), Integrable (fun x ↦ φ x •
      graphOperator S (fun z _ η ↦ χ k η • twoTermGraphRemainder
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x))
    (hF : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ x, φ x • physicalOperator (fun z j ↦ complexifiedPencil (H z)
        (EuclideanSpace.single j 1)) B
        (graphOperator S (fun z _ η ↦ χ k η • twoTermGraphAmplitude
          (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v) x)
      atTop (𝓝 (F φ)))
    (hG : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ x, φ x • graphOperator S (fun z _ η ↦ χ k η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x) atTop (𝓝 (G φ)))
    (hR : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ x, φ x • graphOperator S (fun z _ η ↦ χ k η • twoTermGraphRemainder
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x)
      atTop (𝓝 (R φ))) :
    ∀ φ : 𝓢(Euclidean n, ℂ), tsupport φ ⊆ O → F φ = G φ + R φ := by
  intro φ hφ
  have heq (k : ℕ) :
      (∫ x, φ x • physicalOperator (fun z j ↦ complexifiedPencil (H z)
        (EuclideanSpace.single j 1)) B
        (graphOperator S (fun z _ η ↦ χ k η • twoTermGraphAmplitude
          (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v) x) =
      (∫ x, φ x • graphOperator S (fun z _ η ↦ χ k η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x) +
      (∫ x, φ x • graphOperator S (fun z _ η ↦ χ k η • twoTermGraphRemainder
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x) := by
    have hpoint (x : Euclidean n) :
      φ x • physicalOperator (fun z j ↦ complexifiedPencil (H z)
        (EuclideanSpace.single j 1)) B
        (graphOperator S (fun z _ η ↦ χ k η • twoTermGraphAmplitude
          (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v) x =
      φ x • (graphOperator S (fun z _ η ↦ χ k η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x +
      graphOperator S (fun z _ η ↦ χ k η • twoTermGraphRemainder
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x) := by
      by_cases hx : x ∈ O
      · exact congrArg (fun w : Fin r → ℂ ↦ φ x • w)
          ((sub_eq_iff_eq_add.mp ((hreg k).conjugation hv hvK hx)).trans (add_comm _ _))
      · have hzero : φ x = 0 := by
          by_contra hne
          exact hx (hφ (subset_tsupport (⇑φ) hne))
        simp [hzero]
    calc
      _ = ∫ x, φ x • (graphOperator S (fun z _ η ↦ χ k η • U z η)
          (fun y ↦ -Complex.I • partialDeriv v y t) x +
        graphOperator S (fun z _ η ↦ χ k η • twoTermGraphRemainder
          (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
          (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = _ := by
        simp_rw [smul_add]
        exact integral_add (hGint k φ) (hRint k φ)
  have ht := (hG φ).add (hR φ)
  exact tendsto_nhds_unique (hF φ) (ht.congr fun k ↦ (heq k).symm)


end JanetCartan.FourierIntegral
