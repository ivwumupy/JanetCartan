module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Segment
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.CoefficientBudgets

/-!
# Reserve-graded parameter phase coefficients

The actual `C` in `app:ch_response:thm:response-literal-transfer` contracts
the carrier differential with the averaged covector Hessian. The segment
estimate and Leibniz rule retain the reserve in
`app:ch_response:eq:direct-envelope-profile`. The consumer is the global
primitive assembly in `GradedPrimitives`; the independent phase-jet producer
must supply the primitive Hessian profile on the buffered convex chart.
Only carrier jets through `N+1` and Hessian jets through `N` are used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.GradedPrimitives

/-- Fixed finite constant for the actual parameter coefficient in
`app:ch_response:eq:direct-envelope-profile`, before scale and frequency. -/
def parameterConstant (n p : ℕ) (A : ℕ → ℝ) (Z : ℝ) (k : ℕ) : ℝ :=
  bilinearConstant (parameterCoefficientContraction n p) (fun _ ↦ Z)
    (segmentConstant A Z) k

/-- Nonnegativity of the parameter coefficient constant, for the reverse
composition in `app:ch_response:eq:direct-envelope-profile`. -/
theorem parameterConstant_nonneg (n p : ℕ) {A : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) {Z : ℝ} (hZ : 0 ≤ Z) (k : ℕ) :
    0 ≤ parameterConstant n p A Z k := by
  exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hZ) (segmentConstant_nonneg hA hZ _))

/-- The literal `C` is the contraction of the actual Hessian integral,
with the segment direction before the carrier variation
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterPhaseCoefficient_eq_contraction_average {n p : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
    (q : ParameterCoefficientSpace n p) :
    parameterPhaseCoefficient S ζ q.1 q.2.1 q.2.2 =
      parameterCoefficientContraction n p (fderiv ℝ ζ q.2.2)
        (normalizedSegmentAverage
          (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) ζ q) := rfl

/-- Joint reserve-graded jets of the actual parameter coefficient. The input
bounds concern the primitive covector Hessian and fixed carrier only;
integration and contraction produce all coefficient derivatives. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_parameterPhaseCoefficient_le
    {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
    {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)}
    {C : Set (Euclidean p)}
    (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
    (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
    (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
    (hH : ContDiffOn ℝ ∞
      (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))
    (hζ : ContDiffOn ℝ ∞ ζ C)
    {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hHjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) w‖ ≤
        A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2) q‖ ≤
        parameterConstant n p A Z k * L ^ (k - R) := by
  let H := fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2
  have hdζ : ContDiffOn ℝ ∞ (fderiv ℝ ζ) C := hζ.fderiv_of_isOpen hC (by simp)
  have hd : ContDiffOn ℝ ∞
      (fun w : ParameterCoefficientSpace n p ↦ fderiv ℝ ζ w.2.2) (X ×ˢ V ×ˢ C) := by
    intro w hw
    exact ((hdζ.contDiffAt (hC.mem_nhds hw.2.2)).comp w
      contDiffAt_snd.snd).contDiffWithinAt
  have hav := normalizedSegmentAverage_contDiffOn hX hD hV hC hcD hζD hbuffer hH hζ
  change ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
    parameterCoefficientContraction n p (fderiv ℝ ζ w.2.2)
      (normalizedSegmentAverage H ζ w)) q‖ ≤ _
  apply norm_jet_bilinear_le (parameterCoefficientContraction n p) (hX.prod (hV.prod hC))
    (hd.of_le (by simp : (N : ℕ∞ω) ≤ ∞)) (hav.of_le (by simp)) hk hq
    (fun _ ↦ Z) (segmentConstant A Z) (fun _ ↦ hZ) (segmentConstant_nonneg hA hZ) hL R
  · intro j hj
    apply (norm_parameterCoefficient_pullback_le hC hdζ hq.2.2 j).trans
    rw [norm_iteratedFDeriv_fderiv]
    exact (hζjet (j + 1) (by omega) (by omega) _ hq.2.2).trans
      (le_mul_of_one_le_right hZ (one_le_pow₀ hL))
  · intro j hj
    exact norm_jet_normalizedSegmentAverage_le hX hD hV hC hcD hζD hbuffer hH hζ
      hA hZ hL hHjet (fun i hi hiN ↦ hζjet i hi (by omega)) (hj.trans hk) hq

end JanetCartan.ResponseTransfer.GradedPrimitives
