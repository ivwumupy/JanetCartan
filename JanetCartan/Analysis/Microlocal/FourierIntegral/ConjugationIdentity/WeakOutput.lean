module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.Compact
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Weak output differentiation of the graph operator

For `app:ch_regular_base:eq:direct-graph-identity`, compact local tests absorb
smooth coefficients without global growth assumptions. Integration by parts
identifies the actual physical operator with its distributional action. Hence
weak convergence of the undifferentiated graphs suffices for the differentiated
limit. The consumer is `twoTermGraph_distributional_conjugation`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Compact tests supported in the output chart give integrable local pairings
for `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integrable_local_graph_test_mul {O : Set (Euclidean n)} (hO : IsOpen O)
    {ψ g : Euclidean n → ℂ} (hψ : Continuous ψ) (hK : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ O) (hg : ContinuousOn g O) :
    Integrable (fun x ↦ ψ x * g x) := by
  apply Continuous.integrable_of_hasCompactSupport _ hK.mul_right
  apply continuous_of_tsupport
  intro x hx
  exact (hψ.continuousAt.mul (hg.continuousAt (hO.mem_nhds
    (hs (tsupport_mul_subset_left hx)))))

/-- Coefficient times a compact local test, for weak interpretation of
`app:ch_regular_base:eq:direct-graph-identity`. Only local coefficient smoothness
is needed; this is the literal product, extended by its already zero values. -/
def graphCoefficientTest {O : Set (Euclidean n)} (hO : IsOpen O)
    (φ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (a : Euclidean n → ℂ) (ha : ContDiffOn ℝ ∞ a O) : 𝓢(Euclidean n, ℂ) :=
  (hK.mul_right (f' := a)).toSchwartzMap (by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact (φ.smooth ⊤).contDiffAt.mul (ha.contDiffAt (hO.mem_nhds (hs hx)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy])

/-- The output derivative moves to the compact coefficient-weighted test.
Consumed by the distributional direct graph identity
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem integral_local_test_partialDeriv {O : Set (Euclidean n)} (hO : IsOpen O)
    (ψ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O)
    {f : Euclidean n → ℂ} (hf : ContDiffOn ℝ ∞ f O) (j : Fin n) :
    (∫ x, ψ x * partialDeriv f x j) =
      -(∫ x, (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) ψ) x * f x) := by
  have hd : ContinuousOn (fun x ↦ partialDeriv f x j) O := by
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hp := SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.single j (1 : ℝ)) ψ
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_local_graph_test_mul hO (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) ψ).continuous
      (hK.of_isClosed_subset (isClosed_tsupport _) hp) (hp.trans hs) hf.continuousOn)
    (integrable_local_graph_test_mul hO ψ.continuous hK hs hd)
    (integrable_local_graph_test_mul hO ψ.continuous hK hs hf.continuousOn)
    (fun x _ ↦ ψ.differentiable x)
    (fun x hx ↦ (hf.contDiffAt (hO.mem_nhds (hs hx))).differentiableAt (by simp))

/-- The distributional action of `L = -i(∑ Aⱼ ∂ⱼ + B)` on a compact local
scalar test. Matrix indices are contracted in their original order. This is the
weak left side of `app:ch_regular_base:eq:direct-graph-identity`. -/
def graphPhysicalDistributionPairing {O : Set (Euclidean n)} (hO : IsOpen O)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ j i l, ContDiffOn ℝ ∞ (fun x ↦ A x j i l) O)
    (hB : ∀ i l, ContDiffOn ℝ ∞ (fun x ↦ B x i l) O)
    (F : 𝓢'(Euclidean n, Fin r → ℂ))
    (φ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (i : Fin r) : ℂ :=
  Complex.I * (∑ j, ∑ l, F (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ))
    (graphCoefficientTest hO φ hK hs (fun x ↦ A x j i l) (hA j i l))) l) -
    Complex.I * (∑ l, F (graphCoefficientTest hO φ hK hs (fun x ↦ B x i l) (hB i l)) l)

/-- Integration by parts identifies the literal physical operator with its weak
coefficient-weighted pairing. All integrability follows from compact test support
and local smoothness. Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem physicalOperator_local_pairing {O : Set (Euclidean n)} (hO : IsOpen O)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ j i l, ContDiffOn ℝ ∞ (fun x ↦ A x j i l) O)
    (hB : ∀ i l, ContDiffOn ℝ ∞ (fun x ↦ B x i l) O)
    {f : Euclidean n → Fin r → ℂ} (hf : ContDiffOn ℝ ∞ f O)
    (φ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (i : Fin r) :
    (∫ x, φ x * physicalOperator A B f x i) =
      Complex.I * (∑ j, ∑ l, ∫ x,
        (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ))
          (graphCoefficientTest hO φ hK hs (fun x ↦ A x j i l) (hA j i l))) x * f x l) -
      Complex.I * (∑ l, ∫ x,
        graphCoefficientTest hO φ hK hs (fun x ↦ B x i l) (hB i l) x * f x l) := by
  let a := fun j l ↦ graphCoefficientTest hO φ hK hs (fun x ↦ A x j i l) (hA j i l)
  let b := fun l ↦ graphCoefficientTest hO φ hK hs (fun x ↦ B x i l) (hB i l)
  have hf' (l : Fin r) := contDiffOn_pi.mp hf l
  have haK (j l) : HasCompactSupport (a j l) := hK.mul_right
  have haO (j l) : tsupport (a j l) ⊆ O := tsupport_mul_subset_left.trans hs
  have hbK (l) : HasCompactSupport (b l) := hK.mul_right
  have hbO (l) : tsupport (b l) ⊆ O := tsupport_mul_subset_left.trans hs
  have hd (j l) : ContinuousOn (fun x ↦ partialDeriv (fun y ↦ f y l) x j) O := by
    intro x hx
    exact ((((hf' l).contDiffAt (hO.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hai (j l) := integrable_local_graph_test_mul hO (a j l).continuous (haK j l) (haO j l) (hd j l)
  have hbi (l) := integrable_local_graph_test_mul hO (b l).continuous (hbK l) (hbO l) (hf' l).continuousOn
  have he (x : Euclidean n) : φ x * physicalOperator A B f x i =
      -Complex.I * ((∑ j, ∑ l, a j l x * partialDeriv (fun y ↦ f y l) x j) +
        ∑ l, b l x * f x l) := by
    by_cases hx : x ∈ O
    · have hc (j l) : partialDeriv (fun y ↦ f y l) x j = partialDeriv f x j l := by
        simp [partialDeriv, fderiv_apply ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
      simp [a, b, graphCoefficientTest, physicalOperator, Matrix.mulVec, dotProduct,
        hc, Finset.mul_sum, Finset.sum_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))
      simp [a, b, graphCoefficientTest, hz]
  simp_rw [he]
  rw [integral_const_mul, integral_add
    (integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun l _ ↦ hai j l)
    (integrable_finsetSum _ fun l _ ↦ hbi l),
    integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ fun l _ ↦ hai j l),
    integral_finsetSum _ (fun l _ ↦ hbi l)]
  simp_rw [integral_finsetSum _ (fun l _ ↦ hai _ l),
    integral_local_test_partialDeriv hO (a _ _) (haK _ _) (haO _ _) (hf' _) _,
    Finset.sum_neg_distrib]
  dsimp only [a, b]
  ring

set_option maxHeartbeats 600000 in
/-- Weak convergence of the undifferentiated graphs gives convergence after
applying the actual physical operator. No differentiated-limit hypothesis is
needed in `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem tendsto_physicalOperator_local_pairing {O : Set (Euclidean n)} (hO : IsOpen O)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ j i l, ContDiffOn ℝ ∞ (fun x ↦ A x j i l) O)
    (hB : ∀ i l, ContDiffOn ℝ ∞ (fun x ↦ B x i l) O)
    {f : ℕ → Euclidean n → Fin r → ℂ} (hf : ∀ k, ContDiffOn ℝ ∞ (f k) O)
    (F : 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ (ψ : 𝓢(Euclidean n, ℂ)), HasCompactSupport ψ → tsupport ψ ⊆ O →
      ∀ l, Tendsto (fun k ↦ ∫ x, ψ x * f k x l) atTop (𝓝 (F ψ l)))
    (φ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O)
    (i : Fin r) :
    Tendsto (fun k ↦ ∫ x, φ x * physicalOperator A B (f k) x i) atTop
      (𝓝 (graphPhysicalDistributionPairing hO A B hA hB F φ hK hs i)) := by
  simp_rw [physicalOperator_local_pairing hO A B hA hB (hf _) φ hK hs i]
  unfold graphPhysicalDistributionPairing
  apply Tendsto.sub
  · apply tendsto_const_nhds.mul
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro l _
    let ψ := graphCoefficientTest hO φ hK hs (fun x ↦ A x j i l) (hA j i l)
    have hψK : HasCompactSupport ψ := hK.mul_right
    have hψO : tsupport ψ ⊆ O := tsupport_mul_subset_left.trans hs
    have hd := SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.single j (1 : ℝ)) ψ
    exact hF _ (hψK.of_isClosed_subset (isClosed_tsupport _) hd) (hd.trans hψO) l
  · apply tendsto_const_nhds.mul
    apply tendsto_finsetSum
    intro l _
    let ψ := graphCoefficientTest hO φ hK hs (fun x ↦ B x i l) (hB i l)
    have hψK : HasCompactSupport ψ := hK.mul_right
    have hψO : tsupport ψ ⊆ O := tsupport_mul_subset_left.trans hs
    exact hF ψ hψK hψO l

/-- Local smoothness gives continuity of each physical output component; this
supplies remainder pairing integrability in the weak direct graph identity
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem continuousOn_physicalOperator_component {O : Set (Euclidean n)} (hO : IsOpen O)
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ j i l, ContinuousOn (fun x ↦ A x j i l) O)
    (hB : ∀ i l, ContinuousOn (fun x ↦ B x i l) O)
    {f : Euclidean n → Fin r → ℂ} (hf : ContDiffOn ℝ ∞ f O) (i : Fin r) :
    ContinuousOn (fun x ↦ physicalOperator A B f x i) O := by
  have hd (j l) : ContinuousOn (fun x ↦ partialDeriv f x j l) O := by
    intro x hx
    exact ((continuous_apply l).continuousAt.comp
      (((hf.contDiffAt (hO.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
        continuousAt_const)).continuousWithinAt
  simp only [physicalOperator, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]
  apply continuousOn_const.mul
  apply ContinuousOn.add
  · apply continuousOn_finsetSum
    intro j _
    exact continuousOn_finsetSum _ fun l _ ↦ (hA j i l).mul (hd j l)
  · exact continuousOn_finsetSum _ fun l _ ↦ (hB i l).mul
      (continuous_apply l |>.comp_continuousOn hf.continuousOn)

end JanetCartan.FourierIntegral
