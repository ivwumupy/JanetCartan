module

public import JanetCartan.Iteration.PhysicalSampling.ParameterCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Family

/-!
# The global scalar extension has the same original sampling realization

The fixed carrier cutoff is one on the support of the original incidence and
spectator weight. Every sampled and continuum grouped-prefix normal, and hence
every realized deviation, is therefore literally unchanged. This includes zero
weights without dividing by them (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalSampling

open SamplingKernelBounds Sampling Sampling.Realization RawInputPartition SeparatedSampling

variable {n J p : ℕ}

/-- Apply the same fixed carrier extension to every original band and color. -/
def scalarCarrierCutKernel
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1) :
    BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n :=
  parameterCutKernel D (fun q ↦ β q.2.2)
    (hβ.comp (continuous_snd.comp continuous_snd)) (fun q ↦ hβone q.2.2)

/-- No squared-kernel or Bernstein failure-budget inflation is introduced. -/
theorem scalarCarrierCutKernel_squaredKernelConstant
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1) :
    (scalarCarrierCutKernel D β hβ hβone).squaredKernelConstant = D.squaredKernelConstant := rfl

/-- The locally constructed actual scalar shell bound becomes an all-label
bound without enlarging its constant. The local producer is
`exists_retainedScalar_sharp_bound`; the nonzero-cutoff geometry is supplied by
the retained full cutoff and `scalar_parameter_cube_of_graph_support`. -/
theorem scalarCarrierCutKernel_sharp
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ (i : RefinedIndex J) c z, β z ≠ 0 →
      ‖D.operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C * refinedRadius i)
    (i : RefinedIndex J) (c : Fin 3 → Fin (p + 1)) (z : Point) :
    ‖(scalarCarrierCutKernel D β hβ hβone).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤
      C * refinedRadius i := by
  apply parameterCutKernel_operator_sq_le
  · exact mul_nonneg hC (by unfold refinedRadius; positivity)
  · exact hlocal i c z

/-- Literal equality of the weighted grouped prefix normal at every label. -/
theorem scalarCarrierCutKernel_weighted_prefix_normal
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1)
    (L : ℕ) (c : Fin 3 → Fin (p + 1)) (z : Point) (w : ℝ)
    (hplateau : w ≠ 0 → β z = 1) :
    w • atomNormal (refinedKernelPrefix (scalarCarrierCutKernel D β hβ hβone) L (c, z)) =
      w • atomNormal (refinedKernelPrefix D L (c, z)) := by
  by_cases hw : w = 0
  · simp only [hw, zero_smul]
  · have heq : refinedKernelPrefix (scalarCarrierCutKernel D β hβ hβone) L (c, z) =
        (β z : ℂ) • refinedKernelPrefix D L (c, z) :=
      parameterCutKernel_refinedKernelPrefix D (fun q ↦ β q.2)
        (hβ.comp continuous_snd) (fun q ↦ hβone q.2) L (c, z)
    rw [heq, hplateau hw, Complex.ofReal_one, one_smul]

/-- The scalar continuum mean is the mean of the SAME original physical row,
not a new scalar weighted measure. -/
theorem scalarCarrierCutKernel_patchMeanNormal
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1)
    (ψ : Point → ℝ) (hplateau : ∀ z, ψ z ≠ 0 → β z = 1)
    (B h : ℝ) (w : ℝ → ℝ) (L : ℕ) :
    patchMeanNormal p B ψ w h
      (fun c z ↦ refinedKernelPrefix (scalarCarrierCutKernel D β hβ hβone) L (c, z)) =
    patchMeanNormal p B ψ w h (fun c z ↦ refinedKernelPrefix D L (c, z)) := by
  unfold patchMeanNormal
  apply Finset.sum_congr rfl
  intro q _
  apply integral_congr_ae
  filter_upwards [] with z
  apply scalarCarrierCutKernel_weighted_prefix_normal
  intro hz
  exact hplateau z (mul_ne_zero_iff.mp hz).1

/-- The same original finite samples and weights realize the extended scalar
row, including every zero-mass node. -/
theorem scalarCarrierCutKernel_patchSampleNormal
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : Point → ℝ) (hβ : Continuous β) (hβone : ∀ z, |β z| ≤ 1)
    (ψ : Point → ℝ) (hplateau : ∀ z, ψ z ≠ 0 → β z = 1)
    (B h : ℝ) (w : ℝ → ℝ) (U : Lattice → Point) (L : ℕ) :
    patchSampleNormal p B ψ w h
      (fun c z ↦ refinedKernelPrefix (scalarCarrierCutKernel D β hβ hβone) L (c, z)) U =
    patchSampleNormal p B ψ w h (fun c z ↦ refinedKernelPrefix D L (c, z)) U := by
  unfold patchSampleNormal
  apply Finset.sum_congr rfl
  intro a _
  apply scalarCarrierCutKernel_weighted_prefix_normal
  intro ha
  exact hplateau _ (weight_ne_zero_factors ha).1

/-- All prefixes of a finite original family have exactly the same deviation;
the common measured/scalar event therefore uses one and the same realization. -/
theorem scalarCarrierCutKernel_familyDeviation {A : Type*} [Fintype A]
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (β : A → Point → ℝ) (hβ : ∀ a, Continuous (β a))
    (hβone : ∀ a z, |β a z| ≤ 1)
    (ψ : A → Point → ℝ) (hplateau : ∀ a z, ψ a z ≠ 0 → β a z = 1)
    (B h : ℝ) (w : ℝ → ℝ) (ξ : A → ShiftSpace p B h) (L : ℕ) :
    familyDeviation p B ψ w h
      (fun a c z ↦ refinedKernelPrefix (scalarCarrierCutKernel (D a) (β a) (hβ a) (hβone a)) L (c, z)) ξ =
    familyDeviation p B ψ w h (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ := by
  unfold familyDeviation
  apply Finset.sum_congr rfl
  intro a _
  rw [scalarCarrierCutKernel_patchSampleNormal _ _ _ _ _ (hplateau a),
    scalarCarrierCutKernel_patchMeanNormal _ _ _ _ _ (hplateau a)]

end JanetCartan.PhysicalSampling
