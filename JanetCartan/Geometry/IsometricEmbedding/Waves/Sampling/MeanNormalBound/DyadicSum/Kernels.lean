module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.DyadicSum.Amplitudes
public import JanetCartan.Analysis.Microlocal.NormalComparison.OperatorBounds

/-!
# The literal kernel of the finite dyadic normal sum

The identification needed after `app:ch_waves:eq:sampling-operator-bounds`.
Finite sums commute with both integrals by absolute integrability, using the
compact-frequency kernel estimates on every L² input. Both physical positions
and the exact frequency normalization of every band are retained.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.Sampling.MeanNormalBound
open NormalComparison AmplitudeBound RawInputPartition

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- A finite dyadic family has a common compact frequency carrier. Its radius
may grow with the ceiling; it contributes no constant to the amplitude bound
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_dyadic_frequency_support_radius
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (J : ℕ) :
    ∃ ρ > 0, ∀ (F : Fin J → UniformNormalData G C) (ε : Fin J → ℝ),
      (∀ j, ε j ∈ Icc 0 G.ε₀) → ∀ j ξ, ξ ∉ Metric.closedBall 0 ρ → ∀ z,
        unitFrequencyAmplitude (dyadicScale j.val)
          ((F j).pairedInverseAmplitude (ε j)) ξ z = 0 := by
  obtain ⟨β, hβ, hb⟩ := exists_unitFrequencyAmplitude_frequency_upper G C
  refine ⟨β * dyadicScale J, mul_pos hβ (dyadicScale_pos J), ?_⟩
  intro F ε hε j ξ hξ z
  by_contra hn
  have hbound := hb (F j) (ε j) (hε j) _ (dyadicScale_pos j.val) ξ z hn
  have hscale := dyadicScale_strictMono.monotone j.isLt.le
  apply hξ
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hbound.trans (mul_le_mul_of_nonneg_left hscale hβ.le)

private theorem normal_ae_unitFrequency (F : UniformNormalData G C)
    {ε K : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (hK : 0 < K)
    (f : NormalOutputL2 n r) (i : Fin r) :
    (((F.uniformOscillatoryOperator K ε).comp
      (F.uniformOscillatoryOperator K ε).adjoint) f) i =ᵐ[volume]
      fun x ↦ ∑ a, ∫ y,
        (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ
            (pairedPosition x y) i a) * f a y := by
  let g : Lp ℂ ∞ (volume.restrict G.D) :=
    boundedSymbol (fun _ ↦ 1) aestronglyMeasurable_const 1 (by simp)
  have hg : g =ᵐ[volume.restrict G.D] fun _ ↦ (1 : ℂ) :=
    boundedSymbol_coeFn _ _ _ _
  have hm : multiplicationOperator g = ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (volume.restrict G.D)) := by
    ext v
    filter_upwards [multiplicationOperator_coeFn g v, hg] with u hu hgu
    simpa [hgu] using hu
  have hker := F.uniformOscillatoryNormalOperator_ae_maskedNormalKernel hK.le hε
    (m := fun _ ↦ (1 : ℝ)) continuousOn_const g
    (by simpa only [Complex.ofReal_one] using hg) f i
  rw [UniformNormalData.uniformOscillatoryNormalOperator, hm,
    ContinuousLinearMap.id_comp] at hker
  refine hker.trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro a _
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    rw [F.maskFreeNormalKernel_apply_unitFrequency hε hK]

/-- The sum of actual Hilbert-adjoint normals has exactly the kernel of the
summed full amplitude. Absolute convergence of the frequency and physical
integrals is discharged from the primitive inputs, for every L² vector
(`app:ch_osc:eq:osc-exact-normal-kernel`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem sum_dyadicOscillatoryNormalOperator_ae_kernel
    {J : ℕ} (F : Fin J → UniformNormalData G C) (ε : Fin J → ℝ)
    (hε : ∀ j, ε j ∈ Icc 0 G.ε₀) (f : NormalOutputL2 n r) (i : Fin r) :
    ((∑ j, ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).comp
      ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).adjoint) f) i
        =ᵐ[volume] fun x ↦ ∑ a, ∫ y,
          (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
            dyadicNormalAmplitude F ε ξ (pairedPosition x y) i a) * f a y := by
  classical
  let b := fun j : Fin J ↦
    unitFrequencyAmplitude (dyadicScale j.val) ((F j).pairedInverseAmplitude (ε j))
  let N := fun j : Fin J ↦ ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).comp
    ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).adjoint
  obtain ⟨R, _, A, _, hb⟩ := G.exists_unitFrequencyAmplitude_bounds C
  obtain ⟨ρ, _, hρ⟩ := exists_dyadic_frequency_support_radius G C J
  have hbs (j : Fin J) : MatrixNormalAmplitudeBounds (b j) R A :=
    hb (F j) (ε j) (hε j) _
  have hs (j : Fin J) (a : Fin r) (ξ : Euclidean n)
      (hξ : ξ ∉ Metric.closedBall 0 ρ) (z) : b j ξ z i a = 0 :=
    congrArg (fun M ↦ M i a) (hρ F ε hε j ξ hξ z)
  have hm (j : Fin J) (a : Fin r) :
      StronglyMeasurable (Function.uncurry (fun ξ z ↦ b j ξ z i a)) :=
    (matrixEntryEvaluation i a).continuous.comp_stronglyMeasurable (hbs j).measurable
  have hz (j : Fin J) (a : Fin r) (ξ) (z) : ‖b j ξ z i a‖ ≤ A :=
    (norm_matrixEntry_le_frobenius _ i a).trans ((hbs j).derivative ξ [] (by simp) z)
  have hc (j : Fin J) (a : Fin r) :
      Continuous (Function.uncurry (fun ξ z ↦ b j ξ z i a)) :=
    (matrixEntryEvaluation i a).continuous.comp
      (contDiff_unitFrequencyAmplitude _ ((F j).pairedInverseAmplitude_contDiff (hε j))).continuous
  have hfreq (j : Fin J) (a : Fin r) (x y : Euclidean n) :
      Integrable (fun ξ ↦ Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b j ξ (pairedPosition x y) i a) :=
    integrable_compactFrequencyAmplitude_frequency (fun ξ z ↦ b j ξ z i a)
      (hs j a) (hc j a) x y
  have haction (j : Fin J) (a : Fin r) (x : Euclidean n) :
      Integrable (fun y ↦ (∫ ξ,
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          b j ξ (pairedPosition x y) i a) * f a y) :=
    integrable_compactFrequencyAmplitude_action (fun ξ z ↦ b j ξ z i a)
      (hm j a) (fun ξ ↦ (hbs j).support ξ i a) (hz j a) (hs j a) (f a) x
  have hsum : ((∑ j, N j) f) i = ∑ j, (N j f) i := by
    rw [sum_apply]
    exact map_sum (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : Fin r ↦ Lp ℂ 2 (volume : Measure (Euclidean n))) i)
      (fun j ↦ N j f) Finset.univ
  change ((∑ j, N j) f) i =ᵐ[volume] _
  rw [hsum]
  have hall : ∀ᵐ x ∂volume, ∀ j : Fin J, (N j f) i x =
      ∑ a, ∫ y, (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b j ξ (pairedPosition x y) i a) * f a y :=
    ae_all_iff.mpr (fun j ↦ normal_ae_unitFrequency (F j) (hε j)
      (dyadicScale_pos j.val) f i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ (N j f) i), hall]
    with x hx hN
  rw [hx]
  simp_rw [hN]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← integral_finsetSum _ (fun j _ ↦ haction j a x)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [← Finset.sum_mul]
  congr 1
  rw [← integral_finsetSum _ (fun j _ ↦ hfreq j a x y)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ ↦ by
    simp only [dyadicNormalAmplitude, Matrix.sum_apply, Finset.mul_sum, b]

end JanetCartan.Sampling.MeanNormalBound
