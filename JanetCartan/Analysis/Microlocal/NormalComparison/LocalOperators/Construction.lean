module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Regularity

/-!
# Actual operators from the uniform local data

The entire input L² construction in `app:ch_osc:prop:osc-normal`, with the
manuscript normalization and full physical-space vector output. The family is
defined on all real parameters, by zero outside the closed admissible interval,
so that its derivative within that interval can be stated at either endpoint.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The actual `T_ε^K` of `app:ch_osc:prop:osc-normal`, on the entire scalar
input L² space. Its arbitrary zero values outside the closed parameter interval
allow endpoint derivatives to be expressed with `HasDerivWithinAt`. -/
def UniformNormalData.uniformOscillatoryOperator (F : UniformNormalData G C)
    (K ε : ℝ) : Lp ℂ 2 (volume.restrict G.D) →L[ℂ] NormalOutputL2 n r :=
  if hε : ε ∈ Icc 0 G.ε₀ then
    compactVectorKernelOperator G.D
      (fun i ↦ (F.normalizedKernel_contDiff hε (normalOperatorScale n K) K i).continuous)
      (F.normalizedKernel_hasCompactSupport hε (normalOperatorScale n K) K)
  else 0

/-- On the manuscript interval the operator is constructed from the original
kernel, with no phase extension (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.uniformOscillatoryOperator_of_mem
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    F.uniformOscillatoryOperator K ε =
      compactVectorKernelOperator G.D
        (fun i ↦ (F.normalizedKernel_contDiff hε (normalOperatorScale n K) K i).continuous)
        (F.normalizedKernel_hasCompactSupport hε (normalOperatorScale n K) K) :=
  dite_eq_left hε

/-- The literal input integral in `app:ch_osc:prop:osc-normal` for every L²
input, with the normalization `(K/(2π))^(n/2)`. -/
theorem UniformNormalData.uniformOscillatoryOperator_ae_integral
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (f : Lp ℂ 2 (volume.restrict G.D)) (i : Fin r) :
    (F.uniformOscillatoryOperator K ε f) i =ᵐ[volume]
      fun x ↦ ∫ u in G.D, (normalOperatorScale n K : ℂ) *
        oscillatoryFactor K (F.phase ε x u) * F.amplitude ε x u i * f u := by
  rw [F.uniformOscillatoryOperator_of_mem K hε]
  exact compactVectorKernelOperator_ae_integral G.D _ _ f i

/-- The actual Hilbert adjoint of the constructed operator has the conjugate
kernel from `app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem UniformNormalData.uniformOscillatoryOperator_adjoint_ae_integral
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (f : NormalOutputL2 n r) :
    (F.uniformOscillatoryOperator K ε).adjoint f =ᵐ[volume.restrict G.D]
      fun u ↦ ∑ i, ∫ x, star ((normalOperatorScale n K : ℂ) *
        oscillatoryFactor K (F.phase ε x u) * F.amplitude ε x u i) * f i x := by
  rw [F.uniformOscillatoryOperator_of_mem K hε]
  exact compactVectorKernelOperator_adjoint_ae_integral G.D _ _ f

/-- The actual masked normal family `T_ε^K m (T_ε^K)*` of
`app:ch_osc:prop:osc-normal`, using the Hilbert adjoint. -/
def UniformNormalData.uniformOscillatoryNormalOperator (F : UniformNormalData G C)
    (K : ℝ) (g : Lp ℂ ∞ (volume.restrict G.D)) (ε : ℝ) :
    NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r :=
  (F.uniformOscillatoryOperator K ε).comp
    ((multiplicationOperator g).comp (F.uniformOscillatoryOperator K ε).adjoint)

/-- Full masked normal kernel with both physical positions retained and the
exact squared normalization (`app:ch_osc:eq:osc-exact-normal-kernel`). The mask
is any fixed L∞ representative, independent of the parameter. -/
theorem UniformNormalData.uniformOscillatoryNormalOperator_ae_integral
    (F : UniformNormalData G C) {K : ℝ} (hK : 0 ≤ K)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (g : Lp ℂ ∞ (volume.restrict G.D)) (f : NormalOutputL2 n r) (i : Fin r) :
    (F.uniformOscillatoryNormalOperator K g ε f) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (((K / (2 * Real.pi)) ^ n : ℝ) : ℂ) *
        (∫ u in G.D, oscillatoryFactor K (F.phase ε x u - F.phase ε y u) *
          (F.amplitude ε x u i * star (F.amplitude ε y u j)) * g u) * f j y := by
  unfold uniformOscillatoryNormalOperator
  rw [F.uniformOscillatoryOperator_of_mem K hε]
  have he := compactVectorKernelOperator_cross_ae_integral G.D
    (fun i ↦ (F.normalizedKernel_contDiff hε (normalOperatorScale n K) K i).continuous)
    (F.normalizedKernel_hasCompactSupport hε (normalOperatorScale n K) K)
    (fun j ↦ (F.normalizedKernel_contDiff hε (normalOperatorScale n K) K j).continuous)
    (F.normalizedKernel_hasCompactSupport hε (normalOperatorScale n K) K) g f i
  refine he.trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [← integral_const_mul]
  congr 2
  funext u
  rw [normalizedOscillatoryKernel_mul_star, normalOperatorScale_sq n hK]
  ring

end JanetCartan.NormalComparison
