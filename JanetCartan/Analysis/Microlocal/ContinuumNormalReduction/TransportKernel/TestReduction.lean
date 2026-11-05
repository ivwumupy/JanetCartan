module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Limit
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.OperatorReduction

/-!
# Principal reduction of the normal distribution on tests

For `app:ch_background:eq:bg-real-symbol`, identify the full matrix source-tested
amplitude with its completed principal term and its two actual remainders. Then
identify this distribution with the literal uncut adjoint pairing by the proved
finite-carrier limit. No bounded unregularized carrier is assumed.

The distributional convergence premise below concerns only the ORIGINAL full
amplitude, before diagonal reduction. It is an explicit analytic input allowed
by the normal-kernel task. The normal-reduction consumer must prove it for its
chosen physical source profiles, including their relation to the torus tests.
The outer output pairing stays on torus volume, and the source PDO integrals
stay on Euclidean Lebesgue measure. No equality of these measures is assumed.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

/-- Finite matrix action of the normalized reflected FULL amplitude on
physical source profiles (`app:ch_background:eq:bg-real-symbol`). -/
def reflectedMatrixTestAction
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (f : Fin n → Euclidean n → ℂ) (x : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ ∑ j, fullAmplitudeOperator (fun x y ξ ↦
    (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (f j) x)

/-- The completed principal action plus the ORIGINAL Taylor remainder and
literal diagonal-completion kernel, with every matrix sum and normalization
retained (`app:ch_background:eq:bg-real-symbol`). -/
def principalMatrixTestAction
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (β : Euclidean n → ℝ)
    (f : Fin n → Euclidean n → ℂ) (x : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ ∑ j, (
    fullAmplitudeOperator (unitCompletedPrincipalEntry a J u Ω K i j)
      (fun y ↦ β y • f j y) x +
    fullAmplitudeOperator (diagonalRemainderAmplitude basis (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (f j) x +
    ∫ y, (β y • f j y) * diagonalCompletionErrorKernel a J u Ω K i j x y))

section PrimitiveInputs
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
    {Ω : Set (TransportSymbol.Variables n × Euclidean 2)}
    {W Z : Set (TransportSymbol.InputVariables n)}
    (hΩ : IsOpen Ω) (hreg : TransportSymbol.PrimitiveRegularity a J W)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (TransportSymbol.inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z)
    (hbuffer : closure (F '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hzero : ∀ t : ℝ, t ≤ 1 → a.high t = 0)
    (hone : ∀ t : ℝ, 2 ≤ t → a.high t = 1)
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖)
    {K : Set (Euclidean 2)} (hK : IsCompact K)
    (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (f : Fin n → Euclidean n → ℂ)
    (hf : ∀ j, Continuous (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hβa : ∀ x i j ξ y, reflectedSymbolAmplitude a J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j ≠ 0 → β y = 1)
    (hi : ∀ x i j, Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (f j) x))
    (hid : ∀ x i j, Integrable (sourceAmplitudeTransform (diagonalAmplitude (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (f j) x))
    (hir : ∀ x i j, Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude basis
      (fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (f j) x))
    (hiB : ∀ x i j, Integrable (sourceAmplitudeTransform (fullTaylorCoefficient (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (f j) x))

include hΩ hreg hu hmap hright hs hbuffer hzero hone hCupper hClower hℓ hlow hupper hlower
  hK hβ hf hfc hβa hi hid hir hiB

/-- The finite matrix source-tested principal reduction follows from the actual
primitive smoothness and conic buffers. No matrix kernel identity or remainder
estimate is an input (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedMatrixTestAction_eq_principal (x : Euclidean n) :
    reflectedMatrixTestAction a J u Ω K f x =
      principalMatrixTestAction a J u Ω K basis β f x := by
  apply PiLp.ext
  intro i
  change (∑ j : Fin n, _) = ∑ j : Fin n, _
  apply Finset.sum_congr rfl
  intro j _
  exact fullAmplitudeOperator_principal_reduction_of_primitive_inputs a J u F
    hΩ hreg hu hmap hright hs hbuffer hzero hone hCupper hClower hℓ hlow hupper hlower
    hK i j basis β (f j) x hβ (hβa x i j) (hf j) (hfc j)
    (hi x i j) (hid x i j) (hir x i j) (hiB x i j)

/-- Identify the principal-plus-remainders distribution with the literal uncut
real normal on two output tests. Mask exhaustion and testwise adjoint L²
membership prove the carrier limit; the separately supplied distributional
convergence concerns only the original reflected full amplitude. The principal
decomposition, its finite matrix sums and both remainder kernels are proved,
not assumed (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem realNormal_principal_reduction_of_test_limit
    {d : CarrierData n N} {m : ℕ → CarrierVariable n → ℝ} {Zmask : Set CarrierParameter}
    {R : ℕ → ℝ} {M C : ℝ}
    (hmask : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Zmask (R r) M C)
    (hm : ∀ᵐ z ∂carrierMeasure n, Tendsto (fun r ↦ m r z) atTop (𝓝 1))
    (charts : ∀ r x, x ∈ d.outputChart → ∀ y, y ∈ d.outputChart → ChartInputs d (m r) x y)
    (v w : OutputL2 n)
    (hv : MemLp (carrierAdjointIntegral d (l2ComplexInclusion volume v)) 2 (carrierMeasure n))
    (hw : MemLp (carrierAdjointIntegral d (l2ComplexInclusion volume w)) 2 (carrierMeasure n))
    (hlimit : Tendsto (fun r ↦ 4 * (fullAmplitudeTestPairing (charts r)
        (l2ComplexInclusion volume v) (l2ComplexInclusion volume w)).re) atTop
      (𝓝 ((∫ x : Torus n, inner ℂ (l2ComplexInclusion volume v x)
        (d.outputChart.indicator (fun x ↦
          reflectedMatrixTestAction a J u Ω K f (d.chartPoint x)) x)).re))) :
    4 * (∫ z, inner ℂ
      (carrierAdjointIntegral d (l2ComplexInclusion volume v) z)
      (carrierAdjointIntegral d (l2ComplexInclusion volume w) z) ∂carrierMeasure n).re =
      (∫ x : Torus n, inner ℂ (l2ComplexInclusion volume v x)
        (d.outputChart.indicator (fun x ↦
          principalMatrixTestAction a J u Ω K basis β f (d.chartPoint x)) x)).re := by
  have hnormal := fullAmplitudeTestPairing_tendsto hmask hm charts
    (l2ComplexInclusion volume v) (l2ComplexInclusion volume w) hv hw
  have hreal := ((Complex.continuous_re.tendsto _).comp hnormal).const_mul 4
  have he := (tendsto_nhds_unique hlimit hreal).symm
  have haction : reflectedMatrixTestAction a J u Ω K f =
      principalMatrixTestAction a J u Ω K basis β f := by
    funext x
    exact reflectedMatrixTestAction_eq_principal a J u F hΩ hreg hu hmap hright hs hbuffer
      hzero hone hCupper hClower hℓ hlow hupper hlower hK basis β hβ f hf hfc hβa hi hid hir hiB x
  simpa only [haction] using he

end PrimitiveInputs
end JanetCartan.ContinuumRow.TransportKernel
