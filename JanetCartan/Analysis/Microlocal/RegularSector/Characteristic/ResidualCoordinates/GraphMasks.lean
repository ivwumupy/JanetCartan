module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.GraphIdentification
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# Removing the auxiliary masks on the original physical kernel

The original physical output mask and angular multiplier put every elapsed
point inside the SAME closed transport buffer. On this carrier the auxiliary
time and frequency cutoffs are one, so both the solver and `P W₁` have the
literal original amplitudes. Equality of physical germs retains every
cutoff derivative; it is not a pointwise replacement under differentiation.
Consumer: `completeResidual_of_selected_physical_chart`.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- On the output-time plateau and the ORIGINAL right multiplier carrier,
removing the buffered zero extension preserves the full physical germ.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem supportedConicMatrix_slice_eq_of_masks
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (ρ : Euclidean d → ℝ)
    {V : Set T} (hV : IsOpen V) (κ : ℝ → ℝ) (W : TwoTimeAmplitude d (d + 1))
    (s : ℝ) (η : Euclidean d) {x : E}
    (hp : ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η))) ∈ V)
    (hκ : κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1) (hρ : ρ η = 1) :
    let F := fun p : T ↦ bufferedAmplitude V κ W p.1 p.2.1 p.2.2.1 p.2.2.2
    let f := fun p : T ↦ W p.1 p.2.1 p.2.2.1 p.2.2.2
    (fun y ↦ curryCharacteristicMatrix (supportedConicMatrix ℓ o ρ F)
      (y 0) s (spatialPart y) η) =ᶠ[𝓝 x]
    fun y ↦ curryCharacteristicMatrix (ConicAmplitude.extend ℓ o f)
      (y 0) s (spatialPart y) η := by
  have hsl : ContinuousAt (fun y : E ↦ (y 0, (s, (spatialPart y, (ℓ η)⁻¹ • η)))) x :=
    (contDiff_physicalSlice (coordinateSplit (0 : Fin (d + 1))) s ((ℓ η)⁻¹ • η)).continuous.continuousAt
  have hn := hsl.preimage_mem_nhds (hV.mem_nhds hp)
  have ht := hκ.comp_tendsto (EuclideanSpace.proj (0 : Fin (d + 1))).continuous.continuousAt
  filter_upwards [hn, ht] with y hy hκy
  change κ (y 0) = 1 at hκy
  change (y 0, (s, (spatialPart y, (ℓ η)⁻¹ • η))) ∈ V at hy
  simp only [curryCharacteristicMatrix, supportedConicMatrix, ConicAmplitude.extend,
    ConicPhase.normalize, bufferedAmplitude, indicator_of_mem hy, hρ,
    one_smul, hκy, Complex.ofReal_one]

/-- The original closed buffer and physical/angular masks imply exactly the
elapsed chart containment used to remove the auxiliary extensions. The
closed buffer is exported by `exists_buffered_physical_pencil_kernel`.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem normalized_elapsed_mem_transport_buffer
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)} {ε : ℝ} (hε : 0 < ε)
    {V : Set T} (hbuffer : Metric.closedBall (z.1, z) (2 * ε) ⊆ V)
    (χout β : E → ℂ) (hout : tsupport χout ⊆ elapsedPhysicalBox z ε)
    (hβ : ∀ ξ, β ξ ≠ 0 → spatialPart ξ ∈ ConicPhase.angularCone ℓ z.2.2 ε)
    {r : ℝ} (hr : r ∈ Icc 0 ε) {x ξ : E} (hx : x ∈ tsupport χout) (hξ : β ξ ≠ 0) :
    ConicPhase.normalize ℓ (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ V :=
  hbuffer (ConicPhase.elapsed_mem_domain_closedBuffer ℓ hε hr (hout hx) (hβ ξ hξ)).2

/-- Both literal masked elapsed amplitudes are preserved, including the
full differentiated correction. `hchart` is supplied by
`normalized_elapsed_mem_transport_buffer` on the same geometric witnesses.
The two physical masks and the original multiplier appear on BOTH sides.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem elapsedDirectAmplitude_eq_of_auxiliary_masks
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    {V : Set T} (hV : IsOpen V) (κ : ℝ → ℝ)
    (A : E → Fin (d + 1) → Mat) (B : E → Mat) (W₀ W₁ : TwoTimeAmplitude d (d + 1))
    (χout χsource β : E → ℂ) (r : ℝ)
    (hchart : ∀ x ∈ tsupport χout, ∀ ξ, β ξ ≠ 0 →
      ConicPhase.normalize ℓ (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))) ∈ V)
    (hκ : ∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1)
    (hρ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1) (k : Bool) :
    let F₀ := fun p : T ↦ bufferedAmplitude V κ W₀ p.1 p.2.1 p.2.2.1 p.2.2.2
    let F₁ := fun p : T ↦ bufferedAmplitude V κ W₁ p.1 p.2.1 p.2.2.1 p.2.2.2
    let f₀ := fun p : T ↦ W₀ p.1 p.2.1 p.2.2.1 p.2.2.2
    let f₁ := fun p : T ↦ W₁ p.1 p.2.1 p.2.2.1 p.2.2.2
    elapsedAmplitude (directRetardedAmplitudes A B
      (curryCharacteristicMatrix (supportedConicMatrix ℓ 0 ρ F₀))
      (curryCharacteristicMatrix (supportedConicMatrix ℓ 1 ρ F₁)) k) χout χsource β r =
    elapsedAmplitude (directRetardedAmplitudes A B
      (curryCharacteristicMatrix (ConicAmplitude.extend ℓ 0 f₀))
      (curryCharacteristicMatrix (ConicAmplitude.extend ℓ 1 f₁)) k) χout χsource β r := by
  dsimp only
  funext x z ξ
  by_cases hx : χout x = 0
  · simp [elapsedAmplitude, hx]
  by_cases hξ : β ξ = 0
  · simp [elapsedAmplitude, hξ]
  have hp := hchart x (subset_tsupport χout hx) ξ hξ
  have h₀ := supportedConicMatrix_slice_eq_of_masks ℓ 0 ρ hV κ W₀ (x 0 - r)
    (spatialPart ξ) hp (hκ x (subset_tsupport χout hx)) (hρ ξ hξ)
  have h₁ := supportedConicMatrix_slice_eq_of_masks ℓ 1 ρ hV κ W₁ (x 0 - r)
    (spatialPart ξ) hp (hκ x (subset_tsupport χout hx)) (hρ ξ hξ)
  cases k
  · simp only [directRetardedAmplitudes, elapsedAmplitude, Pi.add_apply,
      h₀.eq_of_nhds, h₁.eq_of_nhds]
  · have hd := twoTimePhysicalApply_eq_of_scaled_germ A B _ _ 1 (x 0 - r) (spatialPart ξ) x
      (by simpa only [one_smul] using h₁)
    simp only [one_smul] at hd
    simp only [directRetardedAmplitudes, elapsedAmplitude, hd]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
