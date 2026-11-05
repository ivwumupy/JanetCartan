module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.BandIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ChartGrades
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Restriction

/-!
# Identifying the joint branches with the physical raw band branches

The epsilon and annular variables are frozen only after physical differentiation.
The same construction includes the physical time direction. These identities
connect the literal integral to the original-chart grade producer in the proof
of `app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.SliceBounds

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Physical directions inside the full epsilon/physical/covector chart
(`app:ch_waves:eq:individual-raw-slice`). -/
def rawSlicePhysicalLift : X →L[ℝ] ℝ × X × P :=
  (ContinuousLinearMap.inr ℝ ℝ (X × P)).comp (ContinuousLinearMap.inl ℝ X P)

/-- Lifting a physical unit direction preserves its norm, including time
directions (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_rawSlicePhysicalLift (v : X) : ‖rawSlicePhysicalLift (P := P) v‖ = ‖v‖ := by
  simp [rawSlicePhysicalLift, Prod.norm_def, norm_nonneg]

/-- Freezing epsilon and the Fourier variable gives the exact physical branch
of the SAME joint functions (`app:ch_waves:eq:individual-raw-slice`). -/
theorem sliceDerivativeAmplitude_freeze
    {Q : Set (ℝ × X × P)} (hQ : IsOpen Q)
    {φ : ℝ × X × P → ℝ} {A : ℝ × X × P → F}
    (hφ : ContDiffOn ℝ ∞ φ Q) (hA : ContDiffOn ℝ ∞ A Q)
    (ε : ℝ) (θ : P) {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s)
    {x : X} (hx : (ε, x, θ) ∈ Q) :
    sliceDerivativeAmplitude (fun y ↦ φ (ε, y, θ)) (fun y ↦ A (ε, y, θ)) v b x =
      sliceDerivativeAmplitude φ A (fun i ↦ rawSlicePhysicalLift (P := P) (v i))
        b (ε, x, θ) := by
  have h := sliceDerivativeAmplitude_comp_affine hQ hφ hA
    (rawSlicePhysicalLift (X := X) (P := P)) (ε, (0, θ)) v b
    (x := x) (by simpa [rawSlicePhysicalLift] using hx)
  simpa only [rawSlicePhysicalLift, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

variable {n : ℕ} [FiniteDimensional ℝ X]

/-- The physical branch in the exact integral expansion equals the joint
original-chart branch. The rescaled mask retains its literal half derivative,
original wide band, and parameter `τ*2^j`. This equality is at every physical
point on the original open chart, not merely almost everywhere
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSliceBandDerivativeAmplitude_eq_jointBranch
    {U : Set X} {V Ω : Set (Euclidean (n - 1))}
    {Q : Set (ℝ × X × Euclidean (n - 1))} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    {S : X → Euclidean (n - 1) → ℝ} {A : X → Euclidean (n - 1) → F}
    {χ : X → ℝ} {ζ : Euclidean (n - 1)} {τ : ℝ} (hτ : τ ≠ 0)
    (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U)
    (hm : ContDiffOn ℝ ∞ (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)) Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    {s : ℕ} (v : Fin s → X) (b : SliceDerivativeBranch s)
    {x : X} {θ : Euclidean (n - 1)} (hx : (τ * (2 : ℝ) ^ j, x, θ) ∈ Q) :
    rawSliceBandDerivativeAmplitude S A χ ζ τ β j v b x θ =
      sliceDerivativeAmplitude (rawSlicePhaseExtension S ζ)
        (rawSliceAmplitudeExtension A χ
          (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β ((2 : ℝ) ^ j • η)) ζ)
        (fun i ↦ rawSlicePhysicalLift (v i)) b (τ * (2 : ℝ) ^ j, x, θ) := by
  let ε := τ * (2 : ℝ) ^ j
  let m : Euclidean (n - 1) → ℂ := fun η ↦
    (Real.sqrt ‖η‖ : ℂ) * β ((2 : ℝ) ^ j • η)
  have hφ := contDiffOn_rawSlicePhaseExtension hU hV hQ hW hIW hS hshift
  have hB := contDiffOn_rawSliceAmplitudeExtension hA hχ hm
    (hshift 1 (hIW (by simp))) hθ
  have hpre : IsOpen ((fun y : X ↦ (ε, y, θ)) ⁻¹' Q) := hQ.preimage (by fun_prop)
  have he : (fun y ↦ rawPrimaryPhaseDifference S ζ ε y θ) =ᶠ[𝓝 x]
      (fun y ↦ rawSlicePhaseExtension S ζ (ε, y, θ)) := by
    filter_upwards [hpre.mem_nhds hx] with y hy
    exact (rawSlicePhaseExtension_eq_rawPrimaryPhaseDifference hV hS
      (hshift 0 (hIW (by simp)) hy).1
      (mul_ne_zero hτ (pow_ne_zero _ (by norm_num)))
      (fun t ht ↦ (hshift t (hIW ht) hy).2)).symm
  have ha : (fun y ↦ rawSliceBandAmplitude A χ ζ τ β j y θ) =ᶠ[𝓝 x]
      (fun y ↦ rawSliceAmplitudeExtension A χ m ζ (ε, y, θ)) := by
    filter_upwards [] with y
    simp only [rawSliceBandAmplitude, rawSliceAmplitudeExtension, m, ε, mul_assoc]
  change sliceDerivativeAmplitude _ _ v b x = _
  rw [(eventuallyEq_sliceDerivativeAmplitude he ha v b).eq_of_nhds]
  exact sliceDerivativeAmplitude_freeze hQ hφ hB ε θ v b hx

end JanetCartan.RawPrimary.SliceBounds
