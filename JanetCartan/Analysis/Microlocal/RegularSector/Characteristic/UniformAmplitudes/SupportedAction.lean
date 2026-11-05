module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.Buffered
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.CollaredAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.ExtensionGerms

/-!
# Physical identification of the supported correction residual

The third matrix estimated by the uniform amplitude constructor is the literal
physical derivative of its second matrix on the auxiliary time plateau. Both
source time and initial covector are frozen. Outside the transported box the
proof uses zero germs, so it retains every support shoulder. The full zeroth
order coefficient and the correction's factor `i` are unchanged.

Consumer: the retarded residual amplitude in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open AmplitudeBounds ConicAmplitude ResidualCoordinates
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- The quantitative collar is the exact supported continuation used by
`ResidualCoordinates`, with its literal frequency mask. This identifies the
objects needed by the smooth supported phase producer (`two-term-null-identity`). -/
theorem collared_eq_supportedConicMatrix (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (angular : Euclidean d → ℝ) {n : ℕ}
    (f : T → Matrix (Fin n) (Fin n) ℂ) :
    collared ℓ o angular f = supportedConicMatrix ℓ o (FiniteMasks.conicMask angular) f := by
  funext q
  ext k j
  simp only [collared, supportedConicMatrix, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The actual collared matrix has its full closed support in the conic
continuation of the same transported box, including all shoulders. Source:
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem tsupport_collared_subset_domain (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (angular : Euclidean d → ℝ) (ha : ∀ η ∈ tsupport angular, 0 < ℓ η)
    {n : ℕ} (f : T → Matrix (Fin n) (Fin n) ℂ) {V : Set T} (hf : tsupport f ⊆ V) :
    tsupport (collared ℓ o angular f) ⊆ ConicPhase.domain ℓ V := by
  rw [collared_eq_supportedConicMatrix]
  apply tsupport_supportedConicMatrix_subset ℓ o _ _ f hf
  exact FiniteMasks.conicMask_tsupport_subset_cone angular ha
    (fun η hη t ht ↦ by
      change 0 < ℓ (t • η)
      simpa only [map_smul, smul_eq_mul] using mul_pos ht hη)

private theorem correctionColumn_smooth_of_matrix
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T)
    (r c : Fin (d + 1)) (σ : Z → ℝ) {U : Set T}
    (hf : ContDiffOn ℝ ∞ (pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ) U)
    (j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) U := by
  apply contDiffOn_pi.mpr
  intro k
  have hg := Complex.imCLM.contDiff.comp_contDiffOn
    ((Matrix.entryLinearMap ℝ ℂ k j).toContinuousLinearMap.contDiff.comp_contDiffOn hf)
  change ContDiffOn ℝ ∞ (fun p ↦
    (pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ p k j).im) U at hg
  simpa [pencilCorrectionComplexMatrix, complexColumnMatrix, Matrix.smul_apply,
    smul_eq_mul] using hg

/-- The buffered local residual, continued with order minus one, is exactly
the physical operator applied to the buffered conic correction on the time
plateau. Its hypotheses are the support/smoothness outputs already proved by
`buffered_pencilAmplitudeFamily_of_uniform_outputs`, not an assumed residual
identity. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem collared_buffered_correction_residual_eq_physicalApply
    (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ)
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T)
    (r c : Fin (d + 1)) (σ : Z → ℝ) (κ : ℝ → ℝ)
    {V U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hVU : V ⊆ U)
    (hf : ContDiffOn ℝ ∞ (pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ) U)
    (hF : ContDiff ℝ ∞ (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ 1)))
    (hs₁ : tsupport (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ 1)) ⊆ V)
    (hs₂ : tsupport (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ 2)) ⊆ V)
    (q : T) (hκ : κ =ᶠ[𝓝 q.1] (fun _ ↦ 1)) (j : Fin (d + 1)) :
    (fun k ↦ collared ℓ 1 angular
      (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ 2)) q k j) =
      WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (fun y k ↦ collared ℓ 1 angular
          (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ 1))
            (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 y) k j)
        ((coordinateSplit i).symm (q.1, q.2.2.1)) := by
  let e := coordinateSplit i
  let p := ConicPhase.normalize ℓ q
  let x := e.symm (q.1, q.2.2.1)
  let sl := physicalSlice e q.2.1 ((ℓ q.2.2.2)⁻¹ • q.2.2.2)
  let f₁ := pencilAmplitudeFamily i Q B h Φ C r c σ 1
  let f₂ := pencilAmplitudeFamily i Q B h Φ C r c σ 2
  let F₁ := bufferedMatrix V κ f₁
  let F₂ := bufferedMatrix V κ f₂
  let col := fun z : T ↦ fun k ↦ F₁ z k j
  have hsl : sl x = p := physicalSlice_at e p
  have hslc : ContinuousAt sl x := (contDiff_physicalSlice e _ _).continuous.continuousAt
  have hc : ContDiff ℝ ∞ col := contDiff_pi.mpr fun k ↦
    (Matrix.entryLinearMap ℝ ℂ k j).toContinuousLinearMap.contDiff.comp hF
  have hd : DifferentiableAt ℝ (col ∘ sl) x :=
    (hc.comp (contDiff_physicalSlice e _ _)).differentiable (by simp) x
  have ha := firstOrderApply_collared_slice ℓ 1 angular e Q B col q.2.1 q.2.2.2 x hd
  change _ = WKB.firstOrderApply _ _ (collared ℓ 1 angular col ∘ physicalSlice e q.2.1 q.2.2.2) x
  rw [ha]
  change (FiniteMasks.conicMask angular q.2.2.2 : ℂ) •
      ((ℓ q.2.2.2)⁻¹ ^ 1 • (fun k ↦ F₂ p k j)) = _
  congr 2
  by_cases hpV : p ∈ V
  · have hg (f : T → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
        bufferedMatrix V κ f =ᶠ[𝓝 p] f := by
      filter_upwards [hV.mem_nhds hpV, hκ.comp_tendsto
        (continuous_fst.continuousAt : ContinuousAt (fun z : T ↦ z.1) p)] with z hz hk
      change κ z.1 = 1 at hk
      simp [bufferedMatrix, bufferedAmplitude, curryCharacteristicMatrix, hz, hk]
    have he : (col ∘ sl) =ᶠ[𝓝 x] fun y k ↦ f₁ (sl y) k j := by
      have ht : Tendsto sl (𝓝 x) (𝓝 p) := hsl ▸ hslc
      filter_upwards [(hg f₁).comp_tendsto ht] with y hy
      exact congrArg (fun M ↦ fun k ↦ M k j) hy
    have hP : WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (col ∘ sl) x = WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ f₁ (sl y) k j) x := by
      simp only [WKB.firstOrderApply, partialDeriv, he.fderiv_eq, he.eq_of_nhds]
    rw [hP]
    have hu := ((correctionColumn_smooth_of_matrix i Q B h Φ C r c σ hf j).contDiffAt
      (hU.mem_nhds (hVU hpV))).differentiableAt (by simp)
    have hid := pencilCorrectionResidualComplexMatrix_column_eq_physicalApply
      i Q B h Φ C r c σ j p hu
    change (fun k ↦ bufferedMatrix V κ f₂ p k j) = _
    rw [(hg f₂).eq_of_nhds]
    exact hid
  · have hn₁ : p ∉ tsupport F₁ := fun hm ↦ hpV (hs₁ hm)
    have hn₂ : p ∉ tsupport F₂ := fun hm ↦ hpV (hs₂ hm)
    have hz : (col ∘ sl) =ᶠ[𝓝 x] 0 := by
      have ht : Tendsto sl (𝓝 x) (𝓝 p) := hsl ▸ hslc
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hn₁).comp_tendsto ht] with y hy
      ext k
      change F₁ (sl y) k j = 0
      simp only [Function.comp_apply, Pi.zero_apply] at hy
      rw [hy]; rfl
    have hP : WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (col ∘ sl) x = WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          0 x := by
      simp only [WKB.firstOrderApply, partialDeriv, hz.fderiv_eq, hz.eq_of_nhds]
    rw [hP, image_eq_zero_of_notMem_tsupport hn₂]
    simp [WKB.firstOrderApply, partialDeriv, complexPencilCoefficient, complexPencilZeroth]
    rfl

/-- Outside the closed support of a joint amplitude every physical slice
has zero first-order action, including the zeroth-order coefficient. This
is used to transfer the supported phase germ to the literal `PW₁` term on
the measurement plateau (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_physicalSlice_eq_zero_of_notMem_tsupport
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (F : T → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (q : T) (hq : q ∉ tsupport F) (j : Fin (d + 1)) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun y k ↦ F (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 y) k j)
      ((coordinateSplit i).symm (q.1, q.2.2.1)) = 0 := by
  let x := (coordinateSplit i).symm (q.1, q.2.2.1)
  let sl := physicalSlice (coordinateSplit i) q.2.1 q.2.2.2
  have hsl : sl x = q := physicalSlice_at (coordinateSplit i) q
  have ht : Tendsto sl (𝓝 x) (𝓝 q) := hsl ▸
    (contDiff_physicalSlice (coordinateSplit i) q.2.1 q.2.2.2).continuous.continuousAt
  have hz : (fun y k ↦ F (sl y) k j) =ᶠ[𝓝 x] (0 : E → Fin (d + 1) → ℂ) := by
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hq).comp_tendsto ht] with y hy
    ext k
    change F (sl y) k j = 0
    change F (sl y) = 0 at hy
    exact congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ ↦ M k j) hy
  change WKB.firstOrderApply _ _ (fun y k ↦ F (sl y) k j) x = 0
  simp only [WKB.firstOrderApply, partialDeriv, hz.fderiv_eq, hz.eq_of_nhds]
  ext k
  simp [complexPencilCoefficient, complexPencilZeroth]

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
