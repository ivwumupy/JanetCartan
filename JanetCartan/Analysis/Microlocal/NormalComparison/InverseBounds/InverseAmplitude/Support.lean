module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.UniformJets

/-!
# Support and buffer of the inverse normal amplitude

The two zero extensions required in Step 1 of `app:ch_osc:prop:osc-normal`.
All statements concern the actual amplitude and its absolute Jacobian.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The physical zero extension in native `(x,(y,v))` coordinates, used by
Step 1 of `app:ch_osc:prop:osc-normal`. -/
def UniformNormalData.extendedInverseAmplitude (F : UniformNormalData G C)
    (ε : ℝ) (z : Euclidean n × (Euclidean n × Euclidean n)) : Matrix (Fin r) (Fin r) ℂ := by
  classical
  exact if z.1 ∈ G.X ∧ z.2.1 ∈ G.X then
    F.maskFreeInverseAmplitude ε z.1 z.2.1 z.2.2 else 0

/-- The physical zero extension agrees with the actual full amplitude on
both physical boxes (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.extendedInverseAmplitude_eq (F : UniformNormalData G C)
    (ε : ℝ) {x y : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X) (v : Euclidean n) :
    F.extendedInverseAmplitude ε (x, (y, v)) = F.maskFreeInverseAmplitude ε x y v := by
  simp [extendedInverseAmplitude, hx, hy]

/-- Either physical position outside the input support kills the complete
matrix amplitude (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.normalAmplitude_eq_zero_of_not_mem_physical
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y : Euclidean n} (hxy : x ∉ G.X₀ ∨ y ∉ G.X₀) (u : Euclidean n) :
    normalAmplitude (F.amplitude ε) x y u = 0 := by
  have ha (z : Euclidean n) (hz : z ∉ G.X₀) : F.amplitude ε z u = 0 := by
    by_contra h
    exact hz (F.amplitude_support ε hε
      (show (z, u) ∈ Function.support (Function.uncurry (F.amplitude ε)) from h)).1
  rcases hxy with hx | hy
  · ext i j
    simp [normalAmplitude, ha x hx]
  · ext i j
    simp [normalAmplitude, ha y hy]

/-- Physical support of the actual inverse amplitude, before extension
(`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y : Euclidean n} (hxy : x ∉ G.X₀ ∨ y ∉ G.X₀) (v : Euclidean n) :
    F.maskFreeInverseAmplitude ε x y v = 0 := by
  classical
  by_cases hv : v ∈ G.V
  · simp [maskFreeInverseAmplitude, hv, inverseJacobianAmplitude,
      F.normalAmplitude_eq_zero_of_not_mem_physical hε hxy]
  · simp [maskFreeInverseAmplitude, hv]

/-- The extension agrees globally at admissible parameters, because the
physical support already lies in the boxes (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.extendedInverseAmplitude_eq_maskFree (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (z : Euclidean n × (Euclidean n × Euclidean n)) :
    F.extendedInverseAmplitude ε z = F.maskFreeInverseAmplitude ε z.1 z.2.1 z.2.2 := by
  by_cases hz : z.1 ∈ G.X ∧ z.2.1 ∈ G.X
  · simp [extendedInverseAmplitude, hz]
  · have h : z.1 ∉ G.X₀ ∨ z.2.1 ∉ G.X₀ := by
      by_contra! h
      exact hz ⟨G.X₀_subset h.1, G.X₀_subset h.2⟩
    simp [extendedInverseAmplitude, hz,
      F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε h]

/-- The image buffer forces vanishing throughout a fixed neighborhood of
every point outside the output chart (`app:ch_osc:prop:osc-normal`, Step 1).
The radius is independent of the family and of both physical positions. -/
theorem UniformNormalData.maskFreeInverseAmplitude_eq_zero_near_chart_compl
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {x y v w : Euclidean n} (hx : x ∈ G.X) (hy : y ∈ G.X)
    (hv : v ∉ G.V) (hw : dist v w ≤ G.inverseBuffer) :
    F.maskFreeInverseAmplitude ε x y w = 0 := by
  classical
  by_cases hwV : w ∈ G.V
  · have hu : F.inverseChart ε x y w ∉ G.D₀ := by
      intro hu
      have hi : w ∈ averagedGradient (F.phase ε) x y '' G.D₀ :=
        ⟨F.inverseChart ε x y w, hu, F.averagedGradient_inverseChart hε hx hy hwV⟩
      exact hv (F.image_buffer ε hε x hx y hy
        (mem_cthickening_of_dist_le v w _ _ hi hw))
    simp [maskFreeInverseAmplitude, hwV, inverseJacobianAmplitude,
      F.normalAmplitude_eq_zero_of_not_mem_input hε x y hu]
  · simp [maskFreeInverseAmplitude, hwV]

/-- A fixed compact set contains the full spatial support for every family
and admissible parameter (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.support_extendedInverseAmplitude_subset
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    Function.support (F.extendedInverseAmplitude ε) ⊆ G.X₀ ×ˢ (G.X₀ ×ˢ closure G.V) := by
  intro z hz
  rw [Function.mem_support, F.extendedInverseAmplitude_eq_maskFree hε] at hz
  have hxy : z.1 ∈ G.X₀ ∧ z.2.1 ∈ G.X₀ := by
    by_contra h
    exact hz (F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε (not_and_or.mp h) z.2.2)
  refine ⟨hxy.1, hxy.2, subset_closure ?_⟩
  by_contra hv
  exact hz (by simp [maskFreeInverseAmplitude, hv])

/-- Compact support of the physical extension, with the containing compact
set fixed before the family (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.hasCompactSupport_extendedInverseAmplitude
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    HasCompactSupport (F.extendedInverseAmplitude ε) :=
  HasCompactSupport.intro (G.compact_X₀.prod (G.compact_X₀.prod G.compact_closure_V))
    (fun z hz ↦ by
      by_contra h
      exact hz (F.support_extendedInverseAmplitude_subset hε h))

end JanetCartan.NormalComparison
