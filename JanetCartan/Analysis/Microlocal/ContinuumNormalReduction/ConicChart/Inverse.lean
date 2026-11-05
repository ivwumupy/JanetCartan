module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Basic

/-!
# The conic inverse constructed from the annular inverse

Step 1 of `app:ch_background:prop:bg-frame`. The inverse is formed by applying
the annular inverse to the normalized output and undoing that dilation only
in the covector slot. Its value is independent of every admissible choice of
normalization, and its two components have degrees zero and one respectively.
-/

@[expose] public noncomputable section

open Set Function

namespace JanetCartan.ContinuumNormalReduction.ConicChart.AnnularData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : AnnularData E)

/-- The annular inverse used by the extension in
`app:ch_background:prop:bg-frame`. It uses the same `invFunOn` construction as
`NormalComparison.UniformNormalData.inverseChart`. -/
def annularInverse (k : ℝ × E) : ℝ × E := invFunOn A.map A.annulus k

/-- The conic inverse in `app:ch_background:eq:bg-full-complex-amplitude`.
Its asserted inverse properties are restricted to the actual cone image. -/
def inverse (k : ℝ × E) : ℝ × E :=
  radialScale ‖k.2‖ (A.annularInverse (‖k.2‖⁻¹ • k))

/-- The annular inverse identity used in the conic extension
(`app:ch_background:prop:bg-frame`). -/
theorem annularInverse_map {u : ℝ × E} (hu : u ∈ A.annulus) :
    A.annularInverse (A.map u) = u :=
  A.annular_injective.leftInvOn_invFunOn hu

/-- The constructed conic inverse is a left inverse on the supported cone
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem inverse_map {u : ℝ × E} (hu : u ∈ A.cone) :
    A.inverse (A.map u) = u := by
  have hp := A.transverse_norm_pos hu
  unfold inverse
  rw [← A.homogeneous u hu _ (inv_pos.mpr hp),
    A.annularInverse_map (A.normalize_mem_annulus hu)]
  simp [hp.ne']

/-- The extended inverse takes its values in the actual input cone
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem inverse_mem {k : ℝ × E} (hk : k ∈ A.map '' A.cone) :
    A.inverse k ∈ A.cone := by
  obtain ⟨u, hu, rfl⟩ := hk
  rw [A.inverse_map hu]
  exact hu

/-- The constructed inverse is a right inverse on the conic output chart
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem map_inverse {k : ℝ × E} (hk : k ∈ A.map '' A.cone) :
    A.map (A.inverse k) = k := by
  obtain ⟨u, hu, rfl⟩ := hk
  rw [A.inverse_map hu]

/-- The output image is itself conic (`app:ch_background:prop:bg-frame`). -/
theorem smul_mem_image {k : ℝ × E} (hk : k ∈ A.map '' A.cone)
    {t : ℝ} (ht : 0 < t) : t • k ∈ A.map '' A.cone := by
  obtain ⟨u, hu, rfl⟩ := hk
  exact ⟨radialScale t u, A.scale_mem u hu t ht, A.homogeneous u hu t ht⟩

/-- Uniqueness of any inverse branch on the supported cone; used to glue
local annular charts in `app:ch_background:prop:bg-frame`. -/
theorem inverse_eq_of_map_eq {k u : ℝ × E} (hu : u ∈ A.cone)
    (he : A.map u = k) : A.inverse k = u := by
  rw [← he, A.inverse_map hu]

/-- Every admissible annular normalization gives the same conic inverse.
This is the overlap independence required in Step 1 of
`app:ch_background:prop:bg-frame`. -/
theorem inverse_eq_rescaled_annularInverse {k : ℝ × E} {t : ℝ}
    (ht : 0 < t) (hk : t • k ∈ A.map '' A.annulus) :
    A.inverse k = radialScale t⁻¹ (A.annularInverse (t • k)) := by
  have hu : A.annularInverse (t • k) ∈ A.annulus := invFunOn_mem hk
  have he : A.map (A.annularInverse (t • k)) = t • k := invFunOn_eq hk
  apply A.inverse_eq_of_map_eq (A.scale_mem _ hu.1 _ (inv_pos.mpr ht))
  rw [A.homogeneous _ hu.1 _ (inv_pos.mpr ht), he, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]

/-- Dilation fixes the inverse incidence parameter and dilates only its
covector (`app:ch_background:eq:bg-jacobian`). -/
theorem inverse_smul {k : ℝ × E} (hk : k ∈ A.map '' A.cone)
    {t : ℝ} (ht : 0 < t) :
    A.inverse (t • k) = radialScale t (A.inverse k) := by
  obtain ⟨u, hu, rfl⟩ := hk
  rw [← A.homogeneous u hu t ht, A.inverse_map (A.scale_mem u hu t ht),
    A.inverse_map hu]

/-- Degree zero of the incidence component of the inverse
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem inverse_smul_fst {k : ℝ × E} (hk : k ∈ A.map '' A.cone)
    {t : ℝ} (ht : 0 < t) : (A.inverse (t • k)).1 = (A.inverse k).1 := by
  rw [A.inverse_smul hk ht]
  rfl

/-- Degree one of the covector component of the inverse
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem inverse_smul_snd {k : ℝ × E} (hk : k ∈ A.map '' A.cone)
    {t : ℝ} (ht : 0 < t) : (A.inverse (t • k)).2 = t • (A.inverse k).2 := by
  rw [A.inverse_smul hk ht]
  rfl

end JanetCartan.ContinuumNormalReduction.ConicChart.AnnularData
