module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Locality

/-!
# Fixed angular margins for the two-time continuation

The positive cone is the cone over a ball in the linear section. Its punctured
inner closure lies in the outer cone. These are the fixed frequency margins
consumed by the conic elapsed graph in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive cone over the fixed angular section ball, for
`app:ch_regular_base:lem:retarded-kernel`. -/
def angularCone (ℓ : E →L[ℝ] ℝ) (η₀ : E) (ρ : ℝ) : Set E :=
  {η | 0 < ℓ η ∧ (ℓ η)⁻¹ • η ∈ ball η₀ ρ}

/-- The angular chart is open, as required by the supported graph calculus
in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem isOpen_angularCone (ℓ : E →L[ℝ] ℝ) (η₀ : E) (ρ : ℝ) :
    IsOpen (angularCone ℓ η₀ ρ) := by
  rw [isOpen_iff_mem_nhds]
  intro η hη
  exact inter_mem ((isOpen_lt continuous_const ℓ.continuous).mem_nhds hη.1)
    ((ℓ.continuous.continuousAt.inv₀ hη.1.ne').smul continuousAt_id |>.preimage_mem_nhds
      (isOpen_ball.mem_nhds hη.2))

/-- The whole angular cone is convex, for averaged-gradient injectivity in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem convex_angularCone (ℓ : E →L[ℝ] ℝ) (η₀ : E) (ρ : ℝ) :
    Convex ℝ (angularCone ℓ η₀ ρ) := by
  intro η hη θ hθ a b ha hb hab
  have hL : 0 < a * ℓ η + b * ℓ θ := by
    have hη0 := hη.1
    have hθ0 := hθ.1
    by_cases ha0 : a = 0
    · simp_all
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hη0)
        (mul_nonneg hb hθ0.le)
  have hsum : a * ℓ η / (a * ℓ η + b * ℓ θ) +
      b * ℓ θ / (a * ℓ η + b * ℓ θ) = 1 := by
    rw [← add_div, div_self hL.ne']
  have hn := (convex_ball η₀ ρ) hη.2 hθ.2
    (div_nonneg (mul_nonneg ha hη.1.le) hL.le)
    (div_nonneg (mul_nonneg hb hθ.1.le) hL.le) hsum
  refine ⟨by simpa using hL, ?_⟩
  convert hn using 1
  simp only [map_add, map_smul, smul_eq_mul, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp [hη.1.ne', hθ.1.ne']

/-- Every positive radial scale stays in the same fixed cone
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem smul_mem_angularCone {ℓ : E →L[ℝ] ℝ} {η₀ η : E} {ρ a : ℝ}
    (hη : η ∈ angularCone ℓ η₀ ρ) (ha : 0 < a) : a • η ∈ angularCone ℓ η₀ ρ := by
  refine ⟨by simpa using mul_pos ha hη.1, ?_⟩
  simpa only [map_smul, smul_eq_mul, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ ha.ne', mul_one] using hη.2

/-- The conic spatial chart excludes zero
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem ne_zero_of_mem_angularCone {ℓ : E →L[ℝ] ℝ} {η₀ η : E} {ρ : ℝ}
    (hη : η ∈ angularCone ℓ η₀ ρ) : η ≠ 0 := by
  intro he
  simpa [he] using hη.1

private theorem angularCone_norm_iff (ℓ : E →L[ℝ] ℝ) (η₀ η : E) (ρ : ℝ) :
    η ∈ angularCone ℓ η₀ ρ ↔ 0 < ℓ η ∧ ‖η - ℓ η • η₀‖ < ρ * ℓ η := by
  refine and_congr_right fun hℓ ↦ ?_
  have he : η - ℓ η • η₀ = ℓ η • ((ℓ η)⁻¹ • η - η₀) := by
    rw [smul_sub, smul_inv_smul₀ hℓ.ne']
  rw [mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ,
    mul_comm ρ, mul_lt_mul_iff_right₀ hℓ]

/-- The punctured closure of an inner cone lies in every strictly wider
outer cone. A positive low-frequency collar therefore gives the closed
frequency margin in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem closure_angularCone_subset {ℓ : E →L[ℝ] ℝ} {η₀ : E} {ρ R : ℝ}
    (hρR : ρ < R) : closure (angularCone ℓ η₀ ρ) \ {0} ⊆ angularCone ℓ η₀ R := by
  let K : Set E := {η | 0 ≤ ℓ η ∧ ‖η - ℓ η • η₀‖ ≤ ρ * ℓ η}
  have hK : IsClosed K :=
    (isClosed_le continuous_const ℓ.continuous).inter
      (isClosed_le (continuous_id.sub (ℓ.continuous.smul continuous_const)).norm
        (continuous_const.mul ℓ.continuous))
  have hsub : angularCone ℓ η₀ ρ ⊆ K := fun η hη ↦
    ⟨hη.1.le, ((angularCone_norm_iff ℓ η₀ η ρ).mp hη).2.le⟩
  intro η hη
  have h := closure_minimal hsub hK hη.1
  have hℓ : 0 < ℓ η := by
    refine lt_of_le_of_ne h.1 ?_
    intro he
    have hn := h.2
    rw [← he, zero_smul, sub_zero, mul_zero] at hn
    exact hη.2 (by simpa using norm_eq_zero.mp (le_antisymm hn (norm_nonneg η)))
  exact (angularCone_norm_iff ℓ η₀ η R).mpr
    ⟨hℓ, h.2.trans_lt (mul_lt_mul_of_pos_right hρR hℓ)⟩

/-- A fixed positive spatial-frequency collar removes the vertex from the
closed inner cone, giving an actual closed support margin for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem closure_angularCone_collar_subset {ℓ : E →L[ℝ] ℝ} {η₀ : E} {ρ R c : ℝ}
    (hρR : ρ < R) (hc : 0 < c) :
    closure (angularCone ℓ η₀ ρ ∩ {η | c < ‖η‖}) ⊆ angularCone ℓ η₀ R := by
  intro η hη
  have hn : c ≤ ‖η‖ := closure_minimal
    (fun θ hθ ↦ le_of_lt hθ.2)
    (isClosed_le continuous_const continuous_norm) hη
  apply closure_angularCone_subset hρR
  refine ⟨closure_mono inter_subset_left hη, ?_⟩
  intro he
  have hz : η = 0 := he
  simp only [hz, norm_zero] at hn
  exact (not_le_of_gt hc) hn

/-- Fixed inner/outer angular margins and a linear section through the
original nonzero covector. The closed buffer radius is supplied by
`exists_buffered_physical_pencil_kernel`; the consumer is the conic chart
assembly in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_angular_margins {η₀ : E} {ε : ℝ} (hε : 0 < ε)
    (hsmall : 2 * ε < ‖η₀‖) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ η₀ = 1 ∧
      η₀ ∈ angularCone ℓ η₀ (ε / 2) ∧
      IsOpen (angularCone ℓ η₀ ε) ∧ Convex ℝ (angularCone ℓ η₀ ε) ∧
      (0 : E) ∉ angularCone ℓ η₀ ε ∧
      closure (angularCone ℓ η₀ (ε / 2)) \ {0} ⊆ angularCone ℓ η₀ ε := by
  have hn : η₀ ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hn
  refine ⟨ℓ, hℓ, ?_, isOpen_angularCone ℓ η₀ ε, convex_angularCone ℓ η₀ ε,
    fun h ↦ ne_zero_of_mem_angularCone h rfl, closure_angularCone_subset (by linarith)⟩
  simp [angularCone, hℓ, hε]

end JanetCartan.RegularSector.Characteristic.ConicPhase
