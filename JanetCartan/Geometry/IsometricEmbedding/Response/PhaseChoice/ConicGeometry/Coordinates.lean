module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Signed

/-!
# Fixed Euclidean coordinates for the canonical product

The consumer `ResponseTransfer.reverseSource_gap_uniform` uses Euclidean
canonical variables. The selected section supplies a fixed equivalence with
the original canonical product. Its two norm inequalities and exact dual
pairing prevent a silent change of norm or Fourier convention in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Fixed Euclidean coordinates for canonical covectors. This is a coordinate
map, not a substitution of physical momentum for canonical energy
(`app:ch_response:thm:response-literal-transfer`). -/
def sectionCanonicalEquiv : (ℝ × Euclidean (n - 1)) ≃L[ℝ] Euclidean n where
  toFun η := η.1 • T.data.adapted.normal + T.data.adapted.embedding η.2
  invFun p := (⟪T.data.adapted.normal, p⟫_ℝ,
    T.data.adapted.embedding.toContinuousLinearMap.adjoint p)
  map_add' := by intro η θ; simp [add_smul]; abel
  map_smul' := by intro a η; simp [smul_add, smul_smul]
  left_inv := by
    intro η
    apply Prod.ext
    · simp [inner_add_right, inner_smul_right, T.data.adapted.orthogonal,
        T.data.adapted.normal_unit]
    · apply ext_inner_right ℝ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp [inner_add_left, inner_smul_left, T.data.adapted.orthogonal,
        T.data.adapted.embedding.inner_map_map]
  right_inv := T.data.adapted.covector_decomposition
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The canonical bilinear pairing becomes the ordinary Euclidean pairing
under the fixed equivalence; no `2π` factors are introduced
(`app:ch_response:thm:response-literal-transfer`). -/
theorem sectionCanonicalEquiv_pairing (η θ : ℝ × Euclidean (n - 1)) :
    ⟪T.sectionCanonicalEquiv η, T.sectionCanonicalEquiv θ⟫_ℝ = canonicalCovector η θ := by
  change ⟪η.1 • T.data.adapted.normal + T.data.adapted.embedding η.2,
    θ.1 • T.data.adapted.normal + T.data.adapted.embedding θ.2⟫_ℝ = _
  have horth : ⟪T.data.adapted.embedding η.2, T.data.adapted.normal⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact T.data.adapted.orthogonal _
  simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    T.data.adapted.orthogonal, horth, T.data.adapted.normal_unit,
    T.data.adapted.embedding.inner_map_map, canonicalCovector_apply, mul_comm]

/-- The Euclidean coordinate map costs at most a factor two relative to the
retained canonical maximum norm
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_sectionCanonicalEquiv_le (η : ℝ × Euclidean (n - 1)) :
    ‖T.sectionCanonicalEquiv η‖ ≤ 2 * ‖η‖ := by
  have h := norm_add_le (η.1 • T.data.adapted.normal) (T.data.adapted.embedding η.2)
  rw [norm_smul, T.data.adapted.normal_unit, mul_one, LinearIsometry.norm_map] at h
  exact h.trans (by linarith [norm_fst_le η, norm_snd_le η])

/-- The inverse coordinate map is a contraction into the original canonical
maximum norm (`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_sectionCanonicalEquiv_symm_le (p : Euclidean n) :
    ‖T.sectionCanonicalEquiv.symm p‖ ≤ ‖p‖ := by
  change max ‖⟪T.data.adapted.normal, p⟫_ℝ‖
    ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint p‖ ≤ ‖p‖
  apply max_le
  · simpa only [T.data.adapted.normal_unit, one_mul] using norm_inner_le_norm
      T.data.adapted.normal p
  · calc
      _ ≤ ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint‖ * ‖p‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.adjoint.norm_map _).le.trans
          T.data.adapted.embedding.norm_toContinuousLinearMap_le) (norm_nonneg _)
      _ = _ := one_mul _

/-- The precise two-sided comparison used when passing the geometric bounds
to Euclidean canonical variables
(`app:ch_response:thm:response-literal-transfer`). -/
theorem sectionCanonicalEquiv_norm_bounds (η : ℝ × Euclidean (n - 1)) :
    ‖η‖ ≤ ‖T.sectionCanonicalEquiv η‖ ∧ ‖T.sectionCanonicalEquiv η‖ ≤ 2 * ‖η‖ := by
  exact ⟨by simpa using T.norm_sectionCanonicalEquiv_symm_le (T.sectionCanonicalEquiv η),
    T.norm_sectionCanonicalEquiv_le η⟩

/-- Explicit transport of the two annular constants and the global inverse
constant through the fixed coordinate equivalence. The hypotheses here are
exactly the conclusions of `exists_selected_primary_conic_geometry`; that
theorem supplies their actual construction from primitive frame closeness
(`app:ch_response:thm:response-literal-transfer`). -/
theorem sectionCanonicalEquiv_transfer_bounds
    (F : (ℝ × Euclidean (n - 1)) → Euclidean n)
    {D : Set (ℝ × Euclidean (n - 1))} {m M L : ℝ}
    (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hann : ∀ η ∈ D, m * ‖η‖ ≤ ‖F η‖ ∧ ‖F η‖ ≤ M * ‖η‖)
    (hinv : ∀ η ∈ D, ∀ θ ∈ D, ‖η - θ‖ ≤ L * ‖F η - F θ‖) :
    (∀ p ∈ T.sectionCanonicalEquiv '' D,
      (m / 2) * ‖p‖ ≤ ‖F (T.sectionCanonicalEquiv.symm p)‖ ∧
      ‖F (T.sectionCanonicalEquiv.symm p)‖ ≤ M * ‖p‖) ∧
    (∀ p ∈ T.sectionCanonicalEquiv '' D, ∀ q ∈ T.sectionCanonicalEquiv '' D,
      ‖p - q‖ ≤ (2 * L) *
        ‖F (T.sectionCanonicalEquiv.symm p) - F (T.sectionCanonicalEquiv.symm q)‖) := by
  constructor
  · rintro p ⟨η, hη, rfl⟩
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    have hn := T.sectionCanonicalEquiv_norm_bounds η
    have ha := hann η hη
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hn.2 hm],
      ha.2.trans (mul_le_mul_of_nonneg_left hn.1 hM)⟩
  · rintro p ⟨η, hη, rfl⟩ q ⟨θ, hθ, rfl⟩
    simp only [ContinuousLinearEquiv.symm_apply_apply, ← map_sub]
    exact (T.norm_sectionCanonicalEquiv_le (η - θ)).trans
      (by nlinarith [hinv η hη θ hθ])

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
