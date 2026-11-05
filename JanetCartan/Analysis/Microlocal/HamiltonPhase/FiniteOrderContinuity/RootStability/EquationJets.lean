module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootValueBounds

/-!
# Equation jets along actual root graphs

The induction for `app:lem:common-hamilton-phase` compares equation jets at two
root graphs before solving for the highest root jet. These estimates use the
perturbation seminorm at exactly the requested order. The additional derivative
in the graph displacement bound belongs only to the fixed reference equation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Same-point equation jets are controlled at the perturbation order `m`.
This supplies the equation-jet input to the root induction in
`app:lem:common-hamilton-phase`. -/
theorem equation_jet_sub_le_cNorm {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {m n : ℕ} (hn : n ≤ m) {z : P × ℝ} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f₀ z‖ ≤
      cNorm K m (f - f₀) := by
  have hs (z : P × ℝ) (hz : z ∈ K) : ContDiffAt ℝ m (f - f₀) z :=
    ((hf.sub hf₀).contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp)
  have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hz hn
  rw [iteratedFDeriv_sub_apply
    ((hf.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
    ((hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))] at hb
  exact hb

/-- The order-zero root estimate with no derivative loss in the perturbation.
The gap is a separate low-order input (`app:lem:common-hamilton-phase`). -/
theorem root_sub_le_cNorm_zero {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {p : P} {l u c s t : ℝ} (hc : 0 < c)
    (hseg : ∀ v ∈ Icc l u, (p, v) ∈ K)
    (hgap : ∀ v ∈ Icc l u, c ≤ |scalarDerivative f (p, v)|)
    (hs : s ∈ Icc l u) (ht : t ∈ Icc l u)
    (hfs : f (p, s) = 0) (hft : f₀ (p, t) = 0) :
    |s - t| ≤ cNorm K 0 (f - f₀) / c := by
  have h := scalar_gap_mul_abs_sub_le
    (fun v hv ↦ (hf.contDiffAt (hD.mem_nhds (hKD (hseg v hv)))).differentiableAt
      (by simp)) hgap hs ht
  have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (f := f - f₀) hK
    (fun z hz ↦ ((hf.sub hf₀).contDiffAt (hD.mem_nhds (hKD hz))).of_le
      (by simp : (0 : ℕ∞ω) ≤ ∞)) (hseg t ht) (le_refl 0)
  simp only [norm_iteratedFDeriv_zero, Pi.sub_apply, hft, sub_zero,
    Real.norm_eq_abs] at hb
  rw [hfs, sub_zero] at h
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm, abs_sub_comm] using h.trans hb

/-- Variation of the reference equation's `n`th jet across a convex cylinder
is bounded by its fixed `(n+1)`st seminorm. The consumer is
`rootGraph_jet_sub_le_cNorm` (`app:lem:common-hamilton-phase`). -/
theorem iteratedFDeriv_sub_le_cNorm_mul_norm {f : P × ℝ → ℝ}
    {K D : Set (P × ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hD : IsOpen D) (hKD : K ⊆ D) (hf : ContDiffOn ℝ ∞ f D)
    (n : ℕ) {x y : P × ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ ≤
      cNorm K (n + 1) f * ‖y - x‖ := by
  have hs (z : P × ℝ) (hz : z ∈ K) : ContDiffAt ℝ ∞ f z :=
    hf.contDiffAt (hD.mem_nhds (hKD hz))
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ ((hs z hz).iteratedFDeriv_right (m := 1) (by simp)).differentiableAt
      (by simp)) _ hx hy
  intro z hz
  rw [norm_fderiv_iteratedFDeriv]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun z hz ↦ (hs z hz).of_le (by simp)) hz le_rfl

/-- Equation jets evaluated at independently constructed roots have the same
perturbation order as the equation itself. Only fixed reference derivatives
through `m+1` enter the constant. This is the coefficient input for the
higher root-jet induction in `app:lem:common-hamilton-phase`. -/
theorem rootGraph_jet_sub_le_cNorm {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {m n : ℕ} (hn : n ≤ m) {p : P} {l u c s t : ℝ} (hc : 0 < c)
    (hseg : ∀ v ∈ Icc l u, (p, v) ∈ K)
    (hgap : ∀ v ∈ Icc l u, c ≤ |scalarDerivative f (p, v)|)
    (hs : s ∈ Icc l u) (ht : t ∈ Icc l u)
    (hfs : f (p, s) = 0) (hft : f₀ (p, t) = 0) :
    ‖iteratedFDeriv ℝ n f (p, s) - iteratedFDeriv ℝ n f₀ (p, t)‖ ≤
      (1 + cNorm K (m + 1) f₀ / c) * cNorm K m (f - f₀) := by
  have hval : |s - t| ≤ cNorm K m (f - f₀) / c :=
    (root_sub_le_cNorm_zero hK hD hKD hf hf₀ hc hseg hgap hs ht hfs hft).trans
      (div_le_div_of_nonneg_right (cNorm_mono_order (Nat.zero_le m)) hc.le)
  have hshift := iteratedFDeriv_sub_le_cNorm_mul_norm hK hconv hD hKD hf₀ n
    (hseg t ht) (hseg s hs)
  have hshift' : ‖iteratedFDeriv ℝ n f₀ (p, s) - iteratedFDeriv ℝ n f₀ (p, t)‖ ≤
      cNorm K (m + 1) f₀ * (cNorm K m (f - f₀) / c) := by
    simp only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs,
      max_eq_right (abs_nonneg (s - t))] at hshift
    exact hshift.trans (mul_le_mul (cNorm_mono_order (Nat.add_le_add_right hn 1)) hval
      (abs_nonneg _) (cNorm_nonneg _ _ _))
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (p, s) - iteratedFDeriv ℝ n f₀ (p, s)‖ +
        ‖iteratedFDeriv ℝ n f₀ (p, s) - iteratedFDeriv ℝ n f₀ (p, t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ cNorm K m (f - f₀) + cNorm K (m + 1) f₀ * (cNorm K m (f - f₀) / c) :=
      add_le_add (equation_jet_sub_le_cNorm hK hD hKD hf hf₀ hn (hseg s hs)) hshift'
    _ = _ := by ring

end JanetCartan.CharacteristicRoot
