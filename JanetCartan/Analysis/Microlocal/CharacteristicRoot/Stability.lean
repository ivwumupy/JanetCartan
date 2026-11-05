module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Patch
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stability of scalar energy roots

Quantitative scalar implicit-function estimates for the initial energy equation
in `app:lem:common-hamilton-phase`. The equation already subtracts the prescribed
canonical energy. In particular, a perturbed equation need not vanish at the
reference base point.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Scalar slices of the energy equation have the distinguished partial derivative
(`app:lem:common-hamilton-phase`). This version allows any parameter space. -/
theorem hasDerivAt_scalarSlice {f : P × ℝ → ℝ} {p : P} {t : ℝ}
    (hf : DifferentiableAt ℝ f (p, t)) :
    HasDerivAt (fun s ↦ f (p, s)) (scalarDerivative f (p, t)) t := by
  simpa [scalarDerivative, Function.comp_def] using
    (hf.hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))).hasDerivAt

/-- A transverse derivative gap gives the inverse value estimate on the entire
fixed scalar interval, for either sign of the derivative
(`app:lem:common-hamilton-phase`). -/
theorem scalar_gap_mul_abs_sub_le {f : P × ℝ → ℝ} {p : P} {l u c : ℝ}
    (hf : ∀ t ∈ Icc l u, DifferentiableAt ℝ f (p, t))
    (hgap : ∀ t ∈ Icc l u, c ≤ |scalarDerivative f (p, t)|)
    {s t : ℝ} (hs : s ∈ Icc l u) (ht : t ∈ Icc l u) :
    c * |t - s| ≤ |f (p, t) - f (p, s)| := by
  have ordered : ∀ s ∈ Icc l u, ∀ t ∈ Icc l u, s < t →
      c * |t - s| ≤ |f (p, t) - f (p, s)| := by
    intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc l u := Icc_subset_Icc hs.1 ht.2
    obtain ⟨v, hv, he⟩ := exists_hasDerivAt_eq_slope
      (fun v ↦ f (p, v)) (fun v ↦ scalarDerivative f (p, v)) hst
      (fun v hv ↦ (hasDerivAt_scalarSlice (hf v (hsub hv))).continuousAt.continuousWithinAt)
      (fun v hv ↦ hasDerivAt_scalarSlice (hf v (hsub (Ioo_subset_Icc_self hv))))
    have h := hgap v (hsub (Ioo_subset_Icc_self hv))
    rw [he, abs_div] at h
    exact (le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hst.ne'))).mp h
  rcases lt_trichotomy s t with h | rfl | h
  · exact ordered s hs t ht h
  · simp
  · simpa only [abs_sub_comm] using ordered t ht s hs h

/-- A transverse gap makes a root unique in the fixed scalar interval
(`app:lem:common-hamilton-phase`). -/
theorem scalar_root_unique_of_gap {f : P × ℝ → ℝ} {p : P} {l u c : ℝ}
    (hc : 0 < c) (hf : ∀ t ∈ Icc l u, DifferentiableAt ℝ f (p, t))
    (hgap : ∀ t ∈ Icc l u, c ≤ |scalarDerivative f (p, t)|)
    {s t : ℝ} (hs : s ∈ Icc l u) (ht : t ∈ Icc l u)
    (hfs : f (p, s) = 0) (hft : f (p, t) = 0) : s = t := by
  have h := scalar_gap_mul_abs_sub_le hf hgap hs ht
  rw [hfs, hft, sub_self, abs_zero] at h
  have he : |t - s| = 0 := by nlinarith [abs_nonneg (t - s)]
  exact (sub_eq_zero.mp (abs_eq_zero.mp he)).symm

/-- Construct a smooth root on a fixed open parameter domain from opposite
endpoint signs and a transverse gap. Existence and smoothness are conclusions;
the proof glues the actual local implicit branches using uniqueness.
This is the fixed-interval step of `app:lem:common-hamilton-phase`. -/
theorem exists_smooth_root_on_interval [CompleteSpace P] {f : P × ℝ → ℝ} {U : Set P}
    (hU : IsOpen U) {l u c : ℝ} (hlu : l < u) (hc : 0 < c)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc l u, ContDiffAt ℝ ∞ f (p, t))
    (hgap : ∀ p ∈ U, ∀ t ∈ Icc l u, c ≤ |scalarDerivative f (p, t)|)
    (hend : ∀ p ∈ U, (f (p, l) < 0 ∧ 0 < f (p, u)) ∨
      (f (p, u) < 0 ∧ 0 < f (p, l))) :
    ∃ g : P → ℝ, ContDiffOn ℝ ∞ g U ∧
      (∀ p ∈ U, g p ∈ Ioo l u ∧ f (p, g p) = 0 ∧
        c ≤ |scalarDerivative f (p, g p)|) ∧
      (∀ p ∈ U, ∀ t ∈ Icc l u, f (p, t) = 0 ↔ g p = t) := by
  have hex : ∀ p ∈ U, ∃ t ∈ Ioo l u, f (p, t) = 0 := by
    intro p hp
    have hcont : ContinuousOn (fun t ↦ f (p, t)) (Icc l u) := by
      intro t ht
      exact (hasDerivAt_scalarSlice ((hf p hp t ht).differentiableAt
        (by simp))).continuousAt.continuousWithinAt
    have hex' : ∃ t ∈ Icc l u, f (p, t) = 0 := by
      rcases hend p hp with h | h
      · exact intermediate_value_Icc hlu.le hcont ⟨h.1.le, h.2.le⟩
      · exact intermediate_value_Icc' hlu.le hcont ⟨h.1.le, h.2.le⟩
    obtain ⟨t, ht, he⟩ := hex'
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, he⟩
    · intro h
      rcases hend p hp with hsign | hsign <;> simp_all
    · intro h
      rcases hend p hp with hsign | hsign <;> simp_all
  classical
  let g : P → ℝ := fun p ↦ if hp : p ∈ U then (hex p hp).choose else 0
  have hg (p : P) (hp : p ∈ U) : g p ∈ Ioo l u ∧ f (p, g p) = 0 := by
    simpa only [g, dite_eq_left hp] using (hex p hp).choose_spec
  have huniq (p : P) (hp : p ∈ U) (t : ℝ) (ht : t ∈ Icc l u) :
      f (p, t) = 0 ↔ g p = t := by
    constructor
    · exact scalar_root_unique_of_gap hc
        (fun t ht ↦ (hf p hp t ht).differentiableAt (by simp))
        (hgap p hp) (Ioo_subset_Icc_self (hg p hp).1) ht (hg p hp).2
    · rintro rfl
      exact (hg p hp).2
  refine ⟨g, ?_, ?_, huniq⟩
  · intro p hp
    have hfp := hf p hp (g p) (Ioo_subset_Icc_self (hg p hp).1)
    have hdp : scalarDerivative f (p, g p) ≠ 0 :=
      abs_pos.mp (hc.trans_le (hgap p hp _ (Ioo_subset_Icc_self (hg p hp).1)))
    let H := localRoot hfp hdp
    have hH : ContDiffAt ℝ ∞ H p := contDiffAt_localRoot hfp hdp
    have hHmem : ∀ᶠ q in 𝓝 p, H q ∈ Ioo l u := by
      apply hH.continuousAt.preimage_mem_nhds
      change Ioo l u ∈ 𝓝 (localRoot hfp hdp (p, g p).1)
      rw [localRoot_base]
      exact isOpen_Ioo.mem_nhds (hg p hp).1
    have heq : g =ᶠ[𝓝 p] H := by
      filter_upwards [hU.mem_nhds hp, hHmem,
        localRoot_eventually_zero hfp hdp (hg p hp).2] with q hq hqH hqzero
      exact (huniq q hq _ (Ioo_subset_Icc_self hqH)).mp hqzero
    exact (hH.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro p hp
    exact ⟨(hg p hp).1, (hg p hp).2,
      hgap p hp _ (Ioo_subset_Icc_self (hg p hp).1)⟩

/-- The perturbation seminorm controls values and actual first derivatives on
the compact cylinder in `app:lem:common-hamilton-phase`. Only smoothness near
the cylinder is required. -/
theorem value_fderiv_sub_le_cNorm {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {z : P × ℝ} (hz : z ∈ K) :
    |f z - f₀ z| ≤ cNorm K 2 (f - f₀) ∧
      ‖fderiv ℝ f z - fderiv ℝ f₀ z‖ ≤ cNorm K 2 (f - f₀) ∧
      |scalarDerivative f z - scalarDerivative f₀ z| ≤ cNorm K 2 (f - f₀) := by
  have hs : ∀ z ∈ K, ContDiffAt ℝ (2 : ℕ) (f - f₀) z := by
    intro z hz
    exact ((hf.contDiffAt (hD.mem_nhds (hKD hz))).sub
      (hf₀.contDiffAt (hD.mem_nhds (hKD hz)))).of_le (by simp)
  have hv := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hz (by omega : 0 ≤ 2)
  have hd := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hz (by omega : 1 ≤ 2)
  rw [norm_iteratedFDeriv_one, fderiv_sub
    ((hf.contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt (by simp))
    ((hf₀.contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt (by simp))] at hd
  refine ⟨by simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply, Real.norm_eq_abs]
    using hv, hd, ?_⟩
  have he := (fderiv ℝ f z - fderiv ℝ f₀ z).le_opNorm ((0, 1) : P × ℝ)
  simpa [scalarDerivative] using he.trans (by simpa using hd)

/-- A small perturbation preserves a uniform transverse gap on the entire
cylinder (`app:lem:common-hamilton-phase`). -/
theorem scalar_gap_of_cNorm_sub_le {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {c : ℝ} (hgap : ∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|)
    (hsmall : cNorm K 2 (f - f₀) ≤ c) :
    ∀ z ∈ K, c ≤ |scalarDerivative f z| := by
  intro z hz
  have h := (value_fderiv_sub_le_cNorm hK hD hKD hf hf₀ hz).2.2
  have htri := abs_sub_abs_le_abs_sub (scalarDerivative f₀ z) (scalarDerivative f z)
  rw [abs_sub_comm (scalarDerivative f₀ z)] at htri
  have := hgap z hz
  linarith

/-- The value of a constructed perturbed root differs from the reference root
by at most the residual divided by the transverse gap. This is the order-zero
stability estimate used by `app:lem:common-hamilton-phase`. -/
theorem root_sub_le_cNorm_div {f f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    {p : P} {l u c s t : ℝ} (hc : 0 < c)
    (hseg : ∀ v ∈ Icc l u, (p, v) ∈ K)
    (hgap : ∀ v ∈ Icc l u, c ≤ |scalarDerivative f (p, v)|)
    (hs : s ∈ Icc l u) (ht : t ∈ Icc l u)
    (hfs : f (p, s) = 0) (hft : f₀ (p, t) = 0) :
    |s - t| ≤ cNorm K 2 (f - f₀) / c := by
  have h := scalar_gap_mul_abs_sub_le
    (fun v hv ↦ (hf.contDiffAt (hD.mem_nhds (hKD (hseg v hv)))).differentiableAt
      (by simp)) hgap hs ht
  have hval := (value_fderiv_sub_le_cNorm hK hD hKD hf hf₀ (hseg t ht)).1
  rw [hfs, sub_zero] at h
  rw [hft, sub_zero] at hval
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm, abs_sub_comm] using h.trans hval

/-- On a supplied compact cylinder with reference endpoint margins, the
perturbation seminorm constructs both reference and perturbed smooth roots on
the same domain. This is the fixed-cylinder part of
`app:lem:common-hamilton-phase`; selecting this cylinder from one simple root is
a separate step. No root of the perturbed equation is an assumption. -/
theorem exists_stable_roots_on_cylinder [CompleteSpace P]
    {f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)} {U : Set P}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D) (hU : IsOpen U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) {l u c e : ℝ}
    (hlu : l < u) (hc : 0 < c) (he : 0 < e)
    (hseg : ∀ p ∈ U, ∀ t ∈ Icc l u, (p, t) ∈ K)
    (hgap : ∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|)
    (hend : ∀ p ∈ U, (f₀ (p, l) ≤ -e ∧ e ≤ f₀ (p, u)) ∨
      (f₀ (p, u) ≤ -e ∧ e ≤ f₀ (p, l))) :
    ∃ g₀ : P → ℝ, ContDiffOn ℝ ∞ g₀ U ∧
      (∀ p ∈ U, g₀ p ∈ Ioo l u ∧ f₀ (p, g₀ p) = 0) ∧
      ∀ f : P × ℝ → ℝ, ContDiffOn ℝ ∞ f D →
        cNorm K 2 (f - f₀) ≤ min c (e / 2) →
        ∃ g : P → ℝ, ContDiffOn ℝ ∞ g U ∧
          (∀ p ∈ U, g p ∈ Ioo l u ∧ f (p, g p) = 0 ∧
            c ≤ |scalarDerivative f (p, g p)| ∧
            |g p - g₀ p| ≤ cNorm K 2 (f - f₀) / c) ∧
          (∀ p ∈ U, ∀ t ∈ Icc l u, f (p, t) = 0 ↔ g p = t) := by
  obtain ⟨g₀, hg₀, hroot₀, _⟩ := exists_smooth_root_on_interval hU hlu hc
    (fun p hp t ht ↦ hf₀.contDiffAt (hD.mem_nhds (hKD (hseg p hp t ht))))
    (fun p hp t ht ↦ (by linarith [hgap (p, t) (hseg p hp t ht)]))
    (fun p hp ↦ (hend p hp).imp
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩))
  refine ⟨g₀, hg₀, fun p hp ↦ ⟨(hroot₀ p hp).1, (hroot₀ p hp).2.1⟩, ?_⟩
  intro f hf hsmall
  have hsmallc := hsmall.trans (min_le_left _ _)
  have hsmalle := hsmall.trans (min_le_right _ _)
  have hgapf := scalar_gap_of_cNorm_sub_le hK hD hKD hf hf₀ hgap hsmallc
  have hendf : ∀ p ∈ U, (f (p, l) < 0 ∧ 0 < f (p, u)) ∨
      (f (p, u) < 0 ∧ 0 < f (p, l)) := by
    intro p hp
    have hl := abs_le.mp ((value_fderiv_sub_le_cNorm hK hD hKD hf hf₀
      (hseg p hp l (left_mem_Icc.mpr hlu.le))).1.trans hsmalle)
    have hu := abs_le.mp ((value_fderiv_sub_le_cNorm hK hD hKD hf hf₀
      (hseg p hp u (right_mem_Icc.mpr hlu.le))).1.trans hsmalle)
    exact (hend p hp).imp
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
      (fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩)
  obtain ⟨g, hg, hroot, huniq⟩ := exists_smooth_root_on_interval hU hlu hc
    (fun p hp t ht ↦ hf.contDiffAt (hD.mem_nhds (hKD (hseg p hp t ht))))
    (fun p hp t ht ↦ hgapf (p, t) (hseg p hp t ht)) hendf
  refine ⟨g, hg, ?_, huniq⟩
  intro p hp
  refine ⟨(hroot p hp).1, (hroot p hp).2.1, (hroot p hp).2.2, ?_⟩
  exact root_sub_le_cNorm_div hK hD hKD hf hf₀ hc (hseg p hp)
    (fun t ht ↦ hgapf (p, t) (hseg p hp t ht))
    (Ioo_subset_Icc_self (hroot p hp).1) (Ioo_subset_Icc_self (hroot₀ p hp).1)
    (hroot p hp).2.1 (hroot₀ p hp).2.1

/-- Differentiating the actual root equation gives the linear identity used to
compare first derivatives in `app:lem:common-hamilton-phase`. -/
theorem scalarDerivative_smul_fderiv_root {f : P × ℝ → ℝ} {g : P → ℝ} {p : P}
    (hf : DifferentiableAt ℝ f (p, g p)) (hg : DifferentiableAt ℝ g p)
    (heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0) :
    scalarDerivative f (p, g p) • fderiv ℝ g p =
      -(fderiv ℝ f (p, g p) ∘L ContinuousLinearMap.inl ℝ P ℝ) := by
  have hchain := hf.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk hg.hasFDerivAt)
  have hz : fderiv ℝ f (p, g p) ∘L
      ((ContinuousLinearMap.id ℝ P).prod (fderiv ℝ g p)) = 0 := by
    exact hchain.unique ((hasFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq heq)
  ext v
  have hv := congrArg (fun L : P →L[ℝ] ℝ ↦ L v) hz
  have hsplit : (v, fderiv ℝ g p v) =
      ((v, 0) : P × ℝ) + (fderiv ℝ g p v) • ((0, 1) : P × ℝ) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at hv
  rw [hsplit, map_add, map_smul] at hv
  simp only [smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
  change scalarDerivative f (p, g p) * fderiv ℝ g p v = _
  change fderiv ℝ f (p, g p) (v, 0) +
    fderiv ℝ g p v * scalarDerivative f (p, g p) = 0 at hv
  linarith

private theorem norm_parameterPartial_le (L : P × ℝ →L[ℝ] ℝ) :
    ‖L ∘L ContinuousLinearMap.inl ℝ P ℝ‖ ≤ ‖L‖ := by
  apply (L ∘L ContinuousLinearMap.inl ℝ P ℝ).opNorm_le_bound (norm_nonneg _)
  intro v
  simpa using L.le_opNorm (v, 0)

/-- The actual differential of a root is bounded by the full equation
differential divided by its transverse gap (`app:lem:common-hamilton-phase`). -/
theorem norm_fderiv_root_le {f : P × ℝ → ℝ} {g : P → ℝ} {p : P} {c M : ℝ}
    (hc : 0 < c) (hf : DifferentiableAt ℝ f (p, g p))
    (hg : DifferentiableAt ℝ g p) (heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0)
    (hgap : c ≤ |scalarDerivative f (p, g p)|) (hM : ‖fderiv ℝ f (p, g p)‖ ≤ M) :
    ‖fderiv ℝ g p‖ ≤ M / c := by
  have hid := congrArg norm (scalarDerivative_smul_fderiv_root hf hg heq)
  rw [norm_smul, Real.norm_eq_abs, norm_neg] at hid
  apply (le_div_iff₀ hc).mpr
  calc
    ‖fderiv ℝ g p‖ * c ≤ |scalarDerivative f (p, g p)| * ‖fderiv ℝ g p‖ := by
      nlinarith [norm_nonneg (fderiv ℝ g p)]
    _ = _ := hid
    _ ≤ ‖fderiv ℝ f (p, g p)‖ := norm_parameterPartial_le _
    _ ≤ M := hM

/-- Subtracting differentiated root equations controls the actual first
derivative difference. The input compares the equation differentials at the two
root graphs; it is obtained from the second-order seminorm and the value estimate
in `app:lem:common-hamilton-phase`. -/
theorem fderiv_root_sub_le_of_fderiv_sub_le
    {f f₀ : P × ℝ → ℝ} {g g₀ : P → ℝ} {p : P} {c B ε : ℝ}
    (hc : 0 < c) (hf : DifferentiableAt ℝ f (p, g p))
    (hf₀ : DifferentiableAt ℝ f₀ (p, g₀ p))
    (hg : DifferentiableAt ℝ g p) (hg₀ : DifferentiableAt ℝ g₀ p)
    (heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0)
    (heq₀ : ∀ᶠ q in 𝓝 p, f₀ (q, g₀ q) = 0)
    (hgap : c ≤ |scalarDerivative f (p, g p)|)
    (hB : ‖fderiv ℝ g₀ p‖ ≤ B)
    (hε : ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ ≤ ε) :
    ‖fderiv ℝ g p - fderiv ℝ g₀ p‖ ≤ (1 + B) * ε / c := by
  let L := fderiv ℝ f (p, g p)
  let L₀ := fderiv ℝ f₀ (p, g₀ p)
  let d := scalarDerivative f (p, g p)
  let d₀ := scalarDerivative f₀ (p, g₀ p)
  let A := L ∘L ContinuousLinearMap.inl ℝ P ℝ
  let A₀ := L₀ ∘L ContinuousLinearMap.inl ℝ P ℝ
  let G := fderiv ℝ g p
  let G₀ := fderiv ℝ g₀ p
  have hA : ‖A - A₀‖ ≤ ε := by
    change ‖(L - L₀) ∘L ContinuousLinearMap.inl ℝ P ℝ‖ ≤ ε
    exact (norm_parameterPartial_le _).trans hε
  have hd : |d - d₀| ≤ ε := by
    have h := (L - L₀).le_opNorm ((0, 1) : P × ℝ)
    have hd' : |d - d₀| ≤ ‖L - L₀‖ := by
      simpa [d, d₀, L, L₀, scalarDerivative] using h
    exact hd'.trans hε
  have hG : d • G = -A := scalarDerivative_smul_fderiv_root hf hg heq
  have hG₀ : d₀ • G₀ = -A₀ := scalarDerivative_smul_fderiv_root hf₀ hg₀ heq₀
  have hid : d • (G - G₀) = -(A - A₀) - (d - d₀) • G₀ := by
    rw [smul_sub, sub_smul, hG, hG₀]
    abel
  have hnorm : |d| * ‖G - G₀‖ ≤ ε + ε * B := by
    calc
      _ = ‖d • (G - G₀)‖ := (norm_smul _ _).symm
      _ = ‖-(A - A₀) - (d - d₀) • G₀‖ := congrArg norm hid
      _ ≤ ‖A - A₀‖ + |d - d₀| * ‖G₀‖ := by
        simpa only [norm_neg, norm_smul, Real.norm_eq_abs] using
          norm_sub_le (-(A - A₀)) ((d - d₀) • G₀)
      _ ≤ ε + ε * B := add_le_add hA
        (mul_le_mul hd hB (norm_nonneg _) ((norm_nonneg _).trans hε))
  apply (le_div_iff₀ hc).mpr
  change ‖G - G₀‖ * c ≤ (1 + B) * ε
  have hnonneg := norm_nonneg (G - G₀)
  change c ≤ |d| at hgap
  nlinarith

/-- The second-order seminorm bounds variation of the reference equation's
first differential across a convex compact cylinder
(`app:lem:common-hamilton-phase`). -/
theorem fderiv_sub_le_cNorm_mul_dist {f : P × ℝ → ℝ} {K D : Set (P × ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) {x y : P × ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ cNorm K 2 f * ‖y - x‖ := by
  have hs (z : P × ℝ) (hz : z ∈ K) : ContDiffAt ℝ ∞ f z :=
    hf.contDiffAt (hD.mem_nhds (hKD hz))
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ ((hs z hz).fderiv_right (m := 1) (by simp)).differentiableAt (by simp))
    _ hx hy
  intro z hz
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun z hz ↦ (hs z hz).of_le (by simp)) hz (by omega)

/-- On a convex compact cylinder with reference endpoint margins and transverse
gap, nearby equations have smooth roots on the same open parameter domain with
uniform value and actual first-derivative estimates. This completes the
fixed-cylinder perturbation step of `app:lem:common-hamilton-phase`. -/
theorem exists_C1_stable_roots_on_cylinder [CompleteSpace P]
    {f₀ : P × ℝ → ℝ} {K D : Set (P × ℝ)} {U : Set P}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hD : IsOpen D) (hKD : K ⊆ D) (hU : IsOpen U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) {l u c e : ℝ}
    (hlu : l < u) (hc : 0 < c) (he : 0 < e)
    (hseg : ∀ p ∈ U, ∀ t ∈ Icc l u, (p, t) ∈ K)
    (hgap : ∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|)
    (hend : ∀ p ∈ U, (f₀ (p, l) ≤ -e ∧ e ≤ f₀ (p, u)) ∨
      (f₀ (p, u) ≤ -e ∧ e ≤ f₀ (p, l))) :
    ∃ (g₀ : P → ℝ) (C δ : ℝ), 0 < C ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ g₀ U ∧
      (∀ p ∈ U, g₀ p ∈ Ioo l u ∧ f₀ (p, g₀ p) = 0) ∧
      ∀ f : P × ℝ → ℝ, ContDiffOn ℝ ∞ f D → cNorm K 2 (f - f₀) ≤ δ →
        ∃ g : P → ℝ, ContDiffOn ℝ ∞ g U ∧
          (∀ p ∈ U, g p ∈ Ioo l u ∧ f (p, g p) = 0 ∧
            c ≤ |scalarDerivative f (p, g p)| ∧
            |g p - g₀ p| ≤ C * cNorm K 2 (f - f₀) ∧
            ‖fderiv ℝ g p - fderiv ℝ g₀ p‖ ≤ C * cNorm K 2 (f - f₀)) ∧
          (∀ p ∈ U, ∀ t ∈ Icc l u, f (p, t) = 0 ↔ g p = t) := by
  obtain ⟨g₀, hg₀, hroot₀, hpert⟩ := exists_stable_roots_on_cylinder
    hK hD hKD hU hf₀ hlu hc he hseg hgap hend
  let M := cNorm K 2 f₀
  let B := 1 + M / c
  have hM : 0 ≤ M := cNorm_nonneg _ _ _
  have hB : 1 ≤ B := by dsimp [B]; linarith [div_nonneg hM hc.le]
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let C := 1 / c + B * B / c
  refine ⟨g₀, C, min c (e / 2), by dsimp [C]; positivity,
    lt_min hc (half_pos he), hg₀, hroot₀, ?_⟩
  intro f hf hsmall
  obtain ⟨g, hg, hroot, huniq⟩ := hpert f hf hsmall
  refine ⟨g, hg, ?_, huniq⟩
  intro p hp
  let ε := cNorm K 2 (f - f₀)
  have hε : 0 ≤ ε := cNorm_nonneg _ _ _
  have hgp := hroot p hp
  have hg₀p := hroot₀ p hp
  have hz := hseg p hp _ (Ioo_subset_Icc_self hgp.1)
  have hz₀ := hseg p hp _ (Ioo_subset_Icc_self hg₀p.1)
  have hfp := (hf.contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt (by simp)
  have hf₀p := (hf₀.contDiffAt (hD.mem_nhds (hKD hz₀))).differentiableAt (by simp)
  have hgg := (hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hgg₀ := (hg₀.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hroot q hq).2.1
  have heq₀ : ∀ᶠ q in 𝓝 p, f₀ (q, g₀ q) = 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hroot₀ q hq).2
  have hnorm₀ : ‖fderiv ℝ f₀ (p, g₀ p)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
        hz₀ (by omega : 1 ≤ 2)
  have hG₀ := norm_fderiv_root_le hc hf₀p hgg₀ heq₀
    (show c ≤ |scalarDerivative f₀ (p, g₀ p)| by linarith [hgap _ hz₀]) hnorm₀
  have hdiff : ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ ≤ B * ε := by
    have hshift := fderiv_sub_le_cNorm_mul_dist hK hconv hD hKD hf₀ hz₀ hz
    have hshift' : ‖fderiv ℝ f₀ (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ ≤
        M * |g p - g₀ p| := by simpa [Prod.norm_def, Real.norm_eq_abs] using hshift
    calc
      _ ≤ ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g p)‖ +
          ‖fderiv ℝ f₀ (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + M * (ε / c) := add_le_add
        (value_fderiv_sub_le_cNorm hK hD hKD hf hf₀ hz).2.1
        (hshift'.trans (mul_le_mul_of_nonneg_left hgp.2.2.2 hM))
      _ = B * ε := by dsimp [B]; ring
  have hder := fderiv_root_sub_le_of_fderiv_sub_le hc hfp hf₀p hgg hgg₀
    heq heq₀ hgp.2.2.1 hG₀ hdiff
  refine ⟨hgp.1, hgp.2.1, hgp.2.2.1, ?_, ?_⟩
  · calc
      _ ≤ ε / c := hgp.2.2.2
      _ = (1 / c) * ε := by ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) hε
  · change ‖fderiv ℝ g p - fderiv ℝ g₀ p‖ ≤ C * ε
    calc
      _ ≤ B * (B * ε) / c := hder
      _ = (B * B / c) * ε := by ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity)) hε

/-- A simple reference root determines a fixed cylinder with positive parameter
and scalar radii, a transverse gap, and nonzero endpoint margins. These are
constructed from the original equation, rather than assumed as perturbation
data (`app:lem:common-hamilton-phase`). -/
theorem exists_simple_root_cylinder {f₀ : P × ℝ → ℝ} {D : Set (P × ℝ)}
    (hD : IsOpen D) (hf₀ : ContDiffOn ℝ ∞ f₀ D) {z₀ : P × ℝ}
    (hz₀ : z₀ ∈ D) (hzero : f₀ z₀ = 0) (hd : scalarDerivative f₀ z₀ ≠ 0) :
    ∃ r a c e : ℝ, 0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < e ∧
      let K := Metric.closedBall z₀.1 (2 * r) ×ˢ Icc (z₀.2 - a) (z₀.2 + a)
      K ⊆ D ∧ (∀ z ∈ K, 2 * c ≤ |scalarDerivative f₀ z|) ∧
      (∀ p ∈ Metric.closedBall z₀.1 (2 * r),
        (f₀ (p, z₀.2 - a) ≤ -e ∧ e ≤ f₀ (p, z₀.2 + a)) ∨
        (f₀ (p, z₀.2 + a) ≤ -e ∧ e ≤ f₀ (p, z₀.2 - a))) := by
  let d := scalarDerivative f₀ z₀
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hcont := continuousAt_scalarDerivative (hf₀.contDiffAt (hD.mem_nhds hz₀))
  have hnear : ∀ᶠ z in 𝓝 z₀, z ∈ D ∧ |scalarDerivative f₀ z - d| < |d| / 2 := by
    filter_upwards [hD.mem_nhds hz₀,
      (hcont.sub continuousAt_const).abs.eventually_lt continuousAt_const
        (show |scalarDerivative f₀ z₀ - d| < |d| / 2 by dsimp [d]; simpa using half_pos (abs_pos.mpr hd))]
      with z hz hdiff
    exact ⟨hz, hdiff⟩
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let a := R / 2
  have ha : 0 < a := half_pos hR
  have haR : a ≤ R := by dsimp [a]; linarith
  have hline (t : ℝ) (ht : t ∈ Icc (z₀.2 - a) (z₀.2 + a)) :
      (z₀.1, t) ∈ Metric.closedBall z₀ R := by
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hR.le, (show |t - z₀.2| ≤ a from abs_le.mpr
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans haR⟩
  have hslice (t : ℝ) (ht : t ∈ Icc (z₀.2 - a) (z₀.2 + a)) :
      HasDerivAt (fun t ↦ f₀ (z₀.1, t)) (scalarDerivative f₀ (z₀.1, t)) t :=
    hasDerivAt_scalarSlice ((hf₀.contDiffAt
      (hD.mem_nhds (hball (hline t ht)).1)).differentiableAt (by simp))
  have hslcont : ContinuousOn (fun t ↦ f₀ (z₀.1, t))
      (Icc (z₀.2 - a) (z₀.2 + a)) :=
    fun t ht ↦ (hslice t ht).continuousAt.continuousWithinAt
  have hmid : z₀.2 ∈ Icc (z₀.2 - a) (z₀.2 + a) := ⟨by linarith, by linarith⟩
  have hlu : z₀.2 - a ≤ z₀.2 + a := by linarith
  have hlmem := left_mem_Icc.mpr hlu
  have humem := right_mem_Icc.mpr hlu
  have hcross : (f₀ (z₀.1, z₀.2 - a) < 0 ∧ 0 < f₀ (z₀.1, z₀.2 + a)) ∨
      (f₀ (z₀.1, z₀.2 + a) < 0 ∧ 0 < f₀ (z₀.1, z₀.2 - a)) := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have hm := strictAntiOn_of_deriv_neg (convex_Icc (z₀.2 - a) (z₀.2 + a))
        hslcont (fun t ht ↦ ?_)
      · right
        constructor
        · simpa only [Prod.eta, hzero] using hm hmid humem (by linarith : z₀.2 < z₀.2 + a)
        · simpa only [Prod.eta, hzero] using hm hlmem hmid (by linarith : z₀.2 - a < z₀.2)
      · have ht' := interior_subset ht
        rw [(hslice t ht').deriv]
        have hn := (abs_lt.mp (hball (hline t ht')).2).2
        have hdabs : |d| = -d := abs_of_neg hneg
        rw [hdabs] at hn
        linarith
    · have hm := strictMonoOn_of_deriv_pos (convex_Icc (z₀.2 - a) (z₀.2 + a))
        hslcont (fun t ht ↦ ?_)
      · left
        constructor
        · simpa only [Prod.eta, hzero] using hm hlmem hmid (by linarith : z₀.2 - a < z₀.2)
        · simpa only [Prod.eta, hzero] using hm hmid humem (by linarith : z₀.2 < z₀.2 + a)
      · have ht' := interior_subset ht
        rw [(hslice t ht').deriv]
        have hn := (abs_lt.mp (hball (hline t ht')).2).1
        have hdabs : |d| = d := abs_of_pos hpos
        rw [hdabs] at hn
        linarith
  have hmargin : ∃ e : ℝ, 0 < e ∧
      ((f₀ (z₀.1, z₀.2 - a) < -e ∧ e < f₀ (z₀.1, z₀.2 + a)) ∨
      (f₀ (z₀.1, z₀.2 + a) < -e ∧ e < f₀ (z₀.1, z₀.2 - a))) := by
    rcases hcross with h | h
    · refine ⟨min (-f₀ (z₀.1, z₀.2 - a)) (f₀ (z₀.1, z₀.2 + a)) / 2,
        half_pos (lt_min (neg_pos.mpr h.1) h.2), Or.inl ⟨?_, ?_⟩⟩ <;>
        linarith [min_le_left (-f₀ (z₀.1, z₀.2 - a)) (f₀ (z₀.1, z₀.2 + a)),
          min_le_right (-f₀ (z₀.1, z₀.2 - a)) (f₀ (z₀.1, z₀.2 + a))]
    · refine ⟨min (-f₀ (z₀.1, z₀.2 + a)) (f₀ (z₀.1, z₀.2 - a)) / 2,
        half_pos (lt_min (neg_pos.mpr h.1) h.2), Or.inr ⟨?_, ?_⟩⟩ <;>
        linarith [min_le_left (-f₀ (z₀.1, z₀.2 + a)) (f₀ (z₀.1, z₀.2 - a)),
          min_le_right (-f₀ (z₀.1, z₀.2 + a)) (f₀ (z₀.1, z₀.2 - a))]
  obtain ⟨e, he, hend⟩ := hmargin
  have hcl : ContinuousAt (fun p ↦ f₀ (p, z₀.2 - a)) z₀.1 :=
    (hf₀.contDiffAt (hD.mem_nhds (hball (hline _ hlmem)).1)).continuousAt.comp
      (f := fun p : P ↦ (p, z₀.2 - a))
      (continuousAt_id.prodMk continuousAt_const)
  have hcu : ContinuousAt (fun p ↦ f₀ (p, z₀.2 + a)) z₀.1 :=
    (hf₀.contDiffAt (hD.mem_nhds (hball (hline _ humem)).1)).continuousAt.comp
      (f := fun p : P ↦ (p, z₀.2 + a))
      (continuousAt_id.prodMk continuousAt_const)
  have hevent : ∀ᶠ p in 𝓝 z₀.1,
      (f₀ (p, z₀.2 - a) ≤ -e ∧ e ≤ f₀ (p, z₀.2 + a)) ∨
      (f₀ (p, z₀.2 + a) ≤ -e ∧ e ≤ f₀ (p, z₀.2 - a)) := by
    rcases hend with h | h
    · filter_upwards [hcl.eventually_lt continuousAt_const h.1,
        continuousAt_const.eventually_lt hcu h.2] with p hl hu
      exact Or.inl ⟨hl.le, hu.le⟩
    · filter_upwards [hcu.eventually_lt continuousAt_const h.1,
        continuousAt_const.eventually_lt hcl h.2] with p hu hl
      exact Or.inr ⟨hu.le, hl.le⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hevent
  let r := min R ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r ≤ R := by dsimp [r]; linarith [min_le_left R ρ, lt_min hR hρ]
  have hrρ : 2 * r ≤ ρ := by dsimp [r]; linarith [min_le_right R ρ, lt_min hR hρ]
  have hsub : Metric.closedBall z₀.1 (2 * r) ×ˢ Icc (z₀.2 - a) (z₀.2 + a) ⊆
      Metric.closedBall z₀ R := by
    intro z hz
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨hz.1.trans hrR, (show |z.2 - z₀.2| ≤ a from abs_le.mpr
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩).trans haR⟩
  refine ⟨r, a, |d| / 4, e, hr, ha, by positivity, he,
    fun z hz ↦ (hball (hsub hz)).1, ?_, ?_⟩
  · intro z hz
    have hdiff := (hball (hsub hz)).2
    have htri := abs_sub_abs_le_abs_sub d (scalarDerivative f₀ z)
    rw [abs_sub_comm d] at htri
    linarith
  · intro p hp
    exact hρsub (Metric.closedBall_subset_closedBall hrρ hp)

/-- Uniform quantitative implicit roots at unchanged canonical energy
(`app:lem:common-hamilton-phase`). A single simple zero of the reference equation
constructs a compact cylinder and positive fixed radii. Every sufficiently small
second-order seminorm perturbation has a unique smooth root on the same outer
parameter ball, with a common transverse gap and uniform bounds for its value
and actual first derivative on the buffered inner closed ball. No base-point
zero or root-existence assumption is imposed on the perturbed equation. -/
theorem exists_uniform_C1_stable_root [FiniteDimensional ℝ P]
    {f₀ : P × ℝ → ℝ} {D : Set (P × ℝ)} (hD : IsOpen D)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) {z₀ : P × ℝ}
    (hz₀ : z₀ ∈ D) (hzero : f₀ z₀ = 0) (hd : scalarDerivative f₀ z₀ ≠ 0) :
    ∃ (r a c C δ : ℝ) (g₀ : P → ℝ),
      0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧ 0 < δ ∧
      let K := Metric.closedBall z₀.1 (2 * r) ×ˢ Icc (z₀.2 - a) (z₀.2 + a)
      IsCompact K ∧ K ⊆ D ∧ g₀ z₀.1 = z₀.2 ∧
      ContDiffOn ℝ ∞ g₀ (Metric.ball z₀.1 (2 * r)) ∧
      (∀ p ∈ Metric.ball z₀.1 (2 * r),
        g₀ p ∈ Ioo (z₀.2 - a) (z₀.2 + a) ∧ f₀ (p, g₀ p) = 0) ∧
      ∀ f : P × ℝ → ℝ, ContDiffOn ℝ ∞ f D → cNorm K 2 (f - f₀) ≤ δ →
        ∃ g : P → ℝ, ContDiffOn ℝ ∞ g (Metric.ball z₀.1 (2 * r)) ∧
          (∀ p ∈ Metric.ball z₀.1 (2 * r),
            g p ∈ Ioo (z₀.2 - a) (z₀.2 + a) ∧ (p, g p) ∈ K ∧
              f (p, g p) = 0 ∧ c ≤ |scalarDerivative f (p, g p)|) ∧
          (∀ p ∈ Metric.ball z₀.1 (2 * r), ∀ t ∈ Icc (z₀.2 - a) (z₀.2 + a),
            f (p, t) = 0 ↔ g p = t) ∧
          (∀ p ∈ Metric.closedBall z₀.1 r,
            |g p - g₀ p| ≤ C * cNorm K 2 (f - f₀) ∧
              ‖fderiv ℝ g p - fderiv ℝ g₀ p‖ ≤ C * cNorm K 2 (f - f₀)) := by
  obtain ⟨r, a, c, e, hr, ha, hc, he, hKD, hgap, hend⟩ :=
    exists_simple_root_cylinder hD hf₀ hz₀ hzero hd
  let K := Metric.closedBall z₀.1 (2 * r) ×ˢ Icc (z₀.2 - a) (z₀.2 + a)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hconv : Convex ℝ K := (convex_closedBall _ _).prod (convex_Icc _ _)
  have hseg : ∀ p ∈ Metric.ball z₀.1 (2 * r),
      ∀ t ∈ Icc (z₀.2 - a) (z₀.2 + a), (p, t) ∈ K :=
    fun _ hp _ ht ↦ ⟨Metric.ball_subset_closedBall hp, ht⟩
  obtain ⟨g₀, C, δ, hC, hδ, hg₀, hroot₀, hpert⟩ :=
    exists_C1_stable_roots_on_cylinder hK hconv hD hKD Metric.isOpen_ball hf₀
      (by linarith : z₀.2 - a < z₀.2 + a) hc he hseg hgap
      (fun p hp ↦ hend p (Metric.ball_subset_closedBall hp))
  have hbase : g₀ z₀.1 = z₀.2 := by
    have hp : z₀.1 ∈ Metric.ball z₀.1 (2 * r) := Metric.mem_ball_self (by positivity)
    have ht : z₀.2 ∈ Icc (z₀.2 - a) (z₀.2 + a) := ⟨by linarith, by linarith⟩
    apply scalar_root_unique_of_gap hc
      (fun t ht ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD (hseg _ hp t ht)))).differentiableAt
        (by simp))
      (fun t ht ↦ (by linarith [hgap _ (hseg _ hp t ht)]))
      (Ioo_subset_Icc_self (hroot₀ _ hp).1) ht (hroot₀ _ hp).2
    simpa only [Prod.eta] using hzero
  refine ⟨r, a, c, C, δ, g₀, hr, ha, hc, hC, hδ, hK, hKD, hbase,
    hg₀, hroot₀, ?_⟩
  intro f hf hsmall
  obtain ⟨g, hg, hroot, huniq⟩ := hpert f hf hsmall
  refine ⟨g, hg, ?_, huniq, ?_⟩
  · intro p hp
    have h := hroot p hp
    exact ⟨h.1, hseg p hp _ (Ioo_subset_Icc_self h.1), h.2.1, h.2.2.1⟩
  · intro p hp
    have hp' : p ∈ Metric.ball z₀.1 (2 * r) :=
      (Metric.closedBall_subset_ball (by linarith : r < 2 * r)) hp
    exact (hroot p hp').2.2.2

end JanetCartan.CharacteristicRoot
