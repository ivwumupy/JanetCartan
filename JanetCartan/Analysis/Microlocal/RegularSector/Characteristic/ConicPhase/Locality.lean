module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Basic

/-!
# Exact local agreement of the conic two-time phase

The Euler identity follows from the proved full differential of the original
phase. Integration on a convex local frequency patch identifies the radial
continuation with that phase on an open overlap. Thus all its local jets,
not just its values, are retained.
Source: `app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrate the original phase's Euler identity along a radial segment
inside the local chart. The differential is the actual one produced by
`exists_buffered_physical_pencil_kernel`, not a conic homogeneity assumption.
Consumer: exact overlap in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem localPhase_smul_on_convex
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {P : Set E} (hP : IsOpen P) (hPc : Convex ℝ P)
    {t s : ℝ} {y : E} (hPt : ∀ η ∈ P, (t, (s, (y, η))) ∈ C.target)
    {η : E} (hη : η ∈ P) {a : ℝ} (ha : 0 < a) (haη : a • η ∈ P) :
    twoTimePhase C (t, (s, (y, a • η))) = a * twoTimePhase C (t, (s, (y, η))) := by
  let I : Set ℝ := {b | b • η ∈ P} ∩ Ioi 0
  have hI : IsOpen I := (hP.preimage (continuous_id.smul continuous_const)).inter isOpen_Ioi
  have hIc : Convex ℝ I := by
    refine Convex.inter ?_ (convex_Ioi 0)
    intro b hb c hc u v hu hv huv
    change (u • b + v • c) • η ∈ P
    simpa only [smul_smul, add_smul, smul_eq_mul] using hPc hb hc hu hv huv
  have h1 : (1 : ℝ) ∈ I := ⟨by simpa using hη, by norm_num⟩
  have haI : a ∈ I := ⟨haη, ha⟩
  have hd (b : ℝ) (hb : b ∈ I) :
      HasDerivAt (fun c : ℝ ↦ twoTimePhase C (t, (s, (y, c • η))) / c) 0 b := by
    have he := ((hasFDerivAt_twoTimePhase_covector (hdiff _ (hPt _ hb.1))).comp_hasDerivAt b
      ((hasDerivAt_id b).smul_const η)).div (hasDerivAt_id b) hb.2.ne'
    convert! he using 1
    simp only [Function.comp_apply, innerSL_apply_apply, one_smul,
      twoTimePhase, inner_smul_right, id_eq, mul_one]
    ring
  have he := hI.is_const_of_deriv_eq_zero hIc.isPreconnected
    (fun b hb ↦ (hd b hb).differentiableAt.differentiableWithinAt)
    (fun b hb ↦ (hd b hb).deriv) haI h1
  simp only [one_smul, div_one] at he
  exact (div_eq_iff ha.ne').mp he |>.trans (mul_comm _ _)

/-- Exact agreement whenever a covector and its fixed radial representative
belong to the same convex local patch
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_eq_on_overlap (ℓ : E →L[ℝ] ℝ)
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {B : Set (ℝ × (ℝ × E))} {P : Set E} (hP : IsOpen P) (hPc : Convex ℝ P)
    (hsub : localPatch B P ⊆ C.target)
    {q : TwoTimePoint E} (hq : q ∈ localPatch B P ∩ domain ℓ (localPatch B P)) :
    phase ℓ C q = twoTimePhase C q := by
  have he := localPhase_smul_on_convex hdiff hP hPc
    (fun η hη ↦ hsub ⟨hq.1.1, hη⟩) hq.1.2 (inv_pos.mpr hq.2.1) hq.2.2.2
  change ℓ q.2.2.2 * twoTimePhase C (normalize ℓ q) = _
  rw [show twoTimePhase C (normalize ℓ q) = (ℓ q.2.2.2)⁻¹ * twoTimePhase C q from he,
    ← mul_assoc, mul_inv_cancel₀ hq.2.1.ne', one_mul]

/-- The agreement is joint in both times, position, and covector, hence
preserves every phase jet on the overlap
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_eventuallyEq_on_overlap (ℓ : E →L[ℝ] ℝ)
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {B : Set (ℝ × (ℝ × E))} {P : Set E}
    (hB : IsOpen B) (hP : IsOpen P) (hPc : Convex ℝ P)
    (hsub : localPatch B P ⊆ C.target)
    {q : TwoTimePoint E} (hq : q ∈ localPatch B P ∩ domain ℓ (localPatch B P)) :
    phase ℓ C =ᶠ[𝓝 q] twoTimePhase C := by
  filter_upwards [((isOpen_localPatch hB hP).inter
    (isOpen_domain ℓ (isOpen_localPatch hB hP))).mem_nhds hq] with w hw
  exact phase_eq_on_overlap ℓ hdiff hP hPc hsub hw

/-- Every point of the unbounded cone normalizes into the open overlap.
Consumer: transferring the spatial mixed half-gap without radial loss
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem phase_eventuallyEq_at_normalize (ℓ : E →L[ℝ] ℝ)
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    {B : Set (ℝ × (ℝ × E))} {P : Set E}
    (hB : IsOpen B) (hP : IsOpen P) (hPc : Convex ℝ P)
    (hsub : localPatch B P ⊆ C.target)
    {q : TwoTimePoint E} (hq : q ∈ domain ℓ (localPatch B P)) :
    phase ℓ C =ᶠ[𝓝 (normalize ℓ q)] twoTimePhase C := by
  have hℓ := normalization_eq_one ℓ hq.1.ne'
  apply phase_eventuallyEq_on_overlap ℓ hdiff hB hP hPc hsub
  refine ⟨hq.2, ?_, ?_⟩
  · rw [hℓ]; norm_num
  · rw [normalize_of_eq_one ℓ hℓ]
    exact hq.2

end JanetCartan.RegularSector.Characteristic.ConicPhase
