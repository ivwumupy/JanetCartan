module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Eikonal
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Normalized
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Scaling
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolRegularity

/-!
# Positive conic invariance of protected phase graphs

The conic part of `app:ch_regular:thm:no-return` and
`app:ch_regular:defn:protected-saturation`.  A zero-energy phase graph is
first propagated by the eikonal graph theorem.  Positive homogeneity then
propagates every radial multiple of that graph.  The Lipschitz constant needed
by the graph theorem is obtained from the smooth Hamilton field on the actual
compact covector buffer.  No invariance hypothesis is used.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology NNReal

namespace JanetCartan.ProtectedFlow

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace P]

/-- The positive conic lift of a phase-gradient family over a physical set.
`app:ch_regular:defn:protected-saturation`. -/
def positiveConicLift (g : P → E → E) (X : Set E) (V : Set P) : Set (E × E) :=
  {z | z.1 ∈ X ∧ ∃ η ∈ V, ∃ r : ℝ, 0 < r ∧ z.2 = r • g η z.1}

omit [CompleteSpace E] [TopologicalSpace P] in
@[simp] theorem mem_positiveConicLift_iff {g : P → E → E} {X : Set E} {V : Set P}
    {z : E × E} : z ∈ positiveConicLift g X V ↔
      z.1 ∈ X ∧ ∃ η ∈ V, ∃ r : ℝ, 0 < r ∧ z.2 = r • g η z.1 := Iff.rfl

omit [CompleteSpace E] in
/-- Positive radial rescaling does not change a normalized covector. -/
theorem normalizedCovector_smul_pos {v : E} {r : ℝ} (hr : 0 < r) :
    normalizedCovector (r • v) = normalizedCovector v := by
  unfold normalizedCovector
  by_cases hv : v = 0
  · simp [hv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  field_simp [ne_of_gt hr, hvn]

/-- Smoothness of the symbol gives the global defect-Lipschitz bound required by
`characteristic_stays_on_eikonal_graph` on a convex compact covector buffer.
The defect is the actual Hamilton defect, so no graph-invariance premise is
hidden in this bound (`app:ch_regular:thm:no-return`). -/
theorem exists_defect_lipschitzOnWith_of_smooth
    (H : HamiltonPhase.HomogeneousSymbol E)
    {D : Set E} (hDconv : Convex ℝ D) (hDcompact : IsCompact D)
    {y : E} (hsub : ∀ z ∈ D, (y, z) ∈ H.domain)
    (hH : ContDiffOn ℝ 2 H.h H.domain)
    {dg : E →L[ℝ] E} :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun z ↦ -H.hx (y, z) - dg (H.hp (y, z))) D := by
  have hv : ContDiffOn ℝ 1 H.vectorField H.domain :=
    H.contDiffOn_vectorField (n := 1) hH
  have hin : ContDiffOn ℝ 1 (fun z : E ↦ (y, z)) D :=
    contDiffOn_const.prodMk contDiffOn_id
  have hv' : ContDiffOn ℝ 1 (fun z : E ↦ H.vectorField (y, z)) D :=
    hv.comp hin hsub
  have hp : ContDiffOn ℝ 1 (fun z : E ↦ H.hp (y, z)) D := by
    simpa [HamiltonPhase.HomogeneousSymbol.vectorField] using hv'.fst
  have hmhx : ContDiffOn ℝ 1 (fun z : E ↦ -H.hx (y, z)) D := by
    simpa [HamiltonPhase.HomogeneousSymbol.vectorField] using hv'.snd
  have hdg : ContDiffOn ℝ 1 (fun _ : E ↦ dg) D := contDiffOn_const
  have hcomp : ContDiffOn ℝ 1 (fun z : E ↦ dg (H.hp (y, z))) D :=
    hdg.clm_apply hp
  have hdef : ContDiffOn ℝ 1
      (fun z ↦ -H.hx (y, z) - dg (H.hp (y, z))) D := hmhx.sub hcomp
  exact hdef.exists_lipschitzOnWith one_ne_zero hDconv hDcompact

/-- A compact physical restriction makes the preceding local estimate uniform
in the base point (`app:ch_regular:thm:no-return`). -/
theorem exists_uniform_defect_lipschitzOnWith_of_smooth
    (H : HamiltonPhase.HomogeneousSymbol E)
    {Y D : Set E} (hY : IsCompact Y) (hD : IsCompact D)
    (hprod : Y ×ˢ D ⊆ H.domain)
    (hH : ContDiffOn ℝ 2 H.h H.domain)
    {dg : E → E →L[ℝ] E} (hdg : ContDiff ℝ 1 dg) :
    ∃ L : ℝ≥0, ∀ y ∈ Y, LipschitzOnWith L
      (fun z ↦ -H.hx (y, z) - dg y (H.hp (y, z))) D := by
  have hv : ContDiffOn ℝ 1 H.vectorField H.domain :=
    H.contDiffOn_vectorField (n := 1) hH
  have hpair : ContDiffOn ℝ 1 (fun z : E × E ↦ z) H.domain := contDiffOn_id
  have hv' : ContDiffOn ℝ 1 (fun z : E × E ↦ H.vectorField z) H.domain := hv
  have hp : ContDiffOn ℝ 1 (fun z : E × E ↦ H.hp z) H.domain := by
    simpa [HamiltonPhase.HomogeneousSymbol.vectorField] using hv'.fst
  have hmhx : ContDiffOn ℝ 1 (fun z : E × E ↦ -H.hx z) H.domain := by
    simpa [HamiltonPhase.HomogeneousSymbol.vectorField] using hv'.snd
  have hdg' : ContDiffOn ℝ 1 (fun z : E × E ↦ dg z.1) H.domain := by
    exact hdg.contDiffOn.comp contDiffOn_fst (fun _ _ ↦ mem_univ _)
  have hcomp : ContDiffOn ℝ 1 (fun z : E × E ↦ dg z.1 (H.hp z)) H.domain :=
    hdg'.clm_apply hp
  have hF : ContDiffOn ℝ 1
      (fun z : E × E ↦ -H.hx z - dg z.1 (H.hp z)) H.domain := hmhx.sub hcomp
  have hloc : LocallyLipschitzOn (Y ×ˢ D)
      (fun z : E × E ↦ -H.hx z - dg z.1 (H.hp z)) := by
    intro z hz
    have hzdom : z ∈ H.domain := hprod hz
    obtain ⟨K, s, hs, hKs⟩ :=
      (hF.contDiffAt (H.isOpen_domain.mem_nhds hzdom)).exists_lipschitzOnWith
    exact ⟨K, s, mem_nhdsWithin_of_mem_nhds hs, hKs⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hY.prod hD) hloc
  refine ⟨L, fun y hy z hz w hw ↦ ?_⟩
  have hz' : (y, z) ∈ Y ×ˢ D := ⟨hy, hz⟩
  have hw' : (y, w) ∈ Y ×ˢ D := ⟨hy, hw⟩
  have hh := hL hz' hw'
  simpa only [edist_dist, dist_prod_same_left] using hh

/-- Every positive radial multiple of a zero-energy phase graph is preserved by
Hamilton's equations on a complete segment, in either orientation.  The graph
and the Lipschitz bound are derived from the phase and symbol smoothness;
conic homogeneity supplies the radial domain and energy identities.
`app:ch_regular:thm:no-return`. -/
theorem characteristic_stays_on_positive_conic_graph
    (H : HamiltonPhase.HomogeneousSymbol E)
    (hH : H.ConicHomogeneous)
    {W Y D : Set E} {ψ : E → ℝ} {dg : E → E →L[ℝ] E}
    {x p : ℝ → E} {a b t₀ r : ℝ}
    (hW : IsOpen W) (ht₀ : t₀ ∈ Icc a b) (hr : 0 < r)
    (hψ : ∀ y ∈ W, ContDiffAt ℝ 2 ψ y)
    (hgraph : ∀ y ∈ W, HasFDerivAt (gradient ψ) (dg y) y)
    (hmem : ∀ y ∈ W, (y, gradient ψ y) ∈ H.domain)
    (he : ∀ y ∈ W, H.h (y, gradient ψ y) = 0)
    (hY : IsCompact Y) (hD : IsCompact D) (hWY : W ⊆ Y)
    (hprod : Y ×ˢ D ⊆ H.domain)
    (hHsmooth : ContDiffOn ℝ 2 H.h H.domain)
    (hdg : ContDiff ℝ 1 dg)
    (hgD : ∀ y ∈ W, gradient ψ y ∈ D)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (H.hp (x t, p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (-H.hx (x t, p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ W)
    (hpD : ∀ t ∈ Icc a b, p t ∈ D)
    (hqD : ∀ t ∈ Icc a b, r⁻¹ • p t ∈ D)
    (hinit : p t₀ = r • gradient ψ (x t₀)) :
    ∀ t ∈ Icc a b, p t = r • gradient ψ (x t) := by
  let q : ℝ → E := fun t ↦ r⁻¹ • p t
  have hqmem : ∀ t ∈ Icc a b, (x t, q t) ∈ H.domain := by
    intro t ht
    have hp_mem : (x t, p t) ∈ H.domain := hprod ⟨hWY (hxW t ht), hpD t ht⟩
    exact hH.scale_mem (x t, p t) hp_mem r⁻¹ (inv_pos.mpr hr)
  have hpq : ∀ t ∈ Icc a b, p t = r • q t := by
    intro t ht
    dsimp [q]
    rw [smul_smul]
    field_simp [ne_of_gt hr]
    simp
  have hxq : ∀ t ∈ Icc a b, HasDerivAt x (H.hp (x t, q t)) t := by
    intro t ht
    convert hx t ht using 1
    rw [hpq t ht, H.hp_smul hH (hqmem t ht) hr]
  have hq : ∀ t ∈ Icc a b, HasDerivAt q (-H.hx (x t, q t)) t := by
    intro t ht
    have hd := (hp t ht).const_smul r⁻¹
    convert hd using 1
    rw [hpq t ht, H.hx_smul hH (hqmem t ht) hr]
    simp [q, smul_neg, smul_smul, ne_of_gt hr]
  obtain ⟨L, hL'⟩ := exists_uniform_defect_lipschitzOnWith_of_smooth
    H hY hD hprod hHsmooth hdg
  have hL : ∀ y ∈ W, LipschitzOnWith L
      (fun z ↦ -H.hx (y, z) - dg y (H.hp (y, z))) D :=
    fun y hy ↦ hL' y (hWY hy)
  have heq : ∀ t ∈ Icc a b, q t = gradient ψ (x t) :=
    characteristic_stays_on_eikonal_graph H hW ht₀ hψ hgraph hmem he hL
      hxq hq hxW hqD hgD (by
        dsimp [q]
        rw [hinit]
        simp [smul_smul, ne_of_gt hr])
  intro t ht
  rw [hpq t ht, heq t ht]

/-- A one-step characteristic relation preserving the positive conic lift.
The segment hypotheses are discharged by
`characteristic_stays_on_positive_conic_graph`; this interface keeps the
finite-chain induction independent of a particular factor implementation. -/
def PositiveConicCharacteristicStep
    (R : (E × E) → (E × E) → Prop) : (E × E) → (E × E) → Prop :=
  R

/-- A diagonal step or a characteristic step. -/
def PositiveConicChainStep
    (R : (E × E) → (E × E) → Prop) (z w : E × E) : Prop :=
  z = w ∨ PositiveConicCharacteristicStep R z w

/-- Finite chains of diagonal and characteristic relations preserve any set
once the characteristic one-step implication has been proved. -/
inductive PositiveConicChain
    (R : (E × E) → (E × E) → Prop) : (E × E) → (E × E) → ℕ → Prop
  | refl (z : E × E) : PositiveConicChain R z z 0
  | tail {z y w : E × E} {n : ℕ} :
      PositiveConicChainStep R z y → PositiveConicChain R y w n →
      PositiveConicChain R z w (n + 1)

omit [CompleteSpace E] [TopologicalSpace P] in
/-- Arbitrary finite products preserve the positive conic lift, including
elliptic identity (diagonal) sources. `app:ch_regular:defn:protected-saturation`. -/
theorem positiveConicChain_preserves
    {g : P → E → E} {X : Set E} {V : Set P}
    {R : (E × E) → (E × E) → Prop}
    (hchar : ∀ z w, z ∈ positiveConicLift g X V → R z w →
      w ∈ positiveConicLift g X V)
    {z w : E × E} {n : ℕ}
    (hchain : PositiveConicChain R z w n)
    (hz : z ∈ positiveConicLift g X V) :
    w ∈ positiveConicLift g X V := by
  induction hchain with
  | refl z => exact hz
  | @tail z y w n hstep hrest ih =>
      apply ih
      rcases hstep with hdiag | hR
      · simpa [hdiag] using hz
      · exact hchar z y hz hR

omit [CompleteSpace E] in
/-- Compact physical and parameter restrictions give one angular buffer for the
whole positive conic lift.  The radius is independent of the conic scale and
of the length of a finite chain. `app:ch_regular:thm:no-return`. -/
theorem exists_positiveConicLift_buffer
    {g : P → E → E} {X : Set E} {V : Set P} {G M : Set E}
    (hX : IsCompact X) (hV : IsCompact V)
    (hg : ContinuousOn (fun y : E × P ↦ g y.2 y.1) (X ×ˢ V))
    (hne : ∀ x ∈ X, ∀ η ∈ V, g η x ≠ 0)
    (hG : IsOpen G) (hM : IsClosed M)
    (hregular : ∀ x ∈ X, ∀ η ∈ V,
      normalizedCovector (g η x) ∈ G \ M) :
    ∃ ε > 0, ∀ z ∈ positiveConicLift g X V,
      closedBall (normalizedCovector z.2) ε ⊆ G \ M := by
  obtain ⟨ε, hε, hbuffer⟩ :=
    exists_normalized_graph_ball_buffer hX hV hg hne hG hM hregular
  refine ⟨ε, hε, ?_⟩
  rintro z ⟨hzX, η, hη, r, hr, hrz⟩
  rw [hrz, normalizedCovector_smul_pos hr]
  exact hbuffer z.1 hzX η hη

end JanetCartan.ProtectedFlow
