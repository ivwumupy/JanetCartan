module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.CarrierCompatibility.Flow

/-!
# Fixed buffers for comparing the supplied flows

The domain deductions for `app:ch_waves:thm:leading` use only fixed radii,
a velocity bound and a Lipschitz bound for the frozen carrier graph. Thus the
smaller time and label radii can be chosen before the immersion. In particular,
containment of the two trajectories in a common uniqueness domain is deduced,
rather than hidden in an interface field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff NNReal

namespace JanetCartan.LeadingWave.FullModulation.CarrierCompatibility

/-- A velocity bound controls displacement on both sides of the initial
section. Used below to place the actual footpoint and both trajectories in
common buffers (`app:ch_waves:thm:leading`). -/
theorem trajectory_displacement_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ v : ℝ → E} {a b M t : ℝ}
    (h0 : (0 : ℝ) ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hd : ∀ s ∈ Ioo a b, HasDerivAt γ (v s) s)
    (hv : ∀ s ∈ Ioo a b, ‖v s‖ ≤ M) : dist (γ t) (γ 0) ≤ M * |t| := by
  simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs ↦ (hd s hs).hasDerivWithinAt) hv (convex_Ioo a b) h0 ht

/-- Explicit common radii depend only on the two constructor buffers, the
fixed speed bound, and the frozen graph Lipschitz bound. The generous spatial
margin also accommodates the footpoint and its whole trajectory
(`app:ch_waves:thm:leading`). -/
theorem exists_comparison_radii {Rc Rf Rg τc τf M L : ℝ}
    (hRc : 0 < Rc) (hRf : 0 < Rf) (hRg : 0 < Rg) (hτc : 0 < τc) (hτf : 0 < τf)
    (hM : 0 ≤ M) (hL : 1 ≤ L) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ ≤ τc ∧ δ ≤ τf ∧
      8 * r ≤ Rc / 32 ∧ 8 * L * r ≤ Rf / 32 ∧ M * δ ≤ r ∧ 3 * r ≤ Rg := by
  have hLp : 0 < L := by linarith
  let r := min (Rc / 256) (min (Rf / (256 * L)) (Rg / 4))
  have hr : 0 < r := by dsimp [r]; positivity
  let δ := min τc (min τf (r / (M + 1)))
  have hδ : 0 < δ := lt_min hτc (lt_min hτf (by positivity))
  have hrC : r ≤ Rc / 256 := min_le_left _ _
  have hrF : r * (256 * L) ≤ Rf :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hδM : δ * (M + 1) ≤ r :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hrG : r ≤ Rg / 4 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨r, δ, hr, hδ, min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), by linarith, by nlinarith,
    by nlinarith, by linarith⟩

section Domains
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Quantitative common domain for the two actual constructor interfaces.
`g` is the frozen carrier-label graph. Each map is assumed to solve its own
ODE with a bounded velocity on its original domain. The carrier inverse maps
into its own initial-label ball and satisfies its own right inverse identity.
The conclusion gives the common initial label and both range containments
needed by `amplitudes_eq_on_carrier`, on a fixed smaller cylinder.

The radii are supplied by `exists_comparison_radii` before the current
immersion; no comparison of the maps is assumed
(`app:ch_waves:thm:leading`). -/
theorem common_trajectory_buffers
    {g : E → G} {p₀ : E} {Rc Rf Rg τc τf M r δ : ℝ} {L : ℝ≥0}
    (_hRc : 0 < Rc) (hRf : 0 < Rf) (hr : 0 < r) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hL : 1 ≤ (L : ℝ))
    (hδc : δ ≤ τc) (hδf : δ ≤ τf)
    (hrc : 8 * r ≤ Rc / 32) (hrf : 8 * (L : ℝ) * r ≤ Rf / 32)
    (hMδ : M * δ ≤ r) (hrg : 3 * r ≤ Rg)
    (hg : LipschitzOnWith L g (closedBall p₀ Rg))
    {φ y : ℝ × E → E} {Φ : ℝ × G → G}
    {vc : ℝ → E → E} {vf : ℝ → G → G}
    {Dc : Set (ℝ × E)} {Df : Set (ℝ × G)}
    (hcoverc : Ioo (-τc) τc ×ˢ ball p₀ (Rc / 32) ⊆ Dc)
    (hcoverf : Ioo (-τf) τf ×ˢ ball (g p₀) (Rf / 32) ⊆ Df)
    (hy : ∀ q ∈ Dc, y q ∈ ball p₀ (Rc / 8))
    (hφy : ∀ q ∈ Dc, φ (q.1, y q) = q.2)
    (hi : ∀ p ∈ ball p₀ (Rc / 8), φ (0, p) = p)
    (hI : ∀ p ∈ ball (g p₀) (Rf / 8), Φ (0, p) = p)
    (hd : ∀ p ∈ ball p₀ (Rc / 8), ∀ t ∈ Ioo (-τc) τc,
      HasDerivAt (fun s ↦ φ (s, p)) (vc t (φ (t, p))) t)
    (hD : ∀ p ∈ ball (g p₀) (Rf / 8), ∀ t ∈ Ioo (-τf) τf,
      HasDerivAt (fun s ↦ Φ (s, p)) (vf t (Φ (t, p))) t)
    (hv : ∀ p ∈ ball p₀ (Rc / 8), ∀ t ∈ Ioo (-τc) τc,
      ‖vc t (φ (t, p))‖ ≤ M)
    (hV : ∀ p ∈ ball (g p₀) (Rf / 8), ∀ t ∈ Ioo (-τf) τf,
      ‖vf t (Φ (t, p))‖ ≤ M) :
    ∀ q ∈ Ioo (-δ) δ ×ˢ ball p₀ r,
      q ∈ Dc ∧ (q.1, g q.2) ∈ Df ∧
      y q ∈ ball p₀ (2 * r) ∧ g (y q) ∈ ball (g p₀) (Rf / 8) ∧
      ∀ t ∈ Ioo (-δ) δ,
        g (φ (t, y q)) ∈ closedBall (g p₀) (Rf / 2) ∧
        Φ (t, g (y q)) ∈ closedBall (g p₀) (Rf / 2) := by
  have htC {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-τc) τc := by
    constructor <;> linarith [ht.1, ht.2]
  have htF {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ Ioo (-τf) τf := by
    constructor <;> linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hspeed {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : M * |t| ≤ r :=
    (mul_le_mul_of_nonneg_left (abs_lt.mpr ht).le hM).trans hMδ
  have hcenter : p₀ ∈ closedBall p₀ Rg := mem_closedBall_self (by linarith)
  have hgraph {p : E} (hp : dist p p₀ < 3 * r) :
      dist (g p) (g p₀) < (L : ℝ) * (3 * r) := by
    have hpC : p ∈ closedBall p₀ Rg := by
      rw [mem_closedBall]; linarith
    exact (hg.dist_le_mul p hpC p₀ hcenter).trans_lt
      (mul_lt_mul_of_pos_left hp (by linarith))
  intro q hq
  have hqc : q ∈ Dc := hcoverc ⟨htC hq.1, ball_subset_ball (by linarith) hq.2⟩
  have hqf : (q.1, g q.2) ∈ Df := by
    refine hcoverf ⟨htF hq.1, ?_⟩
    have hb := hgraph (lt_trans (mem_ball.mp hq.2) (by linarith : r < 3 * r))
    rw [mem_ball]
    nlinarith
  have hyp := hy q hqc
  have hdis {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : dist (φ (t, y q)) (y q) ≤ r := by
    have hb := trajectory_displacement_le (htC h0) (htC ht) (hd _ hyp) (hv _ hyp)
    rw [hi _ hyp] at hb
    exact hb.trans (hspeed ht)
  have hypSmall : dist (y q) p₀ < 2 * r := by
    have hb := hdis hq.1
    rw [hφy q hqc, dist_comm q.2] at hb
    have htri := dist_triangle (y q) q.2 p₀
    have hqp := mem_ball.mp hq.2
    linarith
  have hgy := hgraph (hypSmall.trans (by linarith : 2 * r < 3 * r))
  have hgyp : g (y q) ∈ ball (g p₀) (Rf / 8) := by
    rw [mem_ball]; nlinarith
  refine ⟨hqc, hqf, hypSmall, hgyp, fun t ht ↦ ⟨?_, ?_⟩⟩
  · have htri := dist_triangle (φ (t, y q)) (y q) p₀
    have hd' := hdis ht
    have hp : dist (φ (t, y q)) p₀ < 3 * r := by linarith
    have hb := hgraph hp
    rw [mem_closedBall]
    nlinarith
  · have hb := trajectory_displacement_le (htF h0) (htF ht) (hD _ hgyp) (hV _ hgyp)
    rw [hI _ hgyp] at hb
    have hsmall := hb.trans (hspeed ht)
    have htri := dist_triangle (Φ (t, g (y q))) (g (y q)) (g p₀)
    rw [mem_closedBall]
    nlinarith

end Domains

open ActualCarriers FrozenMenu CurrentFullPhase

/-- The graph Lipschitz constant used in `exists_comparison_radii` is produced
from the fixed carrier reference on its compact buffer, before the current
frame or immersion. The original carrier constructor's coefficient buffer
supplies `hbuffer` (`app:ch_waves:thm:leading`). -/
theorem exists_carrierLabel_lipschitz {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (p₀ : Euclidean (n - 1) × Euclidean 3) (R : ℝ)
    (hbuffer : MapsTo Prod.snd (closedBall p₀ R) (parameterInterior (2 * P.radius))) :
    ∃ L : ℝ≥0, 1 ≤ (L : ℝ) ∧ LipschitzOnWith L (carrierLabel T) (closedBall p₀ R) := by
  have hs : ContDiffOn ℝ ∞ (carrierLabel T) (closedBall p₀ R) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk
      ((T.reference.spatialPatch_smooth hP).comp contDiffOn_snd hbuffer))
  obtain ⟨L, hL⟩ := hs.exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  exact ⟨max 1 L, by exact_mod_cast le_max_left (1 : ℝ≥0) L,
    hL.weaken (le_max_right _ _)⟩

/-- A fixed graph neighborhood and Lipschitz constant exist at every point
of the original closed carrier cube, independently of either flow radius.
Thus the common-domain comparison does not require the two constructors to
choose matching radii (`app:ch_waves:thm:leading`). -/
theorem exists_local_carrierLabel_lipschitz {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (p₀ : Euclidean (n - 1) × Euclidean 3) (hp₀ : p₀.2 ∈ parameterCube P.radius) :
    ∃ Rg : ℝ, ∃ L : ℝ≥0, 0 < Rg ∧ 1 ≤ (L : ℝ) ∧
      LipschitzOnWith L (carrierLabel T) (closedBall p₀ Rg) := by
  have hz := (T.reference.spatialPatch_smooth hP).contDiffAt
    ((isOpen_parameterInterior _).mem_nhds (parameterCube_subset_doubledInterior hP.1 hp₀))
  have hs : ContDiffAt ℝ ∞ (carrierLabel T) p₀ :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hz.comp p₀ contDiffAt_snd))
  obtain ⟨L, V, hV, hLV⟩ := (hs.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  obtain ⟨R, hR, hRV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨R / 2, max 1 L, by positivity, ?_, ?_⟩
  · exact_mod_cast le_max_left (1 : ℝ≥0) L
  · exact (hLV.mono ((closedBall_subset_ball (by linarith : R / 2 < R)).trans hRV)).weaken
      (le_max_right _ _)

end JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
