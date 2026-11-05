module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic
public import JanetCartan.Analysis.Microlocal.Localization.Gap
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A fixed normalized annular selector for elapsed graphs

The frequency-localization step of `paper-v2.tex`,
`app:ch_response:lem:energy-carrier-jets`, consumed by the complete complement
in `paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
The selector depends only on fixed positive radii, never on frequency,
coefficient scale, envelope scale, parameter, or requested accuracy.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The inner radial bump in the annular split of
`app:ch_response:lem:energy-carrier-jets`. -/
def innerAnnularBump (n : ℕ) (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : Euclidean n) :=
  ⟨a / 2, a, by positivity, by linarith⟩

/-- The outer radial bump in the same fixed normalized annular split. -/
def outerAnnularBump (n : ℕ) (b : ℝ) (hb : 0 < b) : ContDiffBump (0 : Euclidean n) :=
  ⟨b, 2 * b, hb, by linarith⟩

/-- One fixed real-valued smooth annular selector, with plateau `[a,b]`.
Source: the frequency localization preceding `new:eq:carrier-ibp`. -/
def annularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ : E) : ℝ :=
  (1 - innerAnnularBump n a ha ξ) * outerAnnularBump n b hb ξ

/-- Smoothness of the actual normalized selector. -/
theorem contDiff_annularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ∞ (annularSelector (n := n) a b ha hb) :=
  (contDiff_const.sub (innerAnnularBump n a ha).contDiff).mul
    (outerAnnularBump n b hb).contDiff

/-- Both the selector and its complement are bounded by one, uniformly before
choosing frequency or accuracy (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSelector_mem_Icc (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ : E) :
    annularSelector a b ha hb ξ ∈ Icc (0 : ℝ) 1 := by
  have hi := (innerAnnularBump n a ha).nonneg (x := ξ)
  have hi' := (innerAnnularBump n a ha).le_one (x := ξ)
  have ho := (outerAnnularBump n b hb).nonneg (x := ξ)
  have ho' := (outerAnnularBump n b hb).le_one (x := ξ)
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hi') ho
  · exact (mul_le_mul_of_nonneg_right (show 1 - innerAnnularBump n a ha ξ ≤ 1 by linarith) ho).trans (by simpa using ho')

/-- Exact plateau, including both boundary spheres, for the annular selector. -/
theorem annularSelector_eq_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {ξ : E} (hl : a ≤ ‖ξ‖) (hu : ‖ξ‖ ≤ b) :
    annularSelector a b ha hb ξ = 1 := by
  have hi := (innerAnnularBump n a ha).zero_of_le_dist (x := ξ)
    (by simpa [innerAnnularBump] using hl)
  have ho := (outerAnnularBump n b hb).one_of_mem_closedBall (x := ξ)
    (by simpa [outerAnnularBump] using hu)
  simp [annularSelector, hi, ho]

/-- The complete annular support avoids zero and is bounded. Neither shoulder
is omitted (`app:ch_response:lem:energy-carrier-jets`). -/
theorem tsupport_annularSelector_subset (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tsupport (annularSelector (n := n) a b ha hb) ⊆
      {ξ | a / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * b} := by
  apply closure_minimal
  · intro ξ hξ
    constructor
    · by_contra! h
      have hi := (innerAnnularBump n a ha).one_of_mem_closedBall (x := ξ)
        (by simpa [innerAnnularBump] using h.le)
      exact hξ (by simp [annularSelector, hi])
    · by_contra! h
      have ho := (outerAnnularBump n b hb).zero_of_le_dist (x := ξ)
        (by simpa [outerAnnularBump] using h.le)
      exact hξ (by simp [annularSelector, ho])
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

/-- Compactness of the fixed selector, for the actual graph regularizations. -/
theorem hasCompactSupport_annularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (annularSelector (n := n) a b ha hb) := by
  apply (isCompact_closedBall (0 : E) (2 * b)).of_isClosed_subset (isClosed_tsupport _)
  intro ξ hξ
  simpa using (tsupport_annularSelector_subset a b ha hb hξ).2

/-- The selector is one on a neighborhood of each covector strictly inside
its plateau; this is the literal "one near every carrier" condition. -/
theorem annularSelector_eventuallyEq_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {ξ : E} (hl : a < ‖ξ‖) (hu : ‖ξ‖ < b) :
    annularSelector a b ha hb =ᶠ[𝓝 ξ] (fun _ => 1) := by
  filter_upwards [continuous_norm.continuousAt.eventually (Ioo_mem_nhds hl hu)] with η hη
  exact annularSelector_eq_one a b ha hb hη.1.le hη.2.le

/-- The complement is supported outside the full plateau, including its
boundary. This conclusion also applies on the topological support of jets. -/
theorem tsupport_one_sub_annularSelector_subset (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tsupport (fun ξ : E => 1 - annularSelector a b ha hb ξ) ⊆
      {ξ | ‖ξ‖ ≤ a ∨ b ≤ ‖ξ‖} := by
  apply closure_minimal
  · intro ξ hξ
    change ‖ξ‖ ≤ a ∨ b ≤ ‖ξ‖
    by_contra! h
    exact hξ (by simp only [annularSelector_eq_one a b ha hb h.1.le h.2.le, sub_self])
  · exact (isClosed_le continuous_norm continuous_const).union
      (isClosed_le continuous_const continuous_norm)

/-- The same selector evaluated at the normalized physical covector. Its
frequency and radii are fixed during parameter differentiation. -/
def physicalAnnularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) (ξ : E) : ℂ := annularSelector a b ha hb (lam⁻¹ • ξ)

/-- Smoothness of the literal amplitude multiplier `π(ξ/λ)`. -/
theorem contDiff_physicalAnnularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) : ContDiff ℝ ∞ (physicalAnnularSelector (n := n) a b ha hb lam) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_annularSelector a b ha hb).comp (contDiff_id.const_smul lam⁻¹))

/-- The physical selector has a frequency-independent bound of one. -/
theorem norm_physicalAnnularSelector_le_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) (ξ : E) : ‖physicalAnnularSelector a b ha hb lam ξ‖ ≤ 1 := by
  have h := annularSelector_mem_Icc a b ha hb (lam⁻¹ • ξ)
  simpa [physicalAnnularSelector, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h.1] using h.2

/-- Compact frequency support follows from the constructed selector; it is
not an extra realization hypothesis. -/
theorem hasCompactSupport_physicalAnnularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {lam : ℝ} (hlam : 0 < lam) :
    HasCompactSupport (physicalAnnularSelector (n := n) a b ha hb lam) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * b * lam))
  intro ξ hξ
  have hξ' : 2 * b * lam < ‖ξ‖ := by simpa using hξ
  have hout : lam⁻¹ • ξ ∉ tsupport (annularSelector a b ha hb) := by
    intro h
    have hu := (tsupport_annularSelector_subset a b ha hb h).2
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hu
    have ht := (inv_mul_le_iff₀ hlam).mp hu
    linarith
  simp only [physicalAnnularSelector, image_eq_zero_of_notMem_tsupport hout,
    Complex.ofReal_zero]

/-- The fixed selector is real, so adjunction leaves it unchanged while
conjugating all original complex amplitude factors. -/
theorem star_physicalAnnularSelector (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (lam : ℝ) (ξ : E) : star (physicalAnnularSelector a b ha hb lam ξ) =
      physicalAnnularSelector a b ha hb lam ξ := by
  simp [physicalAnnularSelector]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
