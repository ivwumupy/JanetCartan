module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.Selector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel

/-!
# Full radial source gaps for the actual elapsed phase

The complement in `app:ch_response:lem:energy-carrier-jets` uses the original
nonlinear source carrier. Its forward derivative is `λ dφ(z) - ξ`; its literal
adjoint derivative is `λ dφ(z) - D_z Θ(z,ξ)`.

The carrier bounds come from the actual supported compatible phase. The radial
comparison for `D_z Θ` must come from the same small-time two-time Hamilton
phase and supported chart (`EvolutionIntegral.Geometry` and its sector
instantiation), on every original supported frequency. Homogeneity and a
normalized derivative comparison may supply it; no comparison at spatial
frequency zero follows merely from nonzero spacetime frequency.

These deductions use only that precise radial comparison, not an inverse
chart or an assumed complementary estimate. They cover the entire exterior
of one annulus, including bounded frequencies and both shoulders.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Forward source phase of the unchanged graph applied to its original
nonlinear carrier (`app:ch_response:lem:energy-carrier-jets`). -/
def forwardCarrierSourcePhase (Θ : E → E → ℝ) (φ : E → ℝ)
    (lam : ℝ) (x ξ z : E) : ℝ := Θ x ξ - inner ℝ z ξ + lam * φ z

/-- Literal reversed phase: the graph phase is evaluated at the integration
position. Source: the adjoint localization in the same lemma. -/
def adjointCarrierSourcePhase (Θ : E → E → ℝ) (φ : E → ℝ)
    (lam : ℝ) (x ξ z : E) : ℝ := inner ℝ x ξ - Θ z ξ + lam * φ z

/-- Exact physical forward oscillation; no multiplier is commuted through a
source-position amplitude. -/
theorem phaseOscillation_forwardCarrierSourcePhase (Θ : E → E → ℝ)
    (φ : E → ℝ) (lam : ℝ) (x ξ z : E) :
    phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z =
      graphOscillation Θ x z ξ * carrier lam φ z := by
  simp only [phaseOscillation, forwardCarrierSourcePhase, graphOscillation, carrier,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact conjugation in the reversed oscillation, with its original graph. -/
theorem phaseOscillation_adjointCarrierSourcePhase (Θ : E → E → ℝ)
    (φ : E → ℝ) (lam : ℝ) (x ξ z : E) :
    phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z =
      star (graphOscillation Θ z x ξ) * carrier lam φ z := by
  simp only [phaseOscillation, adjointCarrierSourcePhase, graphOscillation, carrier,
    Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Source differentiation of the forward elapsed kernel is precisely the
physical covector `λ dφ - ξ`, also for nonlinear carriers. -/
theorem fderiv_forwardCarrierSourcePhase (Θ : E → E → ℝ)
    (φ : E → ℝ) (lam : ℝ) (x ξ z : E) (hφ : DifferentiableAt ℝ φ z) :
    fderiv ℝ (forwardCarrierSourcePhase Θ φ lam x ξ) z =
      lam • fderiv ℝ φ z - InnerProductSpace.toDual ℝ E ξ := by
  have hlin := (InnerProductSpace.toDual ℝ E ξ).hasFDerivAt (x := z)
  have h := ((hasFDerivAt_const (Θ x ξ) z).sub hlin).add (hφ.hasFDerivAt.const_mul lam)
  have he : forwardCarrierSourcePhase Θ φ lam x ξ =
      ((fun _ => Θ x ξ) - (InnerProductSpace.toDual ℝ E ξ : E → ℝ)) +
        (fun y => lam * φ y) := by
    funext y
    simp [forwardCarrierSourcePhase, real_inner_comm]
  rw [he, h.fderiv]
  simp [sub_eq_add_neg, add_comm]

/-- Source differentiation in the literal adjoint retains `D_z Θ(z,ξ)`. -/
theorem fderiv_adjointCarrierSourcePhase (Θ : E → E → ℝ)
    (φ : E → ℝ) (lam : ℝ) (x ξ z : E)
    (hφ : DifferentiableAt ℝ φ z) (hΘ : DifferentiableAt ℝ (fun y => Θ y ξ) z) :
    fderiv ℝ (adjointCarrierSourcePhase Θ φ lam x ξ) z =
      lam • fderiv ℝ φ z - fderiv ℝ (fun y => Θ y ξ) z := by
  have h := ((hasFDerivAt_const (inner ℝ x ξ) z).sub hΘ.hasFDerivAt).add
    (hφ.hasFDerivAt.const_mul lam)
  have he : adjointCarrierSourcePhase Θ φ lam x ξ =
      ((fun _ => inner ℝ x ξ) - (fun y => Θ y ξ)) + (fun y => lam * φ y) := rfl
  rw [he, h.fderiv]
  simp [sub_eq_add_neg, add_comm]

/-- A primitive half-size comparison of the actual physical derivative with
identity supplies the radial bounds used below. The small-time phase producer
must establish this premise on its original supported chart. -/
theorem radial_bounds_of_half_identity_gap (Θ : E → E → ℝ) (z ξ : E)
    (h : ‖fderiv ℝ (fun y => Θ y ξ) z - InnerProductSpace.toDual ℝ E ξ‖ ≤ ‖ξ‖ / 2) :
    (1 / 2 : ℝ) * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => Θ y ξ) z‖ ∧
      ‖fderiv ℝ (fun y => Θ y ξ) z‖ ≤ (3 / 2 : ℝ) * ‖ξ‖ := by
  have hl := norm_sub_norm_le (InnerProductSpace.toDual ℝ E ξ)
    (fderiv ℝ (fun y => Θ y ξ) z)
  have hu := norm_sub_norm_le (fderiv ℝ (fun y => Θ y ξ) z)
    (InnerProductSpace.toDual ℝ E ξ)
  rw [norm_sub_rev] at hl
  simp only [LinearIsometryEquiv.norm_map] at hl hu
  constructor <;> linarith

/-- Uniform full-frequency gap for any covector satisfying the actual graph's
radial comparison. The same selector works for the identity covector in the
forward graph and for `D_z Θ` in its adjoint. The constant and radii precede
frequency, parameters and accuracy (`app:ch_response:lem:energy-carrier-jets`). -/
theorem source_gap_of_annularSelector
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b m M lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM : 0 < M) (hlam : 0 < lam)
    {g v : F} {ξ : E} (hgl : a ≤ ‖g‖) (hgu : ‖g‖ ≤ b)
    (hvl : m * ‖ξ‖ ≤ ‖v‖) (hvu : ‖v‖ ≤ M * ‖ξ‖)
    (hfar : 1 - annularSelector (a / (2 * M)) (2 * b / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0) :
    (radialGapConstant a b * m) * (lam + ‖ξ‖) ≤ ‖lam • g - v‖ := by
  have hξ := tsupport_one_sub_annularSelector_subset (n := n)
    (a / (2 * M)) (2 * b / m) (by positivity) (by positivity)
    (subset_closure hfar)
  have hn : ‖lam⁻¹ • ξ‖ = ‖ξ‖ / lam := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  change ‖lam⁻¹ • ξ‖ ≤ a / (2 * M) ∨ 2 * b / m ≤ ‖lam⁻¹ • ξ‖ at hξ
  rw [hn] at hξ
  have hvfar : ‖v‖ ≤ a * lam / 2 ∨ 2 * b * lam ≤ ‖v‖ := by
    rcases hξ with hl | hu
    · left
      have hl' := (div_le_iff₀ hlam).mp hl
      have ht := mul_le_mul_of_nonneg_left hl' hM.le
      have he : M * (a / (2 * M) * lam) = a * lam / 2 := by field_simp
      rw [he] at ht
      exact hvu.trans ht
    · right
      have hu' := (le_div_iff₀ hlam).mp hu
      have ht := mul_le_mul_of_nonneg_left hu' hm.le
      have he : m * (2 * b / m * lam) = 2 * b * lam := by field_simp
      rw [he] at ht
      exact ht.trans hvl
  have hgap := radial_frequency_gap ha hb hlam.le hgl hgu hvfar
  have hscale : m * (lam + ‖ξ‖) ≤ lam + ‖v‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hm1 hlam.le]
  have hd := (radialGapConstant_pos ha hb).le
  exact (show (radialGapConstant a b * m) * (lam + ‖ξ‖) ≤
    radialGapConstant a b * (lam + ‖v‖) by nlinarith [mul_le_mul_of_nonneg_left hscale hd]).trans hgap

/-- Every carrier between the primitive positive bounds lies strictly inside
this SAME selector's plateau. Thus one selector is one near the full supported
carrier family, uniformly in all its indices. -/
theorem common_annularSelector_eventuallyEq_one
    {a b m M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    {ξ : E} (hl : a ≤ ‖ξ‖) (hu : ‖ξ‖ ≤ b) :
    annularSelector (a / (2 * M)) (2 * b / m)
      (by positivity) (by positivity) =ᶠ[𝓝 ξ] (fun _ => 1) := by
  apply annularSelector_eventuallyEq_one
  · apply lt_of_lt_of_le _ hl
    apply (div_lt_iff₀ (by positivity : 0 < 2 * M)).mpr
    nlinarith
  · apply lt_of_le_of_lt hu
    apply (lt_div_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hm1 hb.le]

/-- Forward derivative gap outside the fixed normalized annulus, including
zero and every high-pass transition. Source: the complete complement of
`app:ch_response:lem:energy-carrier-jets`. -/
theorem forwardCarrierSourcePhase_gap (Θ : E → E → ℝ) (φ : E → ℝ)
    {a b m M lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M) (hlam : 0 < lam)
    (x ξ z : E) (hφ : DifferentiableAt ℝ φ z)
    (hl : a ≤ ‖fderiv ℝ φ z‖) (hu : ‖fderiv ℝ φ z‖ ≤ b)
    (hfar : 1 - annularSelector (a / (2 * M)) (2 * b / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0) :
    (radialGapConstant a b * m) * (lam + ‖ξ‖) ≤
      ‖fderiv ℝ (forwardCarrierSourcePhase Θ φ lam x ξ) z‖ := by
  rw [fderiv_forwardCarrierSourcePhase Θ φ lam x ξ z hφ]
  apply source_gap_of_annularSelector ha hb hm hm1 (by positivity) hlam hl hu
    (v := InnerProductSpace.toDual ℝ E ξ) (ξ := ξ) _ _ hfar
  · simpa using mul_le_mul_of_nonneg_right hm1 (norm_nonneg ξ)
  · simpa using mul_le_mul_of_nonneg_right hM1 (norm_nonneg ξ)

/-- Literal-adjoint derivative gap on the same selector. The extra hypotheses
are precisely radial comparisons for the original phase, supplied by the
small-time supported chart, not a remainder estimate or a phase increment. -/
theorem adjointCarrierSourcePhase_gap (Θ : E → E → ℝ) (φ : E → ℝ)
    {a b m M lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM : 0 < M) (hlam : 0 < lam)
    (x ξ z : E) (hφ : DifferentiableAt ℝ φ z)
    (hΘ : DifferentiableAt ℝ (fun y => Θ y ξ) z)
    (hl : a ≤ ‖fderiv ℝ φ z‖) (hu : ‖fderiv ℝ φ z‖ ≤ b)
    (hvl : m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => Θ y ξ) z‖)
    (hvu : ‖fderiv ℝ (fun y => Θ y ξ) z‖ ≤ M * ‖ξ‖)
    (hfar : 1 - annularSelector (a / (2 * M)) (2 * b / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0) :
    (radialGapConstant a b * m) * (lam + ‖ξ‖) ≤
      ‖fderiv ℝ (adjointCarrierSourcePhase Θ φ lam x ξ) z‖ := by
  rw [fderiv_adjointCarrierSourcePhase Θ φ lam x ξ z hφ hΘ]
  exact source_gap_of_annularSelector ha hb hm hm1 hM hlam hl hu hvl hvu hfar

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
