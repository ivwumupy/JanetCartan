module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.EnvelopeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.ShellLoss
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Concrete shell data for the original source

Leibniz's rule and the actual Sobolev envelope give the amplitude jets required
by `app:ch_osc:prop:osc-source-shell`. The fixed loss `n + 1` is absorbed only
in the tail, for the original-source estimate preceding
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.SourceNegative

/-- The finite Leibniz profile for the cutoff envelope in
`app:ch_response:prop:response-graded`; it is independent of all scales. -/
def cutoffEnvelopeJetConstant (n : ℕ) (X C : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * X i *
    (envelopeJetConstant n (r - i) * C (r - i + (n + 1)))

/-- Nonnegativity of the amplitude profile used in the original-source shell
of `app:ch_response:prop:response-graded`. -/
theorem cutoffEnvelopeJetConstant_nonneg (n : ℕ) {X C : ℕ → ℝ}
    (hX : ∀ i, 0 ≤ X i) (hC : ∀ i, 0 ≤ C i) (r : ℕ) :
    0 ≤ cutoffEnvelopeJetConstant n X C r := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hX i))
    (mul_nonneg (envelopeJetConstant_nonneg _ _) (hC _))

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Derive the cutoff-product jets from the actual Fourier Sobolev envelope,
for the original-source estimate in `app:ch_response:prop:response-graded`. -/
theorem norm_iteratedFDeriv_cutoff_envelope_le
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (hLK : L ≤ K) (r : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ r (fun y ↦ χ y • f y) x‖ ≤
      cutoffEnvelopeJetConstant n X C r * (A * K ^ ((r : ℝ) + (n + 1))) := by
  have hK : 0 ≤ K := le_trans zero_le_one h.scale_one_le
  have hL : 0 ≤ L := le_trans zero_le_one g.scale_one_le
  have hb (i : ℕ) : ‖iteratedFDeriv ℝ i χ x‖ ≤ X i * K ^ i :=
    (g.cutoff_derivatives x i).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLK _) (g.cutoff_constants_nonneg i))
  have he : K ^ ((r : ℝ) + (n + 1)) = K ^ (r + (n + 1)) := by
    norm_cast
  rw [he, cutoffEnvelopeJetConstant, Finset.sum_mul]
  apply (norm_iteratedFDeriv_smul_le g.cutoff_smooth h.smooth x (by simp)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hchoose : 0 ≤ (r.choose i : ℝ) := Nat.cast_nonneg _
  have hcut : 0 ≤ X i * K ^ i := mul_nonneg (g.cutoff_constants_nonneg i) (by positivity)
  calc
    _ ≤ (r.choose i : ℝ) * (X i * K ^ i) *
        ‖iteratedFDeriv ℝ (r - i) f x‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb i) hchoose) (norm_nonneg _)
    _ ≤ (r.choose i : ℝ) * (X i * K ^ i) *
        (envelopeJetConstant n (r - i) * C (r - i + (n + 1)) * A *
          K ^ (r - i + (n + 1))) := by
      apply mul_le_mul_of_nonneg_left (h.norm_iteratedFDeriv_le (r - i) x)
      exact mul_nonneg hchoose hcut
    _ = _ := by
      have hp : K ^ i * K ^ (r - i + (n + 1)) = K ^ (r + (n + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = ((r.choose i : ℝ) * X i *
            (envelopeJetConstant n (r - i) * C (r - i + (n + 1)))) * A *
            (K ^ i * K ^ (r - i + (n + 1))) := by ring
        _ = _ := by rw [hp]; ring

/-- The original cutoff envelope supplies every shell hypothesis. The open
phase domain is obtained from continuity, with constants `c/2` and `2G`,
so only the given gradient bounds on the full compact support are assumed
(`app:ch_response:prop:response-graded`). -/
theorem sourceGeometry_shellBounds
    {χ φ : Euclidean n → ℝ} {S : Set (Euclidean n)}
    {c G L : ℝ} {P X : ℕ → ℝ} (g : SourceGeometry χ φ S c G L P X)
    {f : Euclidean n → F} {hf : MemLp f 2 volume} {A K : ℝ} {C : ℕ → ℝ}
    (h : SobolevEnvelopeBounds f hf A K C) (hLK : L ≤ K) :
    Localization.SourceShellBounds (fun _ : Unit ↦ φ) (fun _ : Unit ↦ fun x ↦ χ x • f x)
      {x | c / 2 < ‖fderiv ℝ φ x‖ ∧ ‖fderiv ℝ φ x‖ < 2 * G}
      S (c / 2) (2 * G) A K (n + 1) P (cutoffEnvelopeJetConstant n X C) := by
  have hd : Continuous (fun x ↦ ‖fderiv ℝ φ x‖) :=
    (g.phase_smooth.continuous_fderiv (by simp)).norm
  have hs : tsupport (fun x ↦ χ x • f x) ⊆ S :=
    (tsupport_smul_subset_left _ _).trans g.support_subset
  refine {
    open_domain := (isOpen_lt continuous_const hd).inter (isOpen_lt hd continuous_const)
    compact_support := g.compact
    support_subset := ?_
    phase_measurable := g.phase_smooth.continuous.measurable.comp measurable_snd
    amplitude_measurable := (g.cutoff_smooth.continuous.smul h.smooth.continuous).stronglyMeasurable.comp_measurable measurable_snd
    phase_smooth := fun _ ↦ g.phase_smooth.contDiffOn
    amplitude_smooth := fun _ ↦ (g.cutoff_smooth.smul h.smooth).contDiffOn
    amplitude_support := fun _ ↦ hs
    lower_pos := by linarith [g.lower_pos]
    lower_lt_upper := by linarith [g.lower_pos, g.lower_lt_upper]
    amplitude_nonneg := h.amplitude_nonneg
    scale_one_le := h.scale_one_le
    loss_nonneg := by positivity
    phase_constants_nonneg := g.phase_constants_nonneg
    amplitude_constants_nonneg := cutoffEnvelopeJetConstant_nonneg n g.cutoff_constants_nonneg h.constants_nonneg
    gradient_lower := fun _ _ hx ↦ hx.1.le
    gradient_upper := fun _ _ hx ↦ hx.2.le
    phase_derivatives := ?_
    amplitude_derivatives := fun _ x _ r ↦ norm_iteratedFDeriv_cutoff_envelope_le g h hLK r x }
  · intro x hx
    constructor
    · linarith [g.gradient_lower x hx, g.lower_pos]
    · linarith [g.gradient_upper x hx, g.lower_pos, g.lower_lt_upper]
  · intro _ x hx j hj
    exact (g.phase_derivatives x (hs hx) j hj).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_trans zero_le_one g.scale_one_le) hLK j)
        (g.phase_constants_nonneg j))

end JanetCartan.ResponseTransfer.SourceNegative
