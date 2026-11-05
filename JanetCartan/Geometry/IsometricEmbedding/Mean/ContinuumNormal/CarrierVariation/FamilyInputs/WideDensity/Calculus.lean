module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity.InverseEvaluations

/-!
# Uniform composition for the original density class

The density class in `paper.tex`, `app:ch_background:prop:bg-frame`, has
`1/2 ≤ 1 + v ≤ 3/2` and a fixed low derivative bound. It need not be a small
neighborhood of zero. The constants below precede `v`. The extra derivative
controls displacement of the density jets between the two actual ODE
footpoints. Consumer: `WideDensity.Canonical` and the original normalized
comparison in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open AmplitudeDifference AmplitudeDifference.PrimitiveDensity
open HamiltonPhase.CompositionContinuity

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform finite norms and differences for an initial density evaluated at
moving ODE labels. The only difference assumption concerns the labels, and
`v` has the original fixed low budget, not a smallness budget. Source:
`app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`. -/
theorem exists_density_evaluation_bounds
    {K : Set E} {L : Set F} (hK : IsCompact K) (hL : IsCompact L)
    (hconv : Convex ℝ L) (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (v : F → ℝ) (g g₀ : E → F) (d : ℝ), 0 ≤ d →
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L (s + 1) v ≤ 1 →
      (∀ x ∈ K, ContDiffAt ℝ ∞ g x) →
      (∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x) →
      MapsTo g K L → MapsTo g₀ K L → cNorm K s g ≤ B → cNorm K s g₀ ≤ B →
      cNorm K s (g - g₀) ≤ d →
      (∀ x ∈ K, ContDiffAt ℝ ∞ (v ∘ g) x ∧ ContDiffAt ℝ ∞ (v ∘ g₀) x) ∧
      cNorm K s (v ∘ g) ≤ C ∧ cNorm K s (v ∘ g₀) ≤ C ∧
      cNorm K s (v ∘ g - v ∘ g₀) ≤ C * d := by
  let A := compositionMultiplicity s * (1 + B) ^ s
  let D := jetDifferenceConstant s 1 B * (1 + 1)
  have hA : 0 ≤ A := by dsimp [A, compositionMultiplicity]; positivity
  have hD : 0 ≤ D := mul_nonneg (jetDifferenceConstant_nonneg s zero_le_one hB) (by norm_num)
  refine ⟨1 + A + D, by positivity, ?_⟩
  intro v g g₀ d hd hv hvnorm hg hg₀ hr hr₀ hm hm₀ hdiff
  have hvlow : cNorm L s v ≤ 1 := (cNorm_mono_order (Nat.le_succ s)).trans hvnorm
  refine ⟨fun x hx ↦ ⟨(hv _ (hr hx)).comp x (hg x hx),
    (hv _ (hr₀ hx)).comp x (hg₀ x hx)⟩, ?_, ?_, ?_⟩
  · exact (cNorm_comp_le_from_bounds hK hL s hv hg hr zero_le_one hvlow hm).trans
      (by change compositionMultiplicity s * 1 * (1 + B) ^ s ≤ _; dsimp [A]; nlinarith)
  · exact (cNorm_comp_le_from_bounds hK hL s hv hg₀ hr₀ zero_le_one hvlow hm₀).trans
      (by change compositionMultiplicity s * 1 * (1 + B) ^ s ≤ _; dsimp [A]; nlinarith)
  · exact (cNorm_comp_sub_le_common_bounds hK hL hconv s zero_le_one hB hd
      hv hv hg hg₀ hr hr₀ hvnorm hm hm₀
      (by simpa only [sub_self, cNorm_zero] using hd) hdiff).trans
        (mul_le_mul_of_nonneg_right (by change D ≤ _; linarith) hd)

/-- Both physical density factors, before or after inverse substitution.
The two maps must be the actual left and right ODE footpoints at the call
site. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
def densityPair (v : F → ℝ) (g : Bool → E → F) (p : E) : ℝ :=
  (1 + v (g false p)) * (1 + v (g true p))

/-- Finite-order comparison of BOTH density factors, uniform over the original
fixed-low class. No smallness of `v` or continuity of a composed density is
assumed. The constant is chosen before density and both pairs of footpoints.
Consumer: the literal canonical density in `WideDensity.Canonical`. Source:
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`. -/
theorem exists_densityPair_sub_bound
    {K : Set E} {L : Set F} (hK : IsCompact K) (hL : IsCompact L)
    (hconv : Convex ℝ L) (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (v : F → ℝ) (g g₀ : Bool → E → F) (d : ℝ), 0 ≤ d →
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L (s + 1) v ≤ 1 →
      (∀ b x, x ∈ K → ContDiffAt ℝ ∞ (g b) x) →
      (∀ b x, x ∈ K → ContDiffAt ℝ ∞ (g₀ b) x) →
      (∀ b, MapsTo (g b) K L) → (∀ b, MapsTo (g₀ b) K L) →
      (∀ b, cNorm K s (g b) ≤ B) → (∀ b, cNorm K s (g₀ b) ≤ B) →
      (∀ b, cNorm K s (g b - g₀ b) ≤ d) →
      (∀ x ∈ K, ContDiffAt ℝ ∞ (densityPair v g) x ∧
        ContDiffAt ℝ ∞ (densityPair v g₀) x) ∧
      cNorm K s (densityPair v g) ≤ C ∧ cNorm K s (densityPair v g₀) ≤ C ∧
      cNorm K s (densityPair v g - densityPair v g₀) ≤ C * d := by
  obtain ⟨A, hA, heval⟩ := exists_density_evaluation_bounds hK hL hconv s hB
  let H : ℝ × ℝ → ℝ := fun p ↦ (1 + p.1) * (1 + p.2)
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_const.add contDiff_fst).mul (contDiff_const.add contDiff_snd)
  obtain ⟨D, hD, hfixed⟩ := exists_fixed_evaluation_bounds hK
    (isCompact_closedBall (0 : ℝ × ℝ) (A + A))
    (fun _ _ ↦ hH.contDiffAt) s (add_nonneg hA.le hA.le)
  refine ⟨1 + D + D * (A + A), by positivity, ?_⟩
  intro v g g₀ d hd hv hvm hg hg₀ hr hr₀ hm hm₀ hdiff
  have he (b : Bool) := heval v (g b) (g₀ b) d hd hv hvm
    (hg b) (hg₀ b) (hr b) (hr₀ b) (hm b) (hm₀ b) (hdiff b)
  have hp := pair_evaluation_bounds hK s (he false) (he true)
  let a : E → ℝ × ℝ := fun x ↦ (v (g false x), v (g true x))
  let a₀ : E → ℝ × ℝ := fun x ↦ (v (g₀ false x), v (g₀ true x))
  have har : MapsTo a K (closedBall 0 (A + A)) := by
    intro x hx
    have hh := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hp.1 y hy).1.of_le (by simp)) hx (Nat.zero_le s)).trans hp.2.1
    simpa only [mem_closedBall, dist_zero_right, norm_iteratedFDeriv_zero, a,
      Function.comp_def] using hh
  have har₀ : MapsTo a₀ K (closedBall 0 (A + A)) := by
    intro x hx
    have hh := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hp.1 y hy).2.of_le (by simp)) hx (Nat.zero_le s)).trans hp.2.2.1
    simpa only [mem_closedBall, dist_zero_right, norm_iteratedFDeriv_zero, a₀,
      Function.comp_def] using hh
  have hb := hfixed a a₀ ((A + A) * d) (by positivity)
    (fun x hx ↦ (hp.1 x hx).1) (fun x hx ↦ (hp.1 x hx).2)
    har har₀ hp.2.1 hp.2.2.1 hp.2.2.2
  change (∀ x ∈ K, ContDiffAt ℝ ∞ (densityPair v g) x ∧
    ContDiffAt ℝ ∞ (densityPair v g₀) x) ∧
    cNorm K s (densityPair v g) ≤ D ∧ cNorm K s (densityPair v g₀) ≤ D ∧
    cNorm K s (densityPair v g - densityPair v g₀) ≤ D * ((A + A) * d) at hb
  exact ⟨hb.1, hb.2.1.trans (by nlinarith), hb.2.2.1.trans (by nlinarith),
    hb.2.2.2.trans (by nlinarith)⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
