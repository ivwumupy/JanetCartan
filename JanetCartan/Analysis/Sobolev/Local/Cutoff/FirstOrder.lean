module

public import JanetCartan.Analysis.Sobolev.Local.Cutoff.Product
public import JanetCartan.Analysis.Sobolev.Local.Scale.Algebra

/-!
# First-order weak cutoff extensions

The first-order endpoint of `app:ch_regular:eq:one-gain-tame`, constructed
from the actual weak jet of each extension and then its infimum norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped ContDiff

set_option maxHeartbeats 600000

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The order-one product jet for `app:ch_regular:eq:one-gain-tame`.
Its first derivative is the actual weak Leibniz derivative; unused orders
are zero. -/
def cutoffFirstJet (χ : E → ℝ) (J : (j : ℕ) → E → E [×j]→L[ℝ] F) :
    (j : ℕ) → E → E [×j]→L[ℝ] F
  | 0 => fun x ↦ χ x • J 0 x
  | 1 => fun x ↦ (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 ↦ E) F).symm
      ((fderiv ℝ χ x).smulRight (J 0 x) + χ x •
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 ↦ E) F) (J 1 x))
  | _ + 2 => fun _ ↦ 0

/-- The finite product jet really satisfies the weak identities through
order one (`app:ch_regular:eq:one-gain-tame`). -/
theorem hasWeakJetOn_cutoffFirstJet {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F}
    (hw : Mollification.HasWeakJetOn volume f J univ 1)
    (hJ : ∀ j ≤ 1, MemLp (J j) 2 volume)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {B₀ B₁ : ℝ} (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ B₁) :
    Mollification.HasWeakJetOn volume (fun x ↦ χ x • f x) (cutoffFirstJet χ J) univ 1 := by
  refine ⟨?_, ?_⟩
  · ext x v
    simp [cutoffFirstJet, hw.1, iteratedFDeriv_zero_apply]
  · intro j hj
    have : j = 0 := by omega
    subst j
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 ↦ E) F
    have hD : MemLp (L ∘ J 1) 2 volume :=
      (hJ 1 le_rfl).of_le_enorm
        (L.continuous.comp_aestronglyMeasurable (hJ 1 le_rfl).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ (L.enorm_map (J 1 x)).le)
    simpa only [cutoffFirstJet, comp_def, LinearIsometryEquiv.apply_symm_apply] using
      (hw.2 0 (by omega)).smooth_smul_univ (hJ 0 (by omega)) hD hχ hB₀ hB₁

/-- Every component of the first product jet is L²
(`app:ch_regular:eq:one-gain-tame`). -/
theorem memLp_cutoffFirstJet
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F}
    (hJ : ∀ j ≤ 1, MemLp (J j) 2 volume)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {B₀ B₁ : ℝ} (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ B₁)
    (j : ℕ) : MemLp (cutoffFirstJet χ J j) 2 volume := by
  rcases j with _ | (_ | j)
  · exact memLp_bounded_smul (hJ 0 (by omega)) hχ.continuous hB₀
  · let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 ↦ E) F
    have hD : MemLp (L ∘ J 1) 2 volume :=
      (hJ 1 le_rfl).of_le_enorm
        (L.continuous.comp_aestronglyMeasurable (hJ 1 le_rfl).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ (L.enorm_map (J 1 x)).le)
    have hsum := (memLp_bounded_smulRight (hJ 0 (by omega))
      (hχ.continuous_fderiv (by simp)) hB₁).add
      (memLp_bounded_smul hD hχ.continuous hB₀)
    exact hsum.of_le_enorm
      (L.symm.continuous.comp_aestronglyMeasurable hsum.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ (L.symm.enorm_map _).le)
  · exact MemLp.zero' (ε := E [×(j + 2)]→L[ℝ] F)

namespace SobolevExtension

variable {U V : Set (EuclideanSpace ℝ (Fin n))} {u : LocalL2 U F} {v : LocalL2 V F}

/-- Cut off a genuine extension, retaining the exact prescribed L² output
class. The a.e. premise merely identifies that class, rather than supplying
any regularity (`app:ch_regular:thm:exact-correction`). -/
def cutoffFirst (e : SobolevExtension U 1 u)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {B₀ B₁ : ℝ} (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ B₁)
    (hv : (fun x ↦ χ x • e.toFun x) =ᵐ[volume.restrict V] v) : SobolevExtension V 1 v where
  toFun := fun x ↦ χ x • e.toFun x
  jet := cutoffFirstJet χ e.jet
  weakJet := hasWeakJetOn_cutoffFirstJet e.weakJet e.memLp_jet hχ hB₀ hB₁
  memLp_fun := memLp_bounded_smul e.memLp_fun hχ.continuous hB₀
  memLp_jet := fun j _ ↦ memLp_cutoffFirstJet e.memLp_jet hχ hB₀ hB₁ j
  restrict_eq := hv

/-- The first-order extension bound depends only on the fixed cutoff's
value and first-derivative bounds (`app:ch_regular:eq:one-gain-tame`). -/
theorem jetNorm_cutoffFirst_le (e : SobolevExtension U 1 u)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {B₀ B₁ : ℝ} (h₀ : 0 ≤ B₀) (h₁ : 0 ≤ B₁)
    (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ B₁)
    (hv : (fun x ↦ χ x • e.toFun x) =ᵐ[volume.restrict V] v) :
    (e.cutoffFirst hχ hB₀ hB₁ hv).jetNorm ≤ (B₀ + B₁) * e.jetNorm := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 ↦ E) F
  let A := fun x ↦ (fderiv ℝ χ x).smulRight (e.jet 0 x)
  let B := fun x ↦ χ x • L (e.jet 1 x)
  have hA := memLp_bounded_smulRight (e.memLp_jet 0 (by omega))
    (hχ.continuous_fderiv (by simp)) hB₁
  have hD : MemLp (L ∘ e.jet 1) 2 volume :=
    (e.memLp_jet 1 le_rfl).of_le_enorm
      (L.continuous.comp_aestronglyMeasurable (e.memLp_jet 1 le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ (L.enorm_map _).le)
  have hB : MemLp B 2 volume := memLp_bounded_smul
    (F := E →L[ℝ] E [×0]→L[ℝ] F) hD hχ.continuous hB₀
  have hzero : (eLpNorm (cutoffFirstJet χ e.jet 0) 2 volume).toReal ≤
      B₀ * (eLpNorm (e.jet 0) 2 volume).toReal := by
    apply eLpNorm_toReal_le_mul_of_bound
      (memLp_cutoffFirstJet e.memLp_jet hχ hB₀ hB₁ 0).aestronglyMeasurable
      (e.memLp_jet 0 (by omega)) h₀
    intro x
    exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hB₀ x) (norm_nonneg _))
  have hfirst : eLpNorm (cutoffFirstJet χ e.jet 1) 2 volume = eLpNorm (A + B) 2 volume := by
    apply eLpNorm_congr_norm_ae
      (memLp_cutoffFirstJet e.memLp_jet hχ hB₀ hB₁ 1).aestronglyMeasurable
      (hA.add hB).aestronglyMeasurable
    exact Eventually.of_forall fun x ↦ L.symm.norm_map _
  have hA' : (eLpNorm A 2 volume).toReal ≤
      B₁ * (eLpNorm (e.jet 0) 2 volume).toReal := by
    apply eLpNorm_toReal_le_mul_of_bound hA.aestronglyMeasurable (e.memLp_jet 0 (by omega)) h₁
    intro x
    exact (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans
      (mul_le_mul_of_nonneg_right (hB₁ x) (norm_nonneg _))
  have hB' : (eLpNorm B 2 volume).toReal ≤
      B₀ * (eLpNorm (e.jet 1) 2 volume).toReal := by
    apply eLpNorm_toReal_le_mul_of_bound (F := E →L[ℝ] E [×0]→L[ℝ] F) (f := B)
      hB.aestronglyMeasurable (e.memLp_jet 1 le_rfl) h₀
    intro x
    dsimp [B]
    rw [← L.map_smul, L.norm_map, norm_smul]
    exact mul_le_mul_of_nonneg_right (hB₀ x) (norm_nonneg _)
  have hadd : (eLpNorm (A + B) 2 volume).toReal ≤
      (eLpNorm A 2 volume).toReal + (eLpNorm B 2 volume).toReal := by
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hA.eLpNorm_ne_top, hB.eLpNorm_ne_top⟩) (eLpNorm_add_le (by norm_num))).trans_eq
      (ENNReal.toReal_add hA.eLpNorm_ne_top hB.eLpNorm_ne_top)
  simp only [jetNorm, cutoffFirst, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  rw [hfirst]
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (e.jet 1) 2 volume)]

end SobolevExtension

end JanetCartan.LocalSobolev
