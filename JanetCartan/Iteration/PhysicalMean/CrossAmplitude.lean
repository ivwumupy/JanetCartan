module

public import JanetCartan.Analysis.ContDiff.Norm.Products
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.CrossResponse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix

/-!
# The actual source-dependent cross amplitude in the quadratic mean row

The modified row keeps the full raw derivative amplitude, replacing only the
background by the SAME canonical derivative `Dν v`. The actual complex
measurement is the one whose `2 Re` channel is the measured Hermitian cross.
Its finite physical coefficient bound is linear in each supplied factor,
with no sample, carrier, band or input-measure constant
(`app:ch_mean_pairs:eq:mean-quadratic-low`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean CanonicalRowComparison FullPhaseCharts.InverseEstimates

/-- Compact physical coefficient control of the literal complex cross
measurement. For the modified quadratic row, `B` is the ACTUAL `Dν v`, `G`
is the FULL corrected raw amplitude, and `C` is the original measurement.
The same estimate also applies to the separately differentiated factors in
the balanced high-order quadratic expansion. -/
theorem complexCrossMeasurement_cNorm_bound {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (s : ℕ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G) :
    let H := fun x ↦ complexCrossMeasurement (C x) (B x) (G x)
    ContDiff ℝ ∞ H ∧ cNorm K s H ≤
      (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm K s C * cNorm K s B * cNorm K s G := by
  dsimp only
  let HB := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  let E := (ContinuousLinearMap.apply ℝ (Euclidean n)
    (E' := Matrix (Fin n) (Fin n) ℝ)).flip
  have hHB : ‖HB‖ ≤ 1 := norm_hermitianContinuousBilinear_le
  have hE : ‖E‖ ≤ 1 := by
    apply E.opNorm_le_bound₂ zero_le_one
    intro L v
    change ‖L v‖ ≤ 1 * ‖L‖ * ‖v‖
    simpa only [one_mul] using L.le_opNorm v
  let Iin : Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
    Complex.I • ContinuousLinearMap.id ℝ _
  have hIin : ‖Iin‖ ≤ 1 := by
    apply Iin.opNorm_le_bound zero_le_one
    intro v
    simp [Iin, norm_smul]
  let GI := Iin ∘ G
  have hGI : ContDiff ℝ ∞ GI := Iin.contDiff.comp hG
  have hGInorm : cNorm K s GI ≤ cNorm K s G :=
    (cNorm_postLinear_le_on hK s Iin (fun _ _ ↦ hG.contDiffAt.of_le (by simp))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hIin (cNorm_nonneg K s G))
  let P := ((2 : ℝ) ^ s) ^ 2 * cNorm K s C * cNorm K s B * cNorm K s G
  have hprod (f : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
      (hf : ContDiff ℝ ∞ f) (hfn : cNorm K s f ≤ cNorm K s G) :
      cNorm K s (fun x ↦ C x (HB (B x) (f x))) ≤ P := by
    have hp : ContDiff ℝ ∞ (fun x ↦ HB (B x) (f x)) := (HB.contDiff.comp hB).clm_apply hf
    have hb := cNorm_bilinear_le_of_opNorm_le HB hK
      (hB.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) (hf.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) hHB
    have he := cNorm_bilinear_le_of_opNorm_le E hK
      (hC.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) (hp.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) hE
    simp only [mul_one] at hb he
    have hbg : cNorm K s (fun x ↦ HB (B x) (f x)) ≤
        (2 : ℝ) ^ s * cNorm K s B * cNorm K s G :=
      hb.trans (mul_le_mul_of_nonneg_left hfn
        (mul_nonneg (by positivity) (cNorm_nonneg K s B)))
    exact he.trans ((mul_le_mul_of_nonneg_left hbg
      (mul_nonneg (by positivity) (cNorm_nonneg K s C))).trans_eq (by dsimp [P]; ring))
  let v₀ := fun x ↦ C x (HB (B x) (G x))
  let vI := fun x ↦ C x (HB (B x) (GI x))
  have hv₀ : ContDiff ℝ ∞ v₀ := hC.clm_apply ((HB.contDiff.comp hB).clm_apply hG)
  have hvI : ContDiff ℝ ∞ vI := hC.clm_apply ((HB.contDiff.comp hB).clm_apply hGI)
  have hv₀n : cNorm K s v₀ ≤ P := hprod G hG le_rfl
  have hvIn : cNorm K s vI ≤ P := hprod GI hGI hGInorm
  let Iout : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin n) := euclideanComplexInclusion
  let IIout : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin n) := Complex.I • Iout
  have hIout : ‖Iout‖ ≤ 1 := euclideanComplexInclusion_norm_le
  have hIIout : ‖IIout‖ ≤ 1 := by
    apply IIout.opNorm_le_bound zero_le_one
    intro v
    simp [IIout, Iout, norm_smul, euclideanComplexInclusion_norm]
  have hu₀ : ContDiff ℝ ∞ (Iout ∘ v₀) := Iout.contDiff.comp hv₀
  have huI : ContDiff ℝ ∞ (IIout ∘ vI) := IIout.contDiff.comp hvI
  have heq : (fun x ↦ complexCrossMeasurement (C x) (B x) (G x)) =
      (Iout ∘ v₀) - (IIout ∘ vI) := rfl
  rw [heq]
  refine ⟨hu₀.sub huI, ?_⟩
  have hu₀n : cNorm K s (Iout ∘ v₀) ≤ P := by
    calc
      _ ≤ ‖Iout‖ * cNorm K s v₀ :=
        cNorm_postLinear_le_on hK s Iout (fun _ _ ↦ hv₀.contDiffAt.of_le (by simp))
      _ ≤ cNorm K s v₀ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hIout (cNorm_nonneg K s v₀)
      _ ≤ P := hv₀n
  have huIn : cNorm K s (IIout ∘ vI) ≤ P := by
    calc
      _ ≤ ‖IIout‖ * cNorm K s vI :=
        cNorm_postLinear_le_on hK s IIout (fun _ _ ↦ hvI.contDiffAt.of_le (by simp))
      _ ≤ cNorm K s vI := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hIIout (cNorm_nonneg K s vI)
      _ ≤ P := hvIn
  exact ((cNorm_sub_le hK (hu₀.of_le (by simp : (s : ℕ∞ω) ≤ ∞))
    (huI.of_le (by simp : (s : ℕ∞ω) ≤ ∞))).trans
      (add_le_add hu₀n huIn)).trans_eq (by dsimp [P]; ring)

/-- The modified row's physical derivative is controlled by the pointwise
jet sum of the SAME source-dependent background, while only the two genuine
coefficient factors are measured in `C^s`. Integrating this bound costs exactly
`H^s(B)`, not `C^s(B)` and not a Sobolev-embedding loss
(`app:ch_mean_pairs:eq:mean-quadratic-low`, `new:eq:Q-derivative-term`). -/
theorem norm_iteratedFDeriv_complexCrossMeasurement_le_source_jets {n N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (s : ℕ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hB : ContDiff ℝ ∞ B) (hG : ContDiff ℝ ∞ G)
    {x : Euclidean n} (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ s (fun y ↦ complexCrossMeasurement (C y) (B y) (G y)) x‖ ≤
      (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm K s C * cNorm K s G *
        ∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j B x‖ := by
  have hcross := complexCrossMeasurement_cNorm_bound (K := {x}) isCompact_singleton
    s C B G hC hB hG
  have hsub : ({x} : Set (Euclidean n)) ⊆ K := singleton_subset_iff.mpr hx
  have hCm := cNorm_mono_set hsub hK (hC.of_le (by simp : (s : ℕ∞ω) ≤ ∞))
  have hGm := cNorm_mono_set hsub hK (hG.of_le (by simp : (s : ℕ∞ω) ≤ ∞))
  have hnonneg : 0 ≤ 2 * ((2 : ℝ) ^ s) ^ 2 := by positivity
  have hBx : cNorm ({x} : Set (Euclidean n)) s B =
      ∑ j ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ j B x‖ := by
    simp only [cNorm, Set.image_singleton, csSup_singleton]
  calc
    _ ≤ cNorm ({x} : Set (Euclidean n)) s
        (fun y ↦ complexCrossMeasurement (C y) (B y) (G y)) :=
      norm_iteratedFDeriv_le_cNorm isCompact_singleton
        (hcross.1.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) (by simp) le_rfl
    _ ≤ (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm {x} s C * cNorm {x} s B *
        cNorm {x} s G := hcross.2
    _ ≤ (2 * ((2 : ℝ) ^ s) ^ 2) * cNorm K s C * cNorm {x} s B *
        cNorm K s G :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCm hnonneg)
          (cNorm_nonneg {x} s B)) hGm (cNorm_nonneg {x} s G)
        (mul_nonneg (mul_nonneg hnonneg (cNorm_nonneg K s C)) (cNorm_nonneg {x} s B))
    _ = _ := by rw [hBx]; ring

end JanetCartan.PhysicalMean
