module

public import JanetCartan.Iteration.PhysicalMean.CrossSobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Scalar
public import JanetCartan.Analysis.Extension.Mollification.WeakJet

/-!
# The sharp Fourier-Sobolev amplitude budget for the actual quadratic row

This inserts the lossless physical source-jet bound into the original scalar
`H^ell` amplitude test. Constants precede the current coefficients, the
source-dependent background, the frequency and the original sample
(`app:ch_mean_pairs:eq:mean-quadratic-low`, `new:eq:Q-derivative-term`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CanonicalRowComparison LocalSobolev Pseudodifferential ArbitraryAccuracy

/-- A fixed-order scalar component of the FULL modified cross coefficient has
its sharp Fourier `H^s` bound from only the SAME background's L² jets through
`s`. No `C^s` norm of that background, Sobolev embedding, or parameter derivative
is assumed. The case `s = ell` is the input to the original amplitude tester. -/
theorem exists_crossAmplitude_component_fourierSobolev_bound (n N s : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (K : Set (Euclidean n)), IsCompact K →
      ∀ (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
        (B G : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
        ContDiff ℝ ∞ C → ContDiff ℝ ∞ B → ContDiff ℝ ∞ G → tsupport G ⊆ K →
      (∀ j ≤ s, MemLp (iteratedFDeriv ℝ j B) 2 volume) → ∀ i : Fin n,
      let f := fun x ↦ complexCrossMeasurement (C x) (B x) (G x) i
      ∃ hf : MemLp f 2 volume,
        MemFourierSobolev (s : ℝ) (hf.toLp f) ∧
          fourierSobolevNorm (s : ℝ) (hf.toLp f) ≤
            D * cNorm K s C * cNorm K s G *
              ∑ j ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ j B) 2 volume := by
  obtain ⟨D₀, hD₀, hFourier⟩ := scalarFourierSobolev_extension_bounds n s
  let a := fun j : ℕ ↦ 2 * ((2 : ℝ) ^ j) ^ 2
  have ha (j) : 0 ≤ a j := by dsimp [a]; positivity
  refine ⟨D₀ * ∑ j ∈ Finset.range (s + 1), a j,
    mul_nonneg hD₀.le (Finset.sum_nonneg fun j _ ↦ ha j), ?_⟩
  intro K hK C B G hC hB hG hGK hBmem i f
  let H := fun x ↦ complexCrossMeasurement (C x) (B x) (G x)
  have hH : ContDiff ℝ ∞ H := (complexCrossMeasurement_cNorm_bound hK s C B G hC hB hG).1
  let π : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).restrictScalars ℝ
  have hπ : ‖π‖ ≤ 1 := by
    apply π.opNorm_le_bound zero_le_one
    intro z
    change ‖z i‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using PiLp.norm_apply_le z i
  have hf : ContDiff ℝ ∞ f := π.contDiff.comp hH
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    apply hGK
    apply subset_tsupport
    intro hz
    exact hx (by simp only [f, hz, map_zero, PiLp.zero_apply])
  have hfmem : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfs
  let P := cNorm K s C * cNorm K s G *
    ∑ k ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ k B) 2 volume
  have hj (j : ℕ) (hjs : j ≤ s) :
      MemLp (iteratedFDeriv ℝ j f) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ j f) 2 volume ≤ a j * P := by
    obtain ⟨hHj, hHjn⟩ := crossAmplitude_jet_L2_bound hK j C B G hC hB hG hGK
      (fun k hk ↦ hBmem k (hk.trans hjs))
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ j f) volume :=
      (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    have hpoint (x : Euclidean n) :
        ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j H x‖ := by
      have hh := π.norm_iteratedFDeriv_comp_left (hH.contDiffAt (x := x))
        (by simp : (j : ℕ∞ω) ≤ ∞)
      exact hh.trans ((mul_le_mul_of_nonneg_right hπ
        (norm_nonneg (iteratedFDeriv ℝ j H x))).trans_eq (one_mul _))
    have hmem : MemLp (iteratedFDeriv ℝ j f) 2 volume :=
      hHj.of_le hmeas (Filter.Eventually.of_forall hpoint)
    have hnorm : lpNorm (iteratedFDeriv ℝ j f) 2 volume ≤
        lpNorm (iteratedFDeriv ℝ j H) 2 volume := by
      simpa only [toReal_eLpNorm] using
        ENNReal.toReal_mono hHj.eLpNorm_ne_top
          (eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall hpoint))
    have hCm := cNorm_mono_order (s := K) (f := C) hjs
    have hGm := cNorm_mono_order (s := K) (f := G) hjs
    have hcoef : a j * cNorm K j C * cNorm K j G ≤
        a j * cNorm K s C * cNorm K s G :=
      mul_le_mul (mul_le_mul_of_nonneg_left hCm (ha j)) hGm
        (cNorm_nonneg K j G) (mul_nonneg (ha j) (cNorm_nonneg K s C))
    have hsum : (∑ k ∈ Finset.range (j + 1), lpNorm (iteratedFDeriv ℝ k B) 2 volume) ≤
        ∑ k ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ k B) 2 volume :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.add_le_add_right hjs 1)) (fun _ _ _ ↦ lpNorm_nonneg)
    refine ⟨hmem, hnorm.trans (hHjn.trans ?_)⟩
    exact (mul_le_mul hcoef hsum
      (Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg)
      (mul_nonneg (mul_nonneg (ha j) (cNorm_nonneg K s C)) (cNorm_nonneg K s G))).trans_eq
        (by dsimp [P]; ring)
  let v : LocalL2 (univ : Set (Euclidean n)) ℂ := (hfmem.restrict univ).toLp f
  let e : SobolevExtension univ s v :=
    { toFun := f
      jet := fun j ↦ iteratedFDeriv ℝ j f
      weakJet := Mollification.hasWeakJetOn_of_contDiff volume
        (hf.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) univ
      memLp_fun := hfmem
      memLp_jet := fun j hj' ↦ (hj j hj').1
      restrict_eq := (MemLp.coeFn_toLp _).symm }
  have he : e.toL2 = hfmem.toLp f := by
    apply Lp.ext
    exact e.toL2_coeFn.trans (MemLp.coeFn_toLp hfmem).symm
  obtain ⟨hHs, hHsNorm⟩ := hFourier univ v e
  rw [he] at hHs hHsNorm
  refine ⟨hfmem, hHs, hHsNorm.trans ?_⟩
  calc
    _ = D₀ * ∑ j ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ j f) 2 volume := rfl
    _ ≤ D₀ * ∑ j ∈ Finset.range (s + 1), a j * P :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj' ↦
        (hj j (Nat.le_of_lt_succ (Finset.mem_range.mp hj'))).2) hD₀.le
    _ = _ := by rw [← Finset.sum_mul]; dsimp [P]; ring

end JanetCartan.PhysicalMean
