module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral
/-!
# Fourier Sobolev bound from the diagonal correction's physical jets

The compact-kernel step of `app:ch_background:eq:bg-real-symbol`.
FiniteChain's compact-support L² estimates control each coordinate derivative;
the existing PDO Fourier Sobolev comparison and compact-test extension then
apply to the original Euclidean L² operator. No derivatives of the datum occur.
-/

open Set MeasureTheory
open scoped ContDiff
open JanetCartan Pseudodifferential AmplitudeBound
open FiniteChain.Retarded.KernelSobolev FiniteChain.Retarded.KernelDecay
@[expose] public noncomputable section
namespace JanetCartan.ContinuumRow.TransportKernel.PrincipalSobolev
set_option maxHeartbeats 1200000
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem column_jet_bound (k : E × E → ℂ) (hk : ContDiff ℝ ∞ k)
    (r : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ r (fun z ↦ k (z,y)) x‖ ≤ ‖iteratedFDeriv ℝ r k (x,y)‖ := by
  let L : E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prod 0
  have he : (fun z ↦ k (z,y)) = (fun p ↦ k (p + (0,y))) ∘ L := by
    funext z; simp [L]
  have ht : ContDiff ℝ ∞ (fun p ↦ k (p + (0,y))) := hk.comp (contDiff_id.add contDiff_const)
  rw [he, L.iteratedFDeriv_comp_right ht x (by simp)]
  rw [iteratedFDeriv_comp_add_right]
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(z, (0 : E))‖ ≤ 1 * ‖z‖
    simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg z), one_mul, le_refl]
  have h := (iteratedFDeriv ℝ r k (L x + (0,y))).norm_compContinuousLinearMap_le
    (fun _ : Fin r ↦ L)
  have hprod : (∏ _ : Fin r, ‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
  have h' := h.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)
  convert h' using 1
  simp only [L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, Prod.mk_add_mk,
    add_zero, zero_add]

private theorem coord_append (is js : List (Fin n)) (f : E → ℂ) :
    euclideanCoordinateDerivList (is ++ js) f =
      euclideanCoordinateDerivList is (euclideanCoordinateDerivList js f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, euclideanCoordinateDerivList, ih]

private theorem test_norm_bound (s : ℕ) (g : E → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) {B : ℝ}
    (hb : ∀ is : List (Fin n), is.length ≤ s →
      ‖((contDiff_euclideanCoordinateDerivList hg is).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hasCompactSupport_euclideanCoordinateDerivList hgs is)).toLp
        (euclideanCoordinateDerivList is g)‖ ≤ B) :
    fourierSobolevNorm (s : ℝ) ((hg.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgs).toLp g) ≤
      (1 + (n : ℝ)) ^ s * B := by
  induction s generalizing g with
  | zero => simpa [fourierSobolevNorm_zero, euclideanCoordinateDerivList] using hb [] (by simp)
  | succ s ih =>
    have hbase := ih g hg hgs (fun is hi ↦ hb is (hi.trans (Nat.le_succ _)))
    have hder (i : Fin n) := ih _ (contDiff_euclideanCoordinateDerivList hg [i])
      (hasCompactSupport_euclideanCoordinateDerivList hgs [i])
      (fun is hi ↦ by simpa only [coord_append] using hb (is ++ [i]) (by simp; omega))
    rw [Nat.cast_add, Nat.cast_one]
    apply (fourierSobolevNorm_le_coordinateDerivatives (by positivity)
      (memFourierSobolev_nat_toLp s g hg hgs)
      (fun i ↦ memFourierSobolev_nat_toLp s _ (contDiff_euclideanCoordinateDerivList hg [i])
        (hasCompactSupport_euclideanCoordinateDerivList hgs [i]))
      (hasEuclideanL2CoordinateDerivative_toLp g hg hgs)).trans
    calc
      _ ≤ (1 + (n : ℝ)) ^ s * B + ∑ i : Fin n, (1 + (n : ℝ)) ^ s * B :=
        add_le_add hbase (Finset.sum_le_sum (fun i _ ↦ hder i))
      _ = _ := by simp [pow_succ]; ring

private theorem compact_kernel_test_bound
    (k : E × E → ℂ) (hk : ContDiff ℝ ∞ k)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hx : ∀ x y, x ∉ X → k (x,y) = 0)
    (hy : ∀ x y, y ∉ Y → k (x,y) = 0)
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ r ≤ s, ∀ p, ‖iteratedFDeriv ℝ r k p‖ ≤ A)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    ∃ (hg : ContDiff ℝ ∞ (fun x ↦ ∫ y, k (x,y) * f y))
      (hgs : HasCompactSupport (fun x ↦ ∫ y, k (x,y) * f y)),
      fourierSobolevNorm (s : ℝ) ((hg.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgs).toLp _) ≤
        ((1 + (n : ℝ)) ^ s * A * compactSupportFactor volume volume Y X) *
          ‖(hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs).toLp f‖ := by
  let g := fun x ↦ ∫ y, k (x,y) * f y
  have hq : ContDiff ℝ ∞ (fun p : E × E ↦ f p.2 • k p) := (hf.comp contDiff_snd).smul hk
  have hqz : ∀ x y, y ∉ Y → f y • k (x,y) = 0 := by
    intro x y hy'; simp [hy x y hy']
  have he : g = fun x ↦ ∫ y, f y • k (x,y) := by
    funext x; simp [g, smul_eq_mul, mul_comm]
  have hg : ContDiff ℝ ∞ g := by
    rw [he]; exact contDiff_integral_commonCarrier hq hY hqz
  have hgz (x : E) (h : x ∉ X) : g x = 0 := by simp [g, hx x _ h]
  have hgs : HasCompactSupport g := HasCompactSupport.intro hX hgz
  refine ⟨hg, hgs, ?_⟩
  have hb' (is : List (Fin n)) (his : is.length ≤ s) (x : E) :
      ‖euclideanCoordinateDerivList is g x‖ ≤
        (A * Real.sqrt (volume.real Y)) *
          ‖(hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs).toLp f‖ := by
    let v : Fin is.length → E := fun i ↦ EuclideanSpace.single (is.get i) 1
    let q : E → ℂ := fun y ↦ iteratedFDeriv ℝ is.length (fun z ↦ k (z,y)) x v
    have hqbound (y : E) : ‖q y‖ ≤ A := by
      apply le_trans _ ((column_jet_bound k hk is.length x y).trans (hb _ his _))
      simpa [q, v, PiLp.norm_single, EuclideanSpace.single] using
        (iteratedFDeriv ℝ is.length (fun z ↦ k (z,y)) x).le_opNorm v
    have hqzero (y : E) (h : y ∉ Y) : q y = 0 := by
      simp [q, outputJet_eq_zero_off_carrier hy is.length x h]
    have hqc : Continuous q := by
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin is.length ↦ E) ℂ v).continuous.comp
        ((contDiff_outputJet hk is.length).continuous.comp
          (continuous_const.prodMk continuous_id))
    have hqm : MemLp q 2 volume := memLp_of_support_bound hqc.aestronglyMeasurable
      hY.measurableSet hY.measure_ne_top hA hqbound hqzero
    have hformula : euclideanCoordinateDerivList is g x = ∫ y, q y * f y := by
      rw [← List.ofFn_get is, euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hg]
      rw [he, iteratedFDeriv_integral_commonCarrier hq hY hqz]
      rw [ContinuousMultilinearMap.integral_apply
        (integrable_outputJet_commonCarrier hq hY hqz _ x)]
      apply integral_congr_ae
      filter_upwards [] with y
      have hcol : ContDiff ℝ ∞ (fun z ↦ k (z,y)) := hk.comp (contDiff_id.prodMk contDiff_const)
      rw [iteratedFDeriv_const_smul_apply' (hcol.of_le (by simp)).contDiffAt]
      simp [q, v, smul_eq_mul, mul_comm]
    rw [hformula]
    exact (norm_integral_mul_le_l2 hqm (hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs)).trans
      (mul_le_mul_of_nonneg_right
        (norm_toLp_le_of_support_bound hqm hY.measurableSet hY.measure_ne_top
          hA hqbound hqzero) (norm_nonneg _))
  refine (test_norm_bound s g hg hgs (B := (A * Real.sqrt (volume.real Y)) *
    ‖(hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs).toLp f‖ * Real.sqrt (volume.real X))
    ?_).trans_eq ?_
  · intro is his
    apply norm_toLp_le_of_support_bound _ hX.measurableSet hX.measure_ne_top
      (mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (norm_nonneg _)) (hb' is his)
    intro x hx'
    have hvan : g =ᶠ[nhds x] (fun _ ↦ 0) :=
      (isOpen_compl_iff.mpr hX.isClosed).eventually_mem hx' |>.mono fun z hz ↦ hgz z hz
    have hv := (euclideanCoordinateDerivList_eventuallyEq hvan is).self_of_nhds
    rw [hv]
    clear his hv
    have hz : euclideanCoordinateDerivList is (fun _ : E ↦ (0 : ℂ)) = 0 := by
      induction is with
      | nil => rfl
      | cons i is ih => simp only [euclideanCoordinateDerivList, ih]; ext z; simp
    exact congrFun hz x
  · unfold compactSupportFactor; ring

/-- Euclidean all-data smoothing from physical kernel jets, consumed by
`localizedDiagonalCorrectionOperator_sobolev_of_jets`. The literal integral
identity, support and jets are the only inputs; the existing density theorem
proves Sobolev membership (`app:ch_background:eq:bg-real-symbol`). -/
theorem compactKernel_fourierSobolev_bound
    (k : E × E → ℂ) (hk : ContDiff ℝ ∞ k)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hx : ∀ x y, x ∉ X → k (x,y) = 0)
    (hy : ∀ x y, y ∉ Y → k (x,y) = 0)
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ r ≤ s, ∀ p, ‖iteratedFDeriv ℝ r k p‖ ≤ A)
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ f, T f =ᵐ[volume] fun x ↦ ∫ y, k (x,y) * f y)
    (f : Lp ℂ 2 (volume : Measure E)) :
    MemFourierSobolev (s : ℝ) (T f) ∧
      fourierSobolevNorm (s : ℝ) (T f) ≤
        ((1 + (n : ℝ)) ^ s * A * compactSupportFactor volume volume Y X) * ‖f‖ := by
  have h := fourierSobolev_operator_bound_of_compactSmooth_zero T (s : ℝ)
    ((1 + (n : ℝ)) ^ s * A * compactSupportFactor volume volume Y X) 0 (fun g hg hgs ↦ ?_) f
  · simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using h
  obtain ⟨hv, hvs, hvb⟩ := compact_kernel_test_bound k hk hX hY hx hy s hA hb g hg hgs
  have he : T ((hg.continuous.memLp_of_hasCompactSupport hgs).toLp g) =
      (hv.continuous.memLp_of_hasCompactSupport hvs).toLp (fun x ↦ ∫ y, k (x,y) * g y) := by
    apply Lp.ext
    filter_upwards [hT ((hg.continuous.memLp_of_hasCompactSupport hgs).toLp g),
      (hv.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hvs).coeFn_toLp] with x hx' hy'
    rw [hx', hy']
    apply integral_congr_ae
    filter_upwards [(hg.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgs).coeFn_toLp] with y hy'
    rw [hy']
  dsimp only
  rw [he]
  exact ⟨memFourierSobolev_nat_toLp s _ hv hvs, by
    simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using hvb⟩

end JanetCartan.ContinuumRow.TransportKernel.PrincipalSobolev
