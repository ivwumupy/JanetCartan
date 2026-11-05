module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfiles
public import JanetCartan.Iteration.PhysicalMean.CanonicalLowQuadratic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData
public import JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Bounds
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometry

/-!
# The actual original quadratic source

The forward amplitude uses the SAME compactly cut corrected matrix from
`OriginalMeasuredHermitianProfiles`, the SAME output observation, and only the
fixed inverse-Fourier normalization. The full angular factor remains in the
scalar mask and in the original `G`; it is not inserted a second time here.
The consuming estimate is `fixedSourceQuadratic_low_bound`
(`app:ch_mean_pairs:eq:block-bilinear`, `new:eq:mean-operators`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open Pseudodifferential

/-- The fixed normalization used only in the uncontracted forward amplitude.
The matching reciprocal is already part of the original bare scalar mask
(`app:ch_mean_pairs:eq:block-bilinear`). -/
def forwardNormalization (n : ℕ) : ℂ :=
  (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ)

/-- Observe the actual cut matrix and freeze its original carrier variables.
No sample, frequency-band or angular weight is divided out. -/
def observedForwardAmplitude {n N : ℕ}
    (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ)
    (q : Euclidean 3 × Euclidean (n - 1)) (a : Fin N) (c : Fin n)
    (x : Euclidean n) : ℂ :=
  forwardNormalization n * (ψ x • B (x, q)) a c

/-- The common physical jet budget is fixed before the history scale. Its
matrix-coordinate factor depends only on the fixed dimensions, never on the
number of samples or retained bands (`app:ch_mean_pairs:eq:block-bilinear`). -/
def observedForwardBudget (n N : ℕ) (Aψ AB : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖forwardNormalization n‖ * matrixEntryBound (Fin N) (Fin n) *
    productProfile
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ)
      Aψ AB j

/-- Nonnegativity of the fixed forward jet budget. -/
theorem observedForwardBudget_nonneg {n N : ℕ} {Aψ AB : ℕ → ℝ}
    (hAψ : ∀ j, 0 ≤ Aψ j) (hAB : ∀ j, 0 ≤ AB j) (j : ℕ) :
    0 ≤ observedForwardBudget n N Aψ AB j := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _) matrixEntryBound_nonneg)
    (productProfile_nonneg _ hAψ hAB j)

/-- The observation's fixed compact seminorm has nonnegative forward cost. -/
theorem observedForwardBudget_cNorm_nonneg {n N : ℕ}
    (K : Set (Euclidean n)) (ψ : Euclidean n → ℝ) {AB : ℕ → ℝ}
    (hAB : ∀ j, 0 ≤ AB j) :
    ∀ j, 0 ≤ observedForwardBudget n N (fun k ↦ cNorm K k ψ) AB j :=
  observedForwardBudget_nonneg (fun k ↦ cNorm_nonneg K k ψ) hAB

/-- Sum only over the original fixed geometric rows, before histories or
sampled nodes. This is never a bound by the number of sampled channels. -/
def fixedRowBudget {I : Type*} [Fintype I] (C : I → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i, C i j

/-- Nonnegativity of the fixed geometric envelope. -/
theorem fixedRowBudget_nonneg {I : Type*} [Fintype I] {C : I → ℕ → ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (j : ℕ) : 0 ≤ fixedRowBudget C j :=
  Finset.sum_nonneg (fun i _ ↦ hC i j)

/-- Each actual original row is controlled by the prehistory envelope. -/
theorem fixedRowBudget_le {I : Type*} [Fintype I] {C : I → ℕ → ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (i : I) (j : ℕ) : C i j ≤ fixedRowBudget C j :=
  Finset.single_le_sum (fun k _ ↦ hC k j) (Finset.mem_univ i)

/-- The actual joint cut-amplitude bound supplies every physical entry jet at
exactly the same order. Freezing the carrier variables is contractive, and the
only normalization cost is the fixed Fourier scalar. This is the `hGj` adapter
for `fixedSourceQuadratic_low_bound`, not an uncut-response profile. -/
theorem observedForwardAmplitude_jets {n N rK rpar : ℕ}
    {ψ : Euclidean n → ℝ}
    {B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hB : ContDiff ℝ ∞ B)
    {Aψ AB : ℕ → ℝ} (hAψ : ∀ j, 0 ≤ Aψ j) (hAB : ∀ j, 0 ≤ AB j)
    {T : ℝ} (hT : 1 ≤ T) (hr : rK ≤ rpar)
    (hBj : ∀ j w, ‖iteratedFDeriv ℝ j B w‖ ≤ AB j * T ^ (j - rpar))
    (q : Euclidean 3 × Euclidean (n - 1)) (a : Fin N) (c : Fin n)
    {x : Euclidean n}
    (hψj : ∀ j, ‖iteratedFDeriv ℝ j ψ x‖ ≤ Aψ j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (observedForwardAmplitude ψ B q a c) x‖ ≤
      observedForwardBudget n N Aψ AB j * T ^ (j - rK) := by
  let g : Euclidean n → Matrix (Fin N) (Fin n) ℂ := fun y ↦ B (y, q)
  have hg : ContDiff ℝ ∞ g := hB.comp (contDiff_id.prodMk contDiff_const)
  have hgj (k : ℕ) : ‖iteratedFDeriv ℝ k g x‖ ≤ AB k * T ^ (k - rK) := by
    exact ((norm_iteratedFDeriv_physical_slice_le isOpen_univ hB.contDiffOn
      (mem_univ (x, q)) k).trans (hBj k (x, q))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hAB k))
  have hψj' (k : ℕ) : ‖iteratedFDeriv ℝ k ψ x‖ ≤ Aψ k * T ^ (k - rK) :=
    (hψj k).trans (le_mul_of_one_le_right (hAψ k) (one_le_pow₀ hT))
  let s : Euclidean n → Matrix (Fin N) (Fin n) ℂ := fun y ↦ ψ y • g y
  have hs : ContDiff ℝ ∞ s := hψ.smul hg
  have hsj := jet_bilinear_le
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ)
    isOpen_univ hψ.contDiffOn hg.contDiffOn (mem_univ x) hT hAψ hAB hψj' hgj j
  have he := norm_iteratedFDeriv_matrix_entry_le s j j le_rfl
    (hs.of_le (by simp)) x a c
  have hes : ContDiff ℝ ∞ (fun y ↦ s y a c) :=
    (matrixEntryCLM a c).contDiff.comp hs
  change ‖iteratedFDeriv ℝ j (fun y ↦ forwardNormalization n • s y a c) x‖ ≤ _
  rw [jet_const_smul hes.contDiffAt]
  exact (mul_le_mul_of_nonneg_left
    (he.trans (mul_le_mul_of_nonneg_left hsj matrixEntryBound_nonneg))
    (norm_nonneg _)).trans_eq (by simp only [observedForwardBudget]; ring)

/-- On the retained physical compact, the observation has a fixed `cNorm`
budget. No scale or source-dependent observation is chosen. -/
theorem observedForwardAmplitude_jets_on_compact {n N rK rpar : ℕ}
    {ψ : Euclidean n → ℝ}
    {B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hB : ContDiff ℝ ∞ B)
    {AB : ℕ → ℝ} (hAB : ∀ j, 0 ≤ AB j)
    {T : ℝ} (hT : 1 ≤ T) (hr : rK ≤ rpar)
    (hBj : ∀ j w, ‖iteratedFDeriv ℝ j B w‖ ≤ AB j * T ^ (j - rpar))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (q : Euclidean 3 × Euclidean (n - 1)) (a : Fin N) (c : Fin n) :
    ∀ x ∈ K, ∀ j,
    ‖iteratedFDeriv ℝ j (observedForwardAmplitude ψ B q a c) x‖ ≤
      observedForwardBudget n N (fun k ↦ cNorm K k ψ) AB j * T ^ (j - rK) := by
  intro x hx j
  exact observedForwardAmplitude_jets hψ hB (fun k ↦ cNorm_nonneg K k ψ) hAB hT hr hBj
    q a c (fun k ↦ norm_iteratedFDeriv_le_cNorm hK (hψ.of_le (by simp)) hx le_rfl) j

/-- The literal affine frequency slice of the SAME cut amplitude. -/
def forwardSlice {n N : ℕ} (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1)) (τ : ℝ)
    (a : Fin N) (c : Fin n) (η : Euclidean (n - 1)) : Euclidean n → ℂ :=
  observedForwardAmplitude ψ B (z, ζ + τ • η) a c

/-- Joint smoothness uses the unchanged original affine carrier slice. -/
theorem forwardSlice_contDiff {n N : ℕ} {ψ : Euclidean n → ℝ}
    {B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hB : ContDiff ℝ ∞ B)
    (z : Euclidean 3) (ζ : Euclidean (n - 1)) (τ : ℝ) (a : Fin N) (c : Fin n) :
    ContDiff ℝ ∞ (Function.uncurry (forwardSlice ψ B z ζ τ a c)) := by
  have hb : ContDiff ℝ ∞ (fun p : Euclidean (n - 1) × Euclidean n ↦
      ψ p.2 • B (p.2, z, ζ + τ • p.1)) :=
    (hψ.comp contDiff_snd).smul (hB.comp (by fun_prop))
  exact contDiff_const.mul ((matrixEntryCLM a c).contDiff.comp hb)

/-- The observation supplies exactly the required support, independently of
whether the original angular or band mask vanishes. -/
theorem forwardSlice_tsupport {n N : ℕ} (ψ : Euclidean n → ℝ)
    (B : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
      Matrix (Fin N) (Fin n) ℂ)
    (z : Euclidean 3) (ζ : Euclidean (n - 1)) (τ : ℝ)
    (a : Fin N) (c : Fin n) (η : Euclidean (n - 1)) :
    tsupport (forwardSlice ψ B z ζ τ a c η) ⊆ tsupport ψ := by
  apply closure_mono
  intro x hx
  by_contra h
  exact hx (by simp only [forwardSlice, observedForwardAmplitude,
    Function.notMem_support.mp h, zero_smul, Matrix.zero_apply, mul_zero])

/-- The original very-low parameter reserve exceeds the exact kernel reserve
needed by the mean theorem. This uses no additional source derivative. -/
theorem mean_kernel_reserve_le_original (n : ℕ) :
    2 * (n / 2 + 2) + (n / 2 + 1) ≤ RawPrimary.SliceBounds.rawSliceParameterOrder n := by
  unfold RawPrimary.SliceBounds.rawSliceParameterOrder RawPrimary.SliceBounds.rawSliceJetOrder
  omega

open RawInputPartition OriginalSampledMomentGeometry PhysicalForwardMean

/-- The SAME fixed native band prefix, with both refined copies retained
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def prefixGate {J : ℕ} (L : ℕ) (j : RefinedIndex J) : ℝ :=
  if j.1.val < L then 1 else 0

/-- Apply the existing prefix to the original scalar mask, not to its angular
factor or Fourier normalization separately. -/
def prefixMask {n J : ℕ} (L : ℕ)
    (m : RefinedIndex J × Euclidean (n - 1) → ℝ)
    (z : RefinedIndex J × Euclidean (n - 1)) : ℝ :=
  prefixGate L z.1 * m z

/-- The discrete prefix leaves frequency continuity intact. -/
theorem prefixMask_continuous {n J : ℕ} (L : ℕ)
    {m : RefinedIndex J × Euclidean (n - 1) → ℝ} (hm : Continuous m) :
    Continuous (prefixMask L m) :=
  ((continuous_of_discreteTopology : Continuous (prefixGate (J := J) L)).comp continuous_fst).mul hm

/-- No source support is enlarged by the original prefix. -/
theorem prefixMask_compact {n J : ℕ} (L : ℕ)
    {m : RefinedIndex J × Euclidean (n - 1) → ℝ} (hm : HasCompactSupport m) :
    HasCompactSupport (prefixMask L m) := hm.mul_left

/-- Every active prefixed shell is active in the original mask. -/
theorem prefixMask_active {n J : ℕ} {L : ℕ}
    {m : RefinedIndex J × Euclidean (n - 1) → ℝ}
    {z : RefinedIndex J × Euclidean (n - 1)} (h : prefixMask L m z ≠ 0) : m z ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

/-- The original high-pass floor survives its fixed native prefix. -/
theorem prefixMask_high {n J : ℕ} (L : ℕ)
    {m : RefinedIndex J × Euclidean (n - 1) → ℝ}
    (hm : ∀ z, ‖z.2‖ ≤ 1 → m z = 0) :
    ∀ z, ‖z.2‖ ≤ 1 → prefixMask L m z = 0 := by
  intro z hz
  simp only [prefixMask, hm z hz, mul_zero]

/-- The actual bare detector gives the closed high-pass floor required by
`fixedSourceQuadratic_low_bound`, including its unit boundary. -/
theorem full_bare_mask_high {n J : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (a : ℝ) :
    ∀ z : RefinedIndex J × Euclidean (n - 1), ‖z.2‖ ≤ 1 →
      a * singleBareScalarMask (originalForwardDetector hηb hr) z = 0 := by
  intro z hz
  have hm : singleBareScalarMask (originalForwardDetector hηb hr) z = 0 := by
    by_contra h
    exact (not_lt_of_ge hz) (one_lt_norm_of_singleBareScalarMask_ne_zero hηb hr h)
  rw [hm, mul_zero]

/-- Use the SAME current phase, trade, and all-order moment budgets after
applying the already fixed native prefix. No chart is reselected. -/
theorem prefix_chart {n J : ℕ}
    {φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ}
    {Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ}
    {m : RefinedIndex J × Euclidean (n-1) → ℝ}
    {L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n}
    {K : Set (Euclidean n)} {DL DP : ℕ → ℝ} {rStar : ℕ} {T : ℝ}
    (h : SampledChart φ Φ m L K DL DP rStar T) (cut : ℕ) :
    SampledChart φ Φ (prefixMask cut m) L K DL DP rStar T := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact h.2.2.2.2.1 z (prefixMask_active hz)
  · intro z hz
    exact h.2.2.2.2.2.1 z (prefixMask_active hz)
  · intro z hz
    exact h.2.2.2.2.2.2.1 z (prefixMask_active hz)
  · intro r hr
    obtain ⟨hl, hp⟩ := h.2.2.2.2.2.2.2 r hr
    exact ⟨fun i η hz ↦ hl i η (prefixMask_active hz),
      fun i η hz ↦ hp i η (prefixMask_active hz)⟩

open MeasureTheory CurrentMean RawInputRealization

/-- The original `canonicalWidePrefixRawMap` has exactly the prefixed annular
kernel needed by the low quadratic theorem. This is a whole finite-sum equality:
no shell triangle inequality, cardinality bound or new input scaling occurs
(`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem prefix_annular_realization {n N J : ℕ}
    (G : WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (A : Fin N → Fin n → RefinedIndex J → Euclidean (n-1) → Euclidean n → ℂ)
    (hG : ∀ w : RefinedInput n J, ∀ z,
      (G ((wideRefinement n J).symm w)).val z () = ∑ j,
        (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ (j,η))
          (fun η ↦ m (j,η) * Real.sqrt ‖η‖) (A a c j)
          (AmplitudeBound.centeredTorusRepresentative z) η * w j η) : Matrix (Fin N) (Fin n) ℂ)
          ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ))
    (cut : ℕ) (w : RefinedInput n J) (z : Torus n) :
    (canonicalWidePrefixRawMap G cut w).val z () = ∑ j,
      (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ (j,η))
        (fun η ↦ prefixMask cut m (j,η) * Real.sqrt ‖η‖) (A a c j)
        (AmplitudeBound.centeredTorusRepresentative z) η * w j η) : Matrix (Fin N) (Fin n) ℂ)
        ∂annularMeasure n (refinedRadius j) : Matrix (Fin N) (Fin n) ℂ) := by
  have hw : widePrefix n J cut ((wideRefinement n J).symm w) =
      (wideRefinement n J).symm (refinedPrefix n J cut w) := by
    apply (wideRefinement n J).injective
    rw [wideRefinement_prefix, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
  change (G (widePrefix n J cut ((wideRefinement n J).symm w))).val z () = _
  rw [hw, hG]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.1.val < cut
  · simp only [refinedPrefix_apply, hj, ite_true, prefixMask, prefixGate, one_mul]
  · refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (annularMeasure n (refinedRadius j))] with η hη
    ext a c
    simp only [refinedPrefix_apply, hj, ite_false, hη, Pi.zero_apply, mul_zero,
      prefixMask, prefixGate, zero_mul, physicalForwardKernel, sampledMomentKernel,
      Complex.ofReal_zero, star_star]

/-- Equality of the original frames as subtypes follows from the common
current projected stress, not from identifying independent choices. -/
theorem frame_eq_of_projected_stress {α : Type*} {P : α → Prop} (Q R : Subtype P) (F : α)
    (hQ : Q.1 = F) (hR : R.1 = F) : Q = R := Subtype.ext (hQ.trans hR.symm)

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate
private def actual := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def field (root suffix : Name) (xs : Array Expr) :=
  mkAppN (mkConst (root ++ suffix)) xs

private def save (suffix : Name) (xs : Array Expr) (term : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "actual quadratic: absent producer constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual quadratic: an open or assumed input reached {suffix}"
  let name := actual ++ suffix
  if let some path ← IO.getEnv "JANET_ACTUAL_Q_TRACE" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn s!"kernel checking {name} with {xs.size} actual parameters"
      h.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original saved50 history, row, color and outer node; actual observed cut-amplitude87 with only fixed Fourier compensation. No angular/sample division or new analytic premise (app:ch_mean_pairs:eq:block-bilinear)."
  logInfo m!"actual quadratic: checked {suffix} on native{xs.size}"

/-- Instantiate the forward amplitude and its primitive physical profiles.
The only inputs are the actual original event, row, color and outer node. -/
elab "construct_actual_forward_amplitude " mode:num : command => liftTermElabM do
  withActualRow fun d => do
    let n := d.raw13[0]!
    let N := d.raw13[1]!
    let graph := d.mean70[53]!
    unless graph.isAppOfArity `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42 do
      throwError "actual quadratic: changed original graph42"
    let fixed := graph.getAppArgs[:22].toArray
    let derivative := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative
    let cut := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
    let ψ := field derivative `observationFunction fixed
    let hψ := field derivative `observation_smooth fixed
    let hψK := field derivative `observation_support fixed
    let K := (← inferType hψK).getAppArgs.back!
    let ka := K.getAppArgs
    let hK ← mkAppM ``ProperSpace.isCompact_closedBall #[ka[ka.size-2]!,ka.back!]
    let AB := field cut `cutAmplitudeBudget (d.parameters[:44].toArray.push d.row)
    let hAB := field cut `cutAmplitudeBudget_nonneg (d.parameters[:44].toArray.push d.row)
    let rate := d.native64[61]!
    let ζ ← referenceCarrier d
    let .forallE colorName colorType _ bi ← inferType rate
      | throwError "actual quadratic: missing original color-rate domain"
    withLocalDeclNoLocalInstanceUpdate colorName bi colorType fun color => do
      withLocalDeclNoLocalInstanceUpdate `node .default
          (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
        let p := d.parameters ++ #[color,node]
        let z ← nodeAt node
        let B := field cut `cutAmplitude (d.parameters.push color)
        let hB := field cut `cutAmplitude_contDiff (d.parameters.push color)
        let jets := field cut `cutAmplitude_jets_global (d.parameters.push color)
        let τ := mkApp rate color
        let carrier := mkApp ζ z
        let slice := field actual `forwardSlice #[n,N,ψ,B,z,carrier,τ]
        match mode.getNat with
        | 0 => save `forwardAmplitude p slice true
        | 1 =>
          save `forwardAmplitude_contDiff p
            (field actual `forwardSlice_contDiff #[n,N,ψ,B,hψ,hB,z,carrier,τ])
        | 2 =>
          save `forwardAmplitude_tsupport p
            (field actual `forwardSlice_tsupport #[n,N,ψ,B,z,carrier,τ])
        | 3 =>
          let hr := mkApp (mkConst (actual ++ `mean_kernel_reserve_le_original)) n
          let orders := (← inferType hr).getAppArgs
          let rK := orders[orders.size-2]!
          let rpar := orders.back!
          let T := mkAppN (mkConst `JanetCartan.currentCoefficientScale)
            #[d.parameters[44]!,d.parameters[46]!]
          let bound := field actual `observedForwardAmplitude_jets_on_compact
            #[n,N,rK,rpar,ψ,B,hψ,hB,AB,hAB,T,d.mean70[62]!,hr,jets,K,hK]
          let sliced ← forallBoundedTelescope (← inferType slice) (some 3) fun aca _ => do
            let shift ← mkAppM ``HSMul.hSMul #[mkApp rate color,aca[2]!]
            let shifted ← mkAppM ``HAdd.hAdd #[mkApp ζ z,shift]
            let q ← mkAppM ``Prod.mk #[z,shifted]
            mkLambdaFVars aca (mkAppN bound #[q,aca[0]!,aca[1]!])
          save `forwardAmplitude_physical_jets p sliced
        | 4 =>
          let Aψ ← withLocalDeclD `j (mkConst ``Nat) fun j => do
            mkLambdaFVars #[j] (← mkAppM `JanetCartan.cNorm #[K,j,ψ])
          let cost := field actual `observedForwardBudget #[n,N,Aψ,AB]
          save `forwardAmplitudeBudget (d.parameters[:44].toArray.push d.row) cost true
        | 5 =>
          let proof := field actual `observedForwardBudget_cNorm_nonneg #[n,N,K,ψ,AB,hAB]
          save `forwardAmplitudeBudget_nonneg (d.parameters[:44].toArray.push d.row) proof
        | 6 =>
          let rows ← mkLambdaFVars #[d.row]
            (field actual `forwardAmplitudeBudget (d.parameters[:44].toArray.push d.row))
          let total ← mkAppM (actual ++ `fixedRowBudget) #[rows]
          save `forwardAmplitudeBudgetTotal d.parameters[:44].toArray total true
        | 7 | 8 =>
          let rowBounds ← mkLambdaFVars #[d.row]
            (field actual `forwardAmplitudeBudget_nonneg (d.parameters[:44].toArray.push d.row))
          if mode.getNat == 7 then
            save `forwardAmplitudeBudgetTotal_nonneg d.parameters[:44].toArray
              (← mkAppM (actual ++ `fixedRowBudget_nonneg) #[rowBounds])
          else
            save `forwardAmplitudeBudget_le_total (d.parameters[:44].toArray.push d.row)
              (← mkAppM (actual ++ `fixedRowBudget_le) #[rowBounds,d.row])
        | _ => throwError "actual quadratic: unknown forward-amplitude field"

/-- Recover the task90 point of the original saved native53. Slots three
and four of native53 describe the *extra* margin, not the selected bare
frame. The two freely bound propositions are genuine numerical admissions;
there is no second sampled shift, frame estimate, inverse or chart premise. -/
def withActualMomentAt (p : Array Expr)
    (next : Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  unless p.size == 53 do throwError "actual moment: expected native53"
  let ns := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
  let source := ns ++ `AtPoint.φ
  let tol := field ns `tolerance #[p[0]!,p[1]!]
  withLocalDeclNoLocalInstanceUpdate `hγMoment .default (← mkAppM ``LE.le #[p[24]!,tol]) fun hγ => do
    let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
    let pre := sampler[:21].toArray ++ p[21:27].toArray ++ #[hγ] ++ p[27:36].toArray ++ #[p[39]!]
    -- Bind the actual R₀ BEFORE extracting the common-clock admission.
    let mut tail := (← getConstInfo source).type
    for a in pre.push p[44]! do
      let .forallE _ _ body _ := tail | throwError "actual moment: changed point47 telescope"
      tail := body.instantiate1 a
    let .forallE _ reach _ _ := tail | throwError "actual moment: missing numerical R₀ reach"
    if reach.hasLooseBVars then throwError "actual moment: uninstantiated R₀ in reach"
    withLocalDeclNoLocalInstanceUpdate `hR90 .default reach fun hR => do
      let point := pre ++ #[p[44]!,hR] ++ p[46:53].toArray
      unless point.size == 47 do throwError "actual moment: original47 carrier ABI changed"
      next hγ hR point

/-- Realize the already fixed discrete prefix of the very same native47
chart, including its normalized phase and traded-direction budgets. Retain
their static all-patch envelopes before the stage or sampled nodes. -/
elab "construct_actual_quadratic_moment_chart" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitude)).type (some 53) fun p _ => do
    withActualMomentAt p fun hγ hR point => do
      let h := field ns `AtPoint.fields point
      let ht ← inferType h
      unless ht.isAppOfArity (ns ++ `SampledChart) 11 do throwError "actual moment: chart operands changed"
      let hs := ht.getAppArgs
      withLocalDeclNoLocalInstanceUpdate `cut .default (mkConst ``Nat) fun cut => do
        save `moment_chart (p ++ #[hγ,hR,cut]) (field actual `prefix_chart (hs ++ #[h,cut]))
      for (pos,k,budget) in #[(7,`DL,`directionBudgetTotal),(8,`DP,`phaseBudgetTotal)] do
        let D := hs[pos]!
        unless D.isAppOfArity (ns ++ `Native ++ k) 39 do throwError "actual moment: lost static patch budget {k}"
        let atSource := D.getAppArgs[:38].toArray
        let root := ns ++ `Native ++ k
        -- The native wrapper carries hγ, but the selected family budget does
        -- not. Expose only that wrapper before forming its fixed patch sum.
        let base ← bodyAt root atSource
        let positive ← bodyAt (ns ++ `Native ++ (if k == `DL then `DL_pos else `DP_pos)) atSource
        let fixed := p[:44].toArray
        let inputs := #[p[0]!,p[1]!,base]
        save budget fixed (field ns `patchTotal inputs) true
        save (budget ++ `nonneg) fixed (field ns `patchTotal_nonneg (inputs.push positive))
        save (budget ++ `dominates) (fixed.push p[50]!)
          (field ns `le_patchTotal (inputs ++ #[positive,D.getAppArgs.back!]))

/-- Task90's chart frame is an independently presented subtype, so do not
try `rfl` between its witnesses. Both projected stresses are the SAME finite
map. The corrected kernel's frame is a literal `LeadingData.Q` constructor. -/
elab "construct_actual_quadratic_same_frame" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
  let cut := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitude)).type (some 53) fun p _ => do
    withActualMomentAt p fun hγ hR point => do
      let ph ← bodyAt (ns ++ `AtPoint.φ) point
      unless ph.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12 do
        throwError "actual moment: lost full finite-rate retained phase"
      let Q90 := ph.getAppArgs[6]!
      unless Q90.isAppOfArity (ns ++ `Native.Q) 45 do throwError "actual moment: changed chart frame"
      let h90 := field ns `Native.Q_current Q90.getAppArgs
      let F := (← inferType h90).getAppArgs[2]!
      let primitive ← bodyAt (cut ++ `cutAmplitude_contDiff) p[:52].toArray
      unless primitive.isAppOfArity `JanetCartan.Sampling.contDiff_cutCorrectedDerivativeAmplitude 28 do
        throwError "actual moment: changed cut87 proof"
      let Q := primitive.getAppArgs[6]!
      let qval ← bodyAt Q.getAppFn.constName! Q.getAppArgs
      unless qval.isAppOfArity ``Subtype.mk 4 && qval.getAppArgs[2]!.isAppOf
          `JanetCartan.ProjectedStressFrame.projectedStress do throwError "actual moment: not original stress"
      let st ← inferType Q
      unless st.isAppOfArity ``Subtype 2 do throwError "actual moment: missing original frame subtype"
      let hs := mkAppN (mkConst ``Eq.refl [.succ .zero]) #[st.getAppArgs[0]!,qval.getAppArgs[2]!]
      let e := mkAppN (mkConst (actual ++ `frame_eq_of_projected_stress) [.zero])
        (st.getAppArgs ++ #[Q90,Q,F,h90,hs])
      save `moment_frame_eq_corrected (p ++ #[hγ,hR]) e

end JanetCartan.PhysicalMean.OriginalMeanQuadraticApplication
end

construct_actual_forward_amplitude 0
construct_actual_forward_amplitude 1
construct_actual_forward_amplitude 2
construct_actual_forward_amplitude 3
construct_actual_forward_amplitude 4
construct_actual_forward_amplitude 5
construct_actual_forward_amplitude 6
construct_actual_forward_amplitude 7
construct_actual_forward_amplitude 8
construct_actual_quadratic_moment_chart
construct_actual_quadratic_same_frame
