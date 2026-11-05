module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.SolverRealization
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSolverTemplate

/-!
# The original inverse without a second source cutoff

The full normalized source in `OriginalSourceProfiles` already contains chi2.
Its inverse input must therefore be `Inv h`, not `Inv (chi2*h)`. We use the
EXISTING chi3 solely to extend that inverse source, and retain the globally
uncut paired solver. No output cutoff or new inverse is selected.
Consumers: the original full-response operator and the observed full-inverse
remainder (`app:ch_regular:thm:exact-correction`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open Set MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal
namespace JanetCartan.PhysicalPrimary.OriginalUncutSolver
open FixedDomainInverse LocalSobolev SmallSupport
open RegularSector.Realization RegularSector.FiniteAssembly
open FourierIntegral Pseudodifferential CharacteristicTransport.CompleteResidual

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A single linear smooth realization of chi3*Inv, derived from the actual
inverse's all-order membership. The proof does not insert chi2 at its input.
The actual original-current constructor below supplies `hInv`. -/
theorem exists_uncut_source_realization {n : ℕ} {W : Set (Euclidean n)}
    (hW : IsOpen W) {x : Euclidean n} (χ₃ : ContDiffBump x)
    (hχ₃ : tsupport (χ₃ : Euclidean n → ℝ) ⊆ W)
    (Inv : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (hInv : ∀ s u, MemRestrictionSobolev W s u → MemRestrictionSobolev W s (Inv u)) :
    ∃ z : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n), ∀ h,
      ContDiff ℝ ∞ (z h) ∧
      z h =ᵐ[volume.restrict W] bumpL2 (p := 2) le_rfl χ₃ (Inv h) ∧
      tsupport (z h) ⊆ tsupport (χ₃ : Euclidean n → ℝ) ∧ W.indicator (z h) = z h := by
  let Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n) :=
    (bumpL2 (p := 2) le_rfl χ₃).comp Inv
  have hex (h : smoothSource W (Euclidean n)) :
      ∃ z : Euclidean n → Euclidean n,
        ContDiff ℝ ∞ z ∧ z =ᵐ[volume.restrict W] Corr h ∧
        tsupport z ⊆ tsupport (χ₃ : Euclidean n → ℝ) ∧ W.indicator z = z := by
    apply exists_supported_smoothRepresentative hW (isClosed_tsupport _) hχ₃ (Corr h)
    · intro s
      exact memRestrictionSobolev_bumpL2_of_all_orders hW χ₃ hχ₃ (Inv h)
        (fun t ↦ hInv t h (h.property t)) s
    · filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₃ (Inv h)] with y hy
      intro hout
      change bumpL2 (p := 2) le_rfl χ₃ (Inv h) y = 0
      have hzero : χ₃ y = 0 := image_eq_zero_of_notMem_tsupport hout
      rw [hy, hzero, zero_smul]
  let z : smoothSource W (Euclidean n) → Euclidean n → Euclidean n :=
    fun h ↦ (hex h).choose
  have hz (h : smoothSource W (Euclidean n)) :
      ContDiff ℝ ∞ (z h) ∧ z h =ᵐ[volume.restrict W] Corr h ∧
        tsupport (z h) ⊆ tsupport (χ₃ : Euclidean n → ℝ) ∧ W.indicator (z h) = z h :=
    (hex h).choose_spec
  have hadd (h k : smoothSource W (Euclidean n)) : z (h+k) = z h+z k := by
    refine supported_continuousRepresentative_unique hW
      (hz (h+k)).1.continuous.continuousOn ((hz h).1.add (hz k).1).continuous.continuousOn
      (hz (h+k)).2.1 ?_ (hz (h+k)).2.2.2 ?_
    · change (fun y ↦ z h y+z k y) =ᵐ[volume.restrict W] Corr (h+k)
      have he : Corr (h+k) = Corr h+Corr k := map_add Corr h.val k.val
      rw [he]
      filter_upwards [(hz h).2.1, (hz k).2.1, Lp.coeFn_add (Corr h) (Corr k)] with y hy hk ha
      exact (congrArg₂ (·+·) hy hk).trans ha.symm
    · change W.indicator (fun y ↦ z h y+z k y) = z h+z k
      rw [indicator_add, (hz h).2.2.2, (hz k).2.2.2]
      rfl
  have hsmul (a : ℝ) (h : smoothSource W (Euclidean n)) : z (a • h) = a • z h := by
    refine supported_continuousRepresentative_unique hW
      (hz (a • h)).1.continuous.continuousOn (contDiff_const.smul (hz h).1).continuous.continuousOn
      (hz (a • h)).2.1 ?_ (hz (a • h)).2.2.2 ?_
    · change (fun y ↦ a • z h y) =ᵐ[volume.restrict W] Corr (a • h)
      have he : Corr (a • h) = a • Corr h := map_smul Corr a h.val
      rw [he]
      filter_upwards [(hz h).2.1, Lp.coeFn_smul a (Corr h)] with y hy ha
      exact (congrArg (a • ·) hy).trans ha.symm
    · ext y
      by_cases hy : y ∈ W
      · simp [hy]
      · have hzero : z h y = 0 := by
          rw [← (hz h).2.2.2, indicator_of_notMem hy]
        simp [hy, hzero]
  exact ⟨{ toFun := z, map_add' := hadd, map_smul' := hsmul }, hz⟩

/-- Realize the SAME paired solver on chi3*Inv(h), globally and at all orders.
The source cutoff appears once AFTER Inv; no physical output cutoff occurs. -/
theorem exists_uncut_solver_realization {d : ℕ} {W : Set (Euclidean (d+1))}
    (hW : IsOpen W) {x : Euclidean (d+1)} (χ₃ : ContDiffBump x)
    (hχ₃ : tsupport (χ₃ : Euclidean (d+1) → ℝ) ⊆ W)
    (Inv : LocalL2 W (Euclidean (d+1)) →L[ℝ] LocalL2 W (Euclidean (d+1)))
    (hInv : ∀ s u, MemRestrictionSobolev W s u → MemRestrictionSobolev W s (Inv u))
    (T : Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure (Euclidean (d+1))))
    (hT : ∀ (u : graphTestSpace (d+1) (d+1)) (s : ℕ),
      MemVectorFourierSobolev (s : ℝ) (T (graphTestToLp u))) :
    ∃ V : smoothSource W (Euclidean (d+1)) →ₗ[ℝ] (Euclidean (d+1) → Euclidean (d+1)), ∀ h,
      ContDiff ℝ ∞ (V h) ∧ V h =ᵐ[volume]
        realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ T))
          (zeroExtend hW.measurableSet (bumpL2 (p := 2) le_rfl χ₃ (Inv h))) := by
  obtain ⟨z, hz⟩ := exists_uncut_source_realization hW χ₃ hχ₃ Inv hInv
  exact exists_smooth_corrected_solver_realization hW.measurableSet χ₃.hasCompactSupport
    (fun h ↦ bumpL2 (p := 2) le_rfl χ₃ (Inv h)) z hz T hT

end JanetCartan.PhysicalPrimary.OriginalUncutSolver

set_option maxHeartbeats 600000 in
construct_original_uncut_solver

end
