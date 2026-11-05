module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.ScalarTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs

/-!
# Fixed angular profiles for the literal adjoint

These are the angular hypotheses of
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow DerivativeKernels

variable {n : ℕ}

/-- Positive dilations cancel in the actual angular graph
(`app:ch_background:eq:bg-T`). -/
theorem adjointAngularGraph_eq_one {R : ℝ} (hR : 0 < R) :
    adjointAngularGraph (n := n) R = adjointAngularGraph 1 := by
  funext p
  simp only [adjointAngularGraph, one_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hR.ne', mul_one]

/-- The explicit punctured frequency neighborhood contains every unit direction
and supports the graph's smoothness, uniformly in positive scale
(`app:ch_background:prop:bg-adjoint`). -/
theorem adjointAngularGraph_contDiffAt {R : ℝ} (hR : 0 < R)
    {p : AdjointSymbolPoint n} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (adjointAngularGraph R) p := by
  rw [adjointAngularGraph_eq_one hR]
  change ContDiffAt ℝ ∞ (fun q : AdjointSymbolPoint n ↦
    (q.1.1, ‖(1 : ℝ) • q.2‖⁻¹ • ((1 : ℝ) • q.2))) p
  simpa only [one_smul] using
    (contDiffAt_fst.fst.prodMk
      (((contDiffAt_snd.norm ℝ hp).inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_snd) :
      ContDiffAt ℝ ∞ (fun q : AdjointSymbolPoint n ↦ (q.1.1, ‖q.2‖⁻¹ • q.2)) p)

/-- A single open neighborhood supplies the endpoint's angular smoothness
hypothesis for all `R ≥ 1` (`app:ch_background:prop:bg-adjoint`). -/
theorem adjointAngularGraph_neighborhood :
    IsOpen ({0}ᶜ : Set (Euclidean (n-1))) ∧
      {η : Euclidean (n-1) | ‖η‖ = 1} ⊆ {0}ᶜ ∧
      ∀ R : ℝ, 1 ≤ R → ∀ η ∈ ({0}ᶜ : Set (Euclidean (n-1))),
        ∀ p : AdjointJetPoint n, ContDiffAt ℝ ∞ (adjointAngularGraph R) (p,η) := by
  refine ⟨isClosed_singleton.isOpen_compl, ?_, ?_⟩
  · intro η hη
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (norm_ne_zero_iff.mp (by rw [hη]; norm_num : ‖η‖ ≠ 0))
  · intro R hR η hη p
    exact adjointAngularGraph_contDiffAt (lt_of_lt_of_le zero_lt_one hR) hη

private theorem angularGraph_jet_translate (p : AdjointSymbolPoint n)
    (hp : p.2 ≠ 0) (i : ℕ) (hi : 1 ≤ i) :
    iteratedFDeriv ℝ i (adjointAngularGraph 1) p =
      iteratedFDeriv ℝ i (adjointAngularGraph 1) (0, p.2) := by
  have he : (fun q : AdjointSymbolPoint n ↦ adjointAngularGraph 1 (q + (p.1, 0))) =
      fun q ↦ adjointAngularGraph 1 q + (p.1.1, 0) := by
    funext q
    simp [adjointAngularGraph]
  have hs := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := adjointAngularGraph (n := n) 1) i (p.1, 0) (0, p.2)
  rw [he] at hs
  rw [fun_iteratedFDeriv_add_apply
    ((adjointAngularGraph_contDiffAt (p := (0, p.2)) zero_lt_one hp).of_le
      (show (i : ℕ∞ω) ≤ ∞ by simp)) contDiffAt_const] at hs
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero, Prod.mk_add_mk,
    zero_add, Prod.mk.eta] using hs.symm

/-- The unbounded carrier coordinate contributes only its constant first jet.
All positive graph jets have fixed bounds independent of scale and of the
carrier and physical points (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_adjointAngularGraph_jet_bounds :
    ∃ N₀ : ℕ → ℝ, (∀ i, 0 ≤ N₀ i) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤ N₀ i := by
  let K : Set (AdjointSymbolPoint n) := {0} ×ˢ sphere 0 1
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_sphere _ _)
  have hs : ∀ p ∈ K, ContDiffAt ℝ ∞ (adjointAngularGraph 1) p := by
    intro p hp
    apply adjointAngularGraph_contDiffAt zero_lt_one
    have hnorm : ‖p.2‖ = 1 := by simpa using hp.2
    exact norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  refine ⟨fun i ↦ cNorm K i (adjointAngularGraph 1),
    fun i ↦ cNorm_nonneg _ _ _, ?_⟩
  intro R hR p hp i hi
  rw [adjointAngularGraph_eq_one (lt_of_lt_of_le zero_lt_one hR),
    angularGraph_jet_translate p (norm_ne_zero_iff.mp (by rw [hp]; norm_num)) i hi]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
    (fun p hp ↦ (hs p hp).of_le (by simp)) ⟨rfl, by simpa using hp⟩ le_rfl

/-- Global complex smoothness of the actual fixed angular mask, before angular
substitution (`app:ch_background:prop:bg-adjoint`). -/
theorem angularMask_complex_contDiff (z₀ : Euclidean 3) (θ₀ : Euclidean (n-1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n-1) ↦
      (CanonicalConic.angularMask z₀ θ₀ ha hb p.1 p.2 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (CanonicalConic.angularMask_smooth z₀ θ₀ ha hb)

/-- Fixed global bounds for every derivative of the original complex angular
mask (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_angularMask_jet_bounds (z₀ : Euclidean 3) (θ₀ : Euclidean (n-1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ P₀ : ℕ → ℝ, (∀ i, 0 ≤ P₀ i) ∧
      ∀ i p, ‖iteratedFDeriv ℝ i (fun p : CarrierParameter × Euclidean (n-1) ↦
        (CanonicalConic.angularMask z₀ θ₀ ha hb p.1 p.2 : ℂ)) p‖ ≤ P₀ i := by
  have hc := (CanonicalConic.angularMask_compact z₀ θ₀ ha hb).comp_left
    (g := fun t : ℝ ↦ (t : ℂ)) (by simp)
  choose P hP hbound using fun i ↦ hc.exists_bound_iteratedFDeriv
    (angularMask_complex_contDiff z₀ θ₀ ha hb) i
  exact ⟨P, hP, fun i p ↦ hbound i i le_rfl p⟩

/-- The fixed angular bounds supply both reserve profiles of the scalar
transport endpoint, including `s = 0` (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_fixed_angular_reserve_profiles
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n-1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ P₀ N₀ : ℕ → ℝ, (∀ i, 0 ≤ P₀ i) ∧ (∀ i, 0 ≤ N₀ i) ∧
      ∀ (H : ℝ), 1 ≤ H → ∀ (s : ℕ) (R : ℝ), 1 ≤ R →
        ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
          (∀ i, ‖iteratedFDeriv ℝ i
            (fun v : CarrierParameter × Euclidean (n-1) ↦
              (CanonicalConic.angularMask z₀ θ₀ ha hb v.1 v.2 : ℂ))
            (adjointAngularGraph R p)‖ ≤
              P₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
          (∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤
              N₀ i * H ^ (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) := by
  obtain ⟨P₀, hP, hPb⟩ := exists_angularMask_jet_bounds z₀ θ₀ ha hb
  obtain ⟨N₀, hN, hNb⟩ := exists_adjointAngularGraph_jet_bounds (n := n)
  refine ⟨P₀, N₀, hP, hN, ?_⟩
  intro H hH s R hR p hp
  constructor
  · intro i
    exact (hPb i _).trans (le_mul_of_one_le_right (hP i)
      (Real.one_le_rpow hH (by positivity)))
  · intro i hi
    exact (hNb R hR p hp i hi).trans (le_mul_of_one_le_right (hN i)
      (Real.one_le_rpow hH (by positivity)))

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
