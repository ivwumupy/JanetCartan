module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.AllOrders

/-!
# Physical Sobolev control of the chart adjoint expansion

For `app:ch_background:prop:bg-adjoint`, compact measurement integration gives
joint smoothness of the chart adjoint. The actual identities in `Iteration`
then identify every derivative word with its finite amplitude expansion.
Termwise L² membership, supplied by the parent's concrete conic estimates,
gives the physical Sobolev estimate after partial radian inverse Fourier
transformation. The bound is the finite sum of the realized term L² norms.

The smooth phase, amplitude, derivative-trade fields and their exact phase
identities remain primitive inputs from the parent geometric construction.
No modified-operator bounds or Fourier intertwining identities are assumed.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential NormalComparison
variable {n : ℕ}

/-- Joint smoothness in carrier and frequency follows by compact measurement
integration, for the physical transfer in `app:ch_background:prop:bg-adjoint`.
This supplies the regularity input to
`exists_memLp_chartAdjoint_physicalSobolevNorm_le_expansion`. -/
theorem contDiff_chartAdjoint_joint
    {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
      a p.1 p.2.1 p.2.2))
    (hsupp : ∀ z x η, x ∉ S → a z x η = 0)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
      Φ p.1 p.2.1 p.2.2))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun u : CarrierVariable n ↦
      chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v) := by
  let F : CarrierVariable n × Euclidean n → ℂ := fun p ↦
    oscillatoryFactor (-1) (Φ p.1.1 p.2 p.1.2) * (a p.1.1 p.2 p.1.2 * v p.2)
  have hr : ContDiff ℝ ∞ (fun p : CarrierVariable n × Euclidean n ↦
      (p.1.1, p.2, p.1.2)) := contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)
  have hF : ContDiff ℝ ∞ F :=
    (CompactTransport.contDiff_oscillatoryFactor (hΦ.comp hr) (-1)).mul
      ((ha.comp hr).mul (hv.comp contDiff_snd))
  have he (u : CarrierVariable n) :
      chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v =
        ∫ x in S, F (u, x) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      simp [F, hsupp u.1 x u.2 hx]
  simp_rw [he]
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hS.measure_lt_top (μ := volume)⟩
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ
    hS (subset_univ _) hF.contDiffOn)

/-- Finite sums of realized terms are in L² and satisfy the triangle bound;
used by `memLp_derivativeWord_chartAdjoint_and_norm_le` in
`app:ch_background:prop:bg-adjoint`. -/
private theorem memLp_sum_realize_and_norm_le
    (ts : List (AdjointDerivativeTerm n))
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (v : Euclidean n → ℂ)
    (hL2 : ∀ t ∈ ts, MemLp (t.realize Φ v) 2 (carrierMeasure n)) :
    MemLp (fun u ↦ (ts.map (fun t ↦ t.realize Φ v u)).sum) 2 (carrierMeasure n) ∧
      (eLpNorm (fun u ↦ (ts.map (fun t ↦ t.realize Φ v u)).sum)
        2 (carrierMeasure n)).toReal ≤
      (ts.map (fun t ↦ (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨hrest, hbound⟩ := ih (fun q hq ↦ hL2 q (List.mem_cons_of_mem t hq))
    have ht := hL2 t (by simp)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨ht.add hrest, ?_⟩
    calc
      _ ≤ (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal +
          (eLpNorm (fun u ↦ (ts.map (fun t ↦ t.realize Φ v u)).sum)
            2 (carrierMeasure n)).toReal := by
        simpa only [← MemLp.toLp_add, Lp.norm_toLp, Pi.add_def] using norm_add_le (ht.toLp _) (hrest.toLp _)
      _ ≤ _ := add_le_add le_rfl hbound

/-- The checked derivative-trade expansion supplies L² membership and its
termwise norm bound for each actual word in `app:ch_background:prop:bg-adjoint`.
Only membership of the realized terms is assumed; the parent obtains it from
the concrete conic L² estimate. -/
theorem memLp_derivativeWord_chartAdjoint_and_norm_le
    {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    (hphaseL : ∀ z x η h, x ∈ S → inner ℝ h η =
      fderiv ℝ (fun y ↦ Φ z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ S → fderiv ℝ (fun w ↦ Φ w x η) z h =
      fderiv ℝ (fun y ↦ Φ z y η) x (V z x h))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (ds : List (InitialCarrierDerivative n))
    (hL2 : ∀ t ∈ adjointDerivativeExpansion L V ds a,
      MemLp (t.realize Φ v) 2 (carrierMeasure n)) :
    MemLp (applyInitialCarrierDerivativeList ds
      (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v))
      2 (carrierMeasure n) ∧
    (eLpNorm (applyInitialCarrierDerivativeList ds
      (fun u ↦ chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v))
      2 (carrierMeasure n)).toReal ≤
    ((adjointDerivativeExpansion L V ds a).map
      (fun t ↦ (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal)).sum := by
  have he := funext (applyInitialCarrierDerivativeList_chartAdjoint
    hS ha hL hV hΦ hphaseL hphaseV hv ds)
  rw [he]
  exact memLp_sum_realize_and_norm_le _ Φ v hL2

/-- Apply the all-order physical transfer to the actual chart adjoint, using
its checked expansion (`app:ch_background:prop:bg-adjoint`). The conclusion
constructs the original L² representative, proves physical Sobolev membership,
and bounds its norm by the finite sum of the realized expansion term norms.
The parent raw adjoint assembly supplies the primitive geometric hypotheses
and termwise L² membership, then estimates these norms by its conic bounds
and fixed-reserve interpolation. All coordinates occur before physical cutoffs. -/
theorem exists_memLp_chartAdjoint_physicalSobolevNorm_le_expansion
    (s : ℕ) {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
      a p.1 p.2.1 p.2.2))
    (hsupp : ∀ z x η, x ∉ S → a z x η = 0)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
      Φ p.1 p.2.1 p.2.2))
    (hphaseL : ∀ z x η h, x ∈ S → inner ℝ h η =
      fderiv ℝ (fun y ↦ Φ z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ S → fderiv ℝ (fun w ↦ Φ w x η) z h =
      fderiv ℝ (fun y ↦ Φ z y η) x (V z x h))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (hL2 : ∀ ds : List (InitialCarrierDerivative n), ds.length ≤ s →
      ∀ t ∈ adjointDerivativeExpansion L V ds a,
        MemLp (t.realize Φ v) 2 (carrierMeasure n)) :
    let f : CarrierVariable n → ℂ := fun u ↦
      chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v
    ∃ hf : MemLp f 2 (carrierMeasure n),
      MemPhysicalSobolev s (partialUnitaryInverse n (hf.toLp f)) ∧
      physicalSobolevNorm s (partialUnitaryInverse n (hf.toLp f)) ≤
        (4 * Real.pi) ^ s * ∑ w : CarrierDerivativeIndex n s,
          ((adjointDerivativeExpansion L V (physicalDerivativeWord w) a).map
            (fun t ↦ (eLpNorm (t.realize Φ v) 2 (carrierMeasure n)).toReal)).sum := by
  let f : CarrierVariable n → ℂ := fun u ↦
    chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v
  have has : SmoothSupportedAdjointAmplitude S a :=
    ⟨fun η ↦ ha.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)), hsupp⟩
  have hΦs (η : Euclidean (n - 1)) :
      ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η) :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hw (ds : List (InitialCarrierDerivative n)) (hs : ds.length ≤ s) :=
    memLp_derivativeWord_chartAdjoint_and_norm_le hS has hL hV hΦs
      hphaseL hphaseV hv ds (hL2 ds hs)
  have hm (ds : List (InitialCarrierDerivative n)) (hs : ds.length ≤ s) :
      MemLp (applyInitialCarrierDerivativeList ds f) 2 (carrierMeasure n) := (hw ds hs).1
  have hreg : ContDiff ℝ ∞ f := contDiff_chartAdjoint_joint hS ha hsupp hΦ hv
  refine ⟨hm [] (Nat.zero_le s), memPhysicalSobolev_partialInverse s f hreg hm, ?_⟩
  exact (physicalSobolevNorm_partialInverse_le_derivativeWordSum s f hreg hm).trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun w _ ↦ (hw _ (physicalDerivativeWord_length_le w)).2))
      (by positivity))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
