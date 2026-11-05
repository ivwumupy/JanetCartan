module

public import JanetCartan.Iteration.PhysicalMean.MomentRows
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# The actual compact forward kernel integral is smooth in physical space

The source space can be the literal sampled disjoint-shell measure. It is only
a metric measurable space: no differentiable structure or frequency derivative
bounds are imposed. Joint continuity of the PHYSICAL kernel jets, compact source
and physical supports, and the input L² membership produce all domination and
all physical differentiation identities. The resulting representative is the
original compact-kernel operator's integral, not an independently chosen smooth
representative. Consumer: `app:ch_mean_pairs:eq:block-normal` and
`app:ch_mean_pairs:eq:block-fields`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.PhysicalForwardMean
open Pseudodifferential AmplitudeBound
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
local notation "E" => Euclidean n

omit [SecondCountableTopology X] in
private theorem exists_compactKernel_physicalJet_majorants
    {Kphys : Set E} {Ksrc : Set X} (hp : IsCompact Kphys) (hs : IsCompact Ksrc)
    (kernel : E → X → ℂ) (hsm : ∀ u, ContDiff ℝ ∞ (fun x ↦ kernel x u))
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦
      iteratedFDeriv ℝ j (fun y ↦ kernel y p.2) p.1))
    (hphys : ∀ u, tsupport (fun x ↦ kernel x u) ⊆ Kphys)
    (hsrc : ∀ u, u ∉ Ksrc → ∀ x, kernel x u = 0) (v : Lp ℂ 2 μ) :
    ∃ b : ℕ → X → ℝ, (∀ j, Integrable (b j) μ) ∧
      ∀ j x u, ‖iteratedFDeriv ℝ j (fun y ↦ v u • kernel y u) x‖ ≤ b j u := by
  have hcompact (j : ℕ) : HasCompactSupport (fun p : E × X ↦
      iteratedFDeriv ℝ j (fun y ↦ kernel y p.2) p.1) := by
    apply HasCompactSupport.of_support_subset_isCompact (hp.prod hs)
    intro p hne
    constructor
    · exact hphys p.2 (support_iteratedFDeriv_subset j hne)
    · by_contra hu
      have he : (fun y ↦ kernel y p.2) = 0 := funext (hsrc p.2 hu)
      exact hne (by simp [he])
  choose C hC using fun j ↦ (hcompact j).exists_bound_of_continuous (hjets j)
  refine ⟨fun j u ↦ C j * ‖Ksrc.indicator (fun z ↦ v z) u‖, ?_, ?_⟩
  · intro j
    exact (((Lp.memLp v).locallyIntegrable (by norm_num)).integrableOn_isCompact hs
      |>.integrable_indicator hs.measurableSet).norm.const_mul (C j)
  · intro j x u
    rw [iteratedFDeriv_const_smul_apply' ((hsm u).contDiffAt.of_le (by simp)), norm_smul]
    by_cases hu : u ∈ Ksrc
    · simpa only [Set.indicator_of_mem hu, mul_comm] using
        mul_le_mul_of_nonneg_left (hC j (x,u)) (norm_nonneg (v u))
    · have he : (fun y ↦ kernel y u) = 0 := funext (hsrc u hu)
      simp [he, Set.indicator_of_notMem hu]

/-- All physical derivatives commute with the SAME compact forward integral.
Joint physical-jet continuity and compact supports construct the majorants;
there is no derivative-interchange or output-regularity premise
(`app:ch_mean_pairs:eq:block-normal`). -/
theorem compactKernel_L2Integral_physicalJets
    {Kphys : Set E} {Ksrc : Set X} (hp : IsCompact Kphys) (hs : IsCompact Ksrc)
    (kernel : E → X → ℂ) (hsm : ∀ u, ContDiff ℝ ∞ (fun x ↦ kernel x u))
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦
      iteratedFDeriv ℝ j (fun y ↦ kernel y p.2) p.1))
    (hphys : ∀ u, tsupport (fun x ↦ kernel x u) ⊆ Kphys)
    (hsrc : ∀ u, u ∉ Ksrc → ∀ x, kernel x u = 0) (v : Lp ℂ 2 μ)
    (j : ℕ) (x : E) :
    Integrable (fun u ↦ v u • iteratedFDeriv ℝ j (fun y ↦ kernel y u) x) μ ∧
    iteratedFDeriv ℝ j (fun y ↦ ∫ u, kernel y u * v u ∂μ) x =
      ∫ u, v u • iteratedFDeriv ℝ j (fun y ↦ kernel y u) x ∂μ := by
  obtain ⟨b, hb, hbound⟩ := exists_compactKernel_physicalJet_majorants
    hp hs kernel hsm hjets hphys hsrc v
  have he (q : ℕ) (y : E) (u : X) :
      iteratedFDeriv ℝ q (fun z ↦ v u • kernel z u) y =
        v u • iteratedFDeriv ℝ q (fun z ↦ kernel z u) y :=
    iteratedFDeriv_const_smul_apply' ((hsm u).contDiffAt.of_le (by simp))
  have hm (q : ℕ) (y : E) : AEStronglyMeasurable
      (fun u ↦ iteratedFDeriv ℝ q (fun z ↦ v u • kernel z u) y) μ := by
    simp_rw [he]
    exact (Lp.aestronglyMeasurable v).smul
      ((hjets q).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hi := MeasureEnvelopes.iteratedFDeriv_integral_of_dominated (r := j) (b := b)
    isOpen_univ (Eventually.of_forall fun u y _ ↦
      (((hsm u).const_smul (v u)).of_le (by simp)).contDiffAt)
    (fun q _ y _ ↦ hm q y) (fun q _ ↦ hb q)
    (fun q _ ↦ Eventually.of_forall fun u y _ ↦ hbound q y u) le_rfl (mem_univ x)
  refine ⟨?_, ?_⟩
  · simpa only [he] using (hb j).mono' (hm j x) (Eventually.of_forall (hbound j x))
  · simp_rw [he] at hi
    simpa only [smul_eq_mul, mul_comm] using hi

/-- The literal forward integral has a compact C∞ representative and all its
coordinate derivatives are in physical L². No weighted input moment assumption
is required for this qualitative statement: the original compact frequency mask
supplies integrability. Quantitative norms are proved from the native scalar
test in the later forward assembly (`app:ch_mean_pairs:eq:block-fields`). -/
theorem compactKernel_L2Integral_smooth
    {Kphys : Set E} {Ksrc : Set X} (hp : IsCompact Kphys) (hs : IsCompact Ksrc)
    (kernel : E → X → ℂ) (hsm : ∀ u, ContDiff ℝ ∞ (fun x ↦ kernel x u))
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦
      iteratedFDeriv ℝ j (fun y ↦ kernel y p.2) p.1))
    (hphys : ∀ u, tsupport (fun x ↦ kernel x u) ⊆ Kphys)
    (hsrc : ∀ u, u ∉ Ksrc → ∀ x, kernel x u = 0) (v : Lp ℂ 2 μ) :
    let w := fun y ↦ ∫ u, kernel y u * v u ∂μ
    ContDiff ℝ ∞ w ∧ tsupport w ⊆ Kphys ∧
      ∀ ds : List (Fin n), MemLp (euclideanCoordinateDerivList ds w) 2 volume := by
  intro w
  obtain ⟨b, hb, hbound⟩ := exists_compactKernel_physicalJet_majorants
    hp hs kernel hsm hjets hphys hsrc v
  let A := fun u x ↦ v u • kernel x u
  have hA (u : X) : ContDiff ℝ ∞ (A u) := (hsm u).const_smul (v u)
  have he (q : ℕ) (y : E) (u : X) : iteratedFDeriv ℝ q (A u) y =
      v u • iteratedFDeriv ℝ q (fun z ↦ kernel z u) y :=
    iteratedFDeriv_const_smul_apply' ((hsm u).contDiffAt.of_le (by simp))
  have hm (q : ℕ) (y : E) : AEStronglyMeasurable
      (fun u ↦ iteratedFDeriv ℝ q (A u) y) μ := by
    simp_rw [he]
    exact (Lp.aestronglyMeasurable v).smul
      ((hjets q).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hint (q : ℕ) (y : E) : Integrable (fun u ↦ iteratedFDeriv ℝ q (A u) y) μ :=
    (hb q).mono' (hm q y) (Eventually.of_forall (hbound q y))
  have hd (q : ℕ) (x : E) : DifferentiableAt ℝ
      (fun y ↦ ∫ u, iteratedFDeriv ℝ q (A u) y ∂μ) x := by
    apply HasFDerivAt.differentiableAt
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun y u ↦ fderiv ℝ (iteratedFDeriv ℝ q (A u)) y)
      (s := univ) (bound := b (q+1)) Filter.univ_mem
    · exact Eventually.of_forall (hm q)
    · exact hint q x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q+1) ↦ E) ℂ).continuous.comp_aestronglyMeasurable
        (hm (q+1) x)
    · exact Eventually.of_forall fun u y _ ↦ by
        simpa only [norm_fderiv_iteratedFDeriv] using hbound (q+1) y u
    · exact hb (q+1)
    · exact Eventually.of_forall fun u y _ ↦ ((hA u).contDiffAt.differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top q : (q : ℕ∞ω) < ∞)).hasFDerivAt
  have hid (q : ℕ) : iteratedFDeriv ℝ q w =
      fun y ↦ ∫ u, iteratedFDeriv ℝ q (A u) y ∂μ := by
    funext y
    simpa only [he] using
      (compactKernel_L2Integral_physicalJets hp hs kernel hsm hjets hphys hsrc v q y).2
  have hw : ContDiff ℝ ∞ w := by
    apply contDiff_iff_continuous_differentiable.mpr
    constructor
    · intro q _
      rw [hid q]
      exact continuous_iff_continuousAt.mpr fun x ↦ (hd q x).continuousAt
    · intro q _
      rw [hid q]
      exact hd q
  have hws : tsupport w ⊆ Kphys := by
    apply closure_minimal _ hp.isClosed
    intro x hx
    by_contra hxp
    have hz (u : X) : kernel x u = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ kernel y u) (fun ht ↦ hxp (hphys u ht))
    exact hx (by simp only [w, hz, zero_mul, integral_zero])
  refine ⟨hw, hws, fun ds ↦ ?_⟩
  have hscoord : HasCompactSupport (euclideanCoordinateDerivList ds w) := by
    apply HasCompactSupport.of_support_subset_isCompact hp
    intro x hx
    have heq := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hw ds.get x
    rw [List.ofFn_get] at heq
    apply hws
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) ds.length
    intro hz
    exact hx (by rw [heq, hz]; simp)
  exact (contDiff_euclideanCoordinateDerivList hw ds).continuous.memLp_of_hasCompactSupport hscoord

end JanetCartan.PhysicalForwardMean
