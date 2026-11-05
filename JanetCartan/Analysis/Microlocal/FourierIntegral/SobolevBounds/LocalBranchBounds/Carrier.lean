module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Bounds

/-!
# Carrier coverage for local graph estimates

Compact physical support and the closed frequency carrier keep every nonzero
branch jet in the region where the actual phase and inverse are regular.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Actual joint derivatives cannot enlarge the closed support, even where
primitive coefficients are singular. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem tsupport_derivative_subset (c : Coordinate n) (A : FullAmplitude n r) :
    tsupport (uncurry (derivative c A)) ⊆ tsupport (uncurry A) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have he := derivative_congr (f := A) (g := 0) (p := p)
    (notMem_tsupport_iff_eventuallyEq.mp hn) c
  exact hp (by simpa only [derivative_zero, uncurry, Pi.zero_apply] using he)

/-- The low reserve includes covector derivatives; these also preserve support.
Source: Step 3 before `app:ch_regular_base:eq:fio-input`. -/
theorem tsupport_jet_subset (w : List (Coordinate n)) (A : FullAmplitude n r) :
    tsupport (uncurry (jet w A)) ⊆ tsupport (uncurry A) := by
  induction w with
  | nil => exact Subset.rfl
  | cons c w ih => exact (tsupport_derivative_subset c _).trans ih

private theorem graph_remainder_support (i : Fin n) (A : FullAmplitude n r) :
    tsupport (uncurry (graphTransferRemainder S i A)) ⊆ tsupport (uncurry A) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hz (c : Coordinate n) : uncurry (derivative c A) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hn (tsupport_derivative_subset c A hm))
  have hx := hz (.left, i)
  have hy (j) := hz (.right, j)
  apply hp
  change _ + ∑ j, _ = 0
  change partialDeriv (fun z => A z p.1.2 p.2) p.1.1 i = 0 at hx
  have hy' (j) : partialDeriv (fun z => A p.1.1 z p.2) p.1.2 j = 0 := hy j
  simp only [hx, hy', smul_zero, Finset.sum_const_zero, add_zero]

private theorem branch_support
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (hR : ∀ i B, tsupport (uncurry (R i B)) ⊆ tsupport (uncurry B))
    (hP : ∀ i j B, tsupport (uncurry (P i j B)) ⊆ tsupport (uncurry B))
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) :
    tsupport (uncurry p.1) ⊆ tsupport (uncurry A) := by
  induction is generalizing p with
  | nil =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_singleton] at hp
    subst p
    exact Subset.rfl
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    simp only [fullAmplitudeDerivativeStep, List.mem_cons, List.mem_ofFn] at hp
    rcases hp with rfl | ⟨j, rfl⟩
    · exact (hR i q.1).trans (ih q hq)
    · exact (hP i j q.1).trans (ih q hq)

/-- Every forward branch jet is supported in the initial complete amplitude.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_branch_jet_support (is : List (Fin n))
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A is)
    (w : List (Coordinate n)) :
    tsupport (uncurry (jet w p.1)) ⊆ tsupport (uncurry A) :=
  (tsupport_jet_subset w p.1).trans (branch_support _ _ graph_remainder_support
    (fun _ _ _ => tsupport_smul_subset_right _ _) is p hp)

/-- Every reverse branch jet stays in the initial support, including derivatives
of the inverse-weighted amplitude. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjoint_branch_jet_support (is : List (Fin n))
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) :
    tsupport (uncurry (jet w p.1)) ⊆ tsupport (uncurry A) :=
  (tsupport_jet_subset w p.1).trans (branch_support (adjointTransferRemainder S) (adjointTransferDatum S)
    (fun i B => tsupport_adjointTransferRemainder_subset S B i)
    (fun i j B => tsupport_adjointTransferDatum_subset S B i j) is p hp)

/-- Pointwise compact physical and closed frequency carriers control the joint
closed support. The frequency carrier need not be compact. Source: Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem tsupport_subset_carrier {K : Set (Euclidean n × Euclidean n)}
    {F : Set (Euclidean n)} (hK : IsCompact K) (hF : IsClosed F)
    (hA : ∀ p : Point n, p ∉ K ×ˢ F → uncurry A p = 0) :
    tsupport (uncurry A) ⊆ K ×ˢ F := by
  apply closure_minimal _ (hK.isClosed.prod hF)
  intro p hp
  by_contra hn
  exact hp (hA p hn)

/-- The actual region of primitive regularity. Its inverse condition is tested
pointwise, so no gap outside the physical carrier is imposed. Source: Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def regularRegion (S : Euclidean n → Euclidean n → ℝ) : Set (Point n) :=
  {p | p.2 ≠ 0 ∧ IsUnit (mixedPhaseMatrix S p.1.1 p.2).det}

/-- The inverse gap at one nonzero covector persists on a neighborhood.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem isOpen_regularRegion
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) :
    IsOpen (regularRegion S) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have he (i j : Fin n) : ContinuousAt
      (fun q : Point n => mixedPhaseMatrix S q.1.1 q.2 i j) p := by
    simpa only [Function.comp_def] using
      ((ForwardRegularized.smoothAt_mixedPhaseEntry (hS _ _ hp.1) i j).comp p
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)).continuousAt
  have hm : ContinuousAt (fun q : Point n => mixedPhaseMatrix S q.1.1 q.2) p :=
    continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => he i j))
  have hd := continuous_id.matrix_det.continuousAt.comp hm
  have hη : ∀ᶠ q : Point n in 𝓝 p, q.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne hp.1
  have hdet : ∀ᶠ q : Point n in 𝓝 p, (mixedPhaseMatrix S q.1.1 q.2).det ≠ 0 :=
    hd.eventually_ne hp.2.ne_zero
  filter_upwards [hη, hdet] with q hq hdet
  exact ⟨hq, isUnit_iff_ne_zero.mpr hdet⟩

/-- Local primitive smoothness follows from the actual phase, amplitude and
inverse gap. No global smoothness of homogeneous primitives is assumed.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem smoothPrimitivesOn_regularRegion
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hA : ∀ p : Point n, p.2 ≠ 0 → ContDiffAt ℝ ∞ (uncurry A) p) :
    SmoothPrimitivesOn S A (regularRegion S) := by
  refine ⟨fun p hp => hA p hp.1, ?_⟩
  intro a p hp
  let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) a.2.2).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) a.2.1))
  have hm : ContDiffAt ℝ ∞ (fun q : Point n =>
      if a.1 then (mixedPhaseMatrix S q.1.1 q.2)⁻¹ else mixedPhaseMatrix S q.1.1 q.2) p := by
    cases ha : a.1 with
    | false =>
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Function.comp_def, Function.uncurry_def] using
        (contDiffAt_mixedPhaseMatrix_of_phase S (p.1.1, p.2) (hS _ _ hp.1)).comp p
          (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    | true =>
      simpa only [ha, ↓reduceIte, Function.comp_def] using
        (contDiffAt_mixedPhaseMatrix_inverse_of_phase S (p.1.1, p.2)
          (hS _ _ hp.1) hp.2).comp p (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp p (ev.contDiff.contDiffAt.comp p hm)
  change ContDiffAt ℝ ∞ (fun q : Point n =>
    (ev (if a.1 then (mixedPhaseMatrix S q.1.1 q.2)⁻¹ else mixedPhaseMatrix S q.1.1 q.2) : ℂ)) p at hc
  convert hc using 1
  funext q
  cases ha : a.1 <;> simp [uncurry, scalarPrimitive, ha, ev] <;> rfl

/-- A carrier gap is needed only at the physical positions of nonvanishing
jets. Source: the localization before `app:ch_regular_base:eq:fio-input`. -/
theorem mem_regularRegion_of_carrier {K : Set (Euclidean n × Euclidean n)}
    {F : Set (Euclidean n)} (hF0 : (0 : Euclidean n) ∉ F)
    (hinv : ∀ q ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S q.1 η).det)
    {p : Point n} (hp : p ∈ K ×ˢ F) : p ∈ regularRegion S := by
  have hη : p.2 ≠ 0 := fun hz => hF0 (hz ▸ hp.2)
  exact ⟨hη, hinv p.1 hp.1 p.2 hη⟩

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
