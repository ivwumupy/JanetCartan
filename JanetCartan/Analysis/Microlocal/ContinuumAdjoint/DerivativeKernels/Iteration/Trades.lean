module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration.Regularity

/-!
# One derivative of a realized expansion term

The concrete recursion agrees with the actual Fourier-side derivative. The
carrier branch uses the compact integral derivative theorem and the initial
branch uses physical multiplication by `i⟪h,η⟫`
(`app:ch_background:eq:bg-derivative-trade`).
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison AmplitudeBound
variable {n : ℕ}

/-- Every realized term is an absolutely integrable chart integral
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_realize_integrand
    {S : Set (Euclidean n)} (hS : IsCompact S) {t : AdjointDerivativeTerm n}
    (ha : SmoothSupportedAdjointAmplitude S t.amplitude)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v) (u : CarrierVariable n) :
    Integrable (fun x ↦ oscillatoryFactor (-1) (Φ u.1 x u.2) *
      (t.amplitude u.1 x u.2 * euclideanCoordinateDerivList t.dataDerivatives v x)) :=
  integrable_chartAdjoint ((hΦ u.2).comp (contDiff_const.prodMk contDiff_id))
    ((ha.smooth u.2).comp (contDiff_const.prodMk contDiff_id)).continuous
    (contDiff_euclideanCoordinateDerivList hv _).continuous
    (hS.of_isClosed_subset (isClosed_tsupport _) (ha.tsupport_subset hS.isClosed _ _))

private theorem hasDerivAt_carrier_line {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : CarrierParameter → F} (hf : Differentiable ℝ f)
    (z h : CarrierParameter) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • h)) (fderiv ℝ f z h) 0 := by
  have he : HasDerivAt (fun s : ℝ ↦ z + s • h) h 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z)
  simpa only [Function.comp_def, zero_smul, add_zero] using
    (hf (z + (0 : ℝ) • h)).hasFDerivAt.comp_hasDerivAt 0 he

/-- Finite sums of the branch integrals can be collected into the one-step
trade integrand; compact support proves every integrability premise
(`app:ch_background:prop:bg-adjoint`). -/
theorem sum_realize_differentiateAdjointTerm
    {S : Set (Euclidean n)} (hS : IsCompact S) {t : AdjointDerivativeTerm n}
    (ha : SmoothSupportedAdjointAmplitude S t.amplitude)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (d : InitialCarrierDerivative n) (u : CarrierVariable n) :
    ((differentiateAdjointTerm L V d t).map (fun q ↦ q.realize Φ v u)).sum =
      ∫ x, oscillatoryFactor (-1) (Φ u.1 x u.2) *
        (zeroBranchAmplitude L V d t.amplitude u.1 x u.2 *
            euclideanCoordinateDerivList t.dataDerivatives v x +
          ∑ j, firstBranchAmplitude L V d t.amplitude j u.1 x u.2 *
            partialDeriv (euclideanCoordinateDerivList t.dataDerivatives v) x j) := by
  have h0 := integrable_realize_integrand hS
    (t := ⟨zeroBranchAmplitude L V d t.amplitude, t.dataDerivatives⟩)
    (ha.zeroBranch hS.isClosed hL hV d) hΦ hv u
  have h1 (j) := integrable_realize_integrand hS
    (t := ⟨firstBranchAmplitude L V d t.amplitude j, j :: t.dataDerivatives⟩)
    (ha.firstBranch hL hV d j) hΦ hv u
  simp only [differentiateAdjointTerm, List.map_cons, List.map_ofFn, List.sum_cons,
    List.sum_ofFn, Function.comp_def, AdjointDerivativeTerm.realize, chartAdjoint,
    euclideanCoordinateDerivList, partialDeriv] at *
  simp_rw [mul_add, Finset.mul_sum]
  rw [integral_add h0 (integrable_finsetSum _ (fun j _ ↦ h1 j)),
    integral_finsetSum _ (fun j _ ↦ h1 j)]

/-- One actual derivative of a realized term equals the constructed `n+1`
branches. The phase identities are needed only on the common measurement
support (`app:ch_background:eq:bg-derivative-trade`). -/
theorem applyInitialCarrierDerivative_realize
    {S : Set (Euclidean n)} (hS : IsCompact S) {t : AdjointDerivativeTerm n}
    (ha : SmoothSupportedAdjointAmplitude S t.amplitude)
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
    (d : InitialCarrierDerivative n) (u : CarrierVariable n) :
    applyInitialCarrierDerivative d (t.realize Φ v) u =
      ((differentiateAdjointTerm L V d t).map (fun q ↦ q.realize Φ v u)).sum := by
  rw [sum_realize_differentiateAdjointTerm hS ha hL hV hΦ hv]
  have hw := contDiff_euclideanCoordinateDerivList hv t.dataDerivatives
  have has (x) (hx : t.amplitude u.1 x u.2 ≠ 0) : x ∈ S := by
    by_contra hn
    exact hx (ha.zero_off _ _ _ hn)
  cases d with
  | initial h =>
    exact chartAdjoint_initial_trade
      ((hΦ u.2).comp (contDiff_const.prodMk contDiff_id))
      ((ha.smooth u.2).comp (contDiff_const.prodMk contDiff_id)) hw
      ((hL h).comp (contDiff_const.prodMk contDiff_id))
      (hS.of_isClosed_subset (isClosed_tsupport _) (ha.tsupport_subset hS.isClosed _ _))
      (inner ℝ h u.2) (fun x hx ↦ hphaseL _ _ _ _ (has x hx))
  | carrier h =>
    have hp : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ (u.1 + p.1 • h, p.2)) :=
      (contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd
    have hderA (x) : deriv (fun s : ℝ ↦ t.amplitude (u.1 + s • h) x u.2) 0 =
        fderiv ℝ (fun z ↦ t.amplitude z x u.2) u.1 h :=
      (hasDerivAt_carrier_line
        (((ha.smooth u.2).comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp)) u.1 h).deriv
    have hderΦ (x) : deriv (fun s : ℝ ↦ Φ (u.1 + s • h) x u.2) 0 =
        fderiv ℝ (fun z ↦ Φ z x u.2) u.1 h :=
      (hasDerivAt_carrier_line
        (((hΦ u.2).comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp)) u.1 h).deriv
    have hd := hasDerivAt_chartAdjoint_carrier (U := univ) isOpen_univ hS
      ((hΦ u.2).comp hp) ((ha.smooth u.2).comp hp)
      ((hV h).comp ((contDiff_const (c := u.1)).prodMk contDiff_id)) hw
      (fun s _ ↦ ha.tsupport_subset hS.isClosed (u.1 + s • h) u.2)
      (s := 0) (mem_univ _) (fun x hx ↦ by
        simpa only [Function.comp_def, zero_smul, add_zero, hderΦ, id_eq] using hphaseV u.1 x u.2 h
          (has x (by simpa only [Function.comp_def, zero_smul, add_zero] using hx)))
    have hd' := hasDerivAt_carrier_line
      ((contDiff_chartAdjoint_carrier hS ha hΦ hw u.2).differentiable (by simp)) u.1 h
    have he := hd'.unique hd
    simpa only [Function.comp_def, zero_smul, add_zero, hderA, id_eq,
      applyInitialCarrierDerivative, AdjointDerivativeTerm.realize, zeroBranchAmplitude,
      firstBranchAmplitude] using he

end JanetCartan.ContinuumAdjoint.DerivativeKernels
