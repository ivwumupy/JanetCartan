module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.RegularizedBound
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CutoffReserve
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Limit

/-!
# The modified half-order carrier L² bound

The estimate for an arbitrary full modified amplitude in
`app:ch_background:prop:bg-adjoint`. The primitive half-order jets and weighted
conic geometry produce the order-zero normal estimate. The concrete compact
cutoffs have a proved uniform primitive reserve and converge to one. Fatou
then constructs the unique bounded realization of the literal `chartAdjoint`
on all Euclidean measurement L² data, with carrier measure exactly `dz dη`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol
variable {n : ℕ}

/-- Low L² bound for any full half-order modified amplitude, independently
of the expansion recursion (`app:ch_background:prop:bg-adjoint`). The constant
is chosen before the amplitude and its budget. All remaining assumptions are
primitive symbol jets, genuine conic geometry, and compact supports of the
original regularized density; no normal identity or operator estimate is an
input. The compact-image sets may grow with the cutoff index without changing
the constant. Both physical positions, all masks, and the degree-one Jacobian
are retained throughout the proof. -/
theorem exists_modifiedAdjoint_L2_bound
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (g : Chart n) (s : JetRescaling g) (ρ B c : ℝ)
    (L : Set (JointVariables n)) (V : Set (Euclidean 2))
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L V)
    (X : Set (Euclidean n)) (hX : IsCompact X) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (hn : 0 < n) :
    ∃ Q ≥ 0, ∀ (a : AdjointAmplitude n) (A : ℝ)
      (_hr : PrimitiveRegularity g a (fun _ ↦ 1))
      (_hamp : PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X V Z Ω L a)
    (_he : MeasurePreserving g.coordinates volume (volume.prod volume))
    (C : ℕ → Euclidean n → Euclidean n → Set (Euclidean 2 × Euclidean n))
    (_hC : ∀ k x y, IsCompact (C k x y))
    (_hCD : ∀ k x y p, p ∈ C k x y → p.2 ∈ g.domain x y p.1)
    (_hΨc : ∀ k x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) (C k x y))
    (_hUc : ∀ k x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.inverse x y p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, g.forward x y p.1 p.2)) '' C k x y))
    (_hJc : ∀ k x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ g.jacobian x y p.1 p.2)
      (C k x y))
    (_hD : ∀ x y v, MeasurableSet (g.domain x y v))
    (_hΨ : ∀ x y v t, t ∈ g.domain x y v →
      HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v t) (g.domain x y v) t)
    (_hinj : ∀ x y v, InjOn (g.forward x y v) (g.domain x y v))
    (_hU : ∀ x y v t, t ∈ g.domain x y v → g.inverse x y v (g.forward x y v t) = t)
    (_hsupp : ∀ k x y p, p ∉ C k x y → modifiedNormalDensity a (modifiedCarrierCutoff k) x y
      (TransportKernel.chartCarrierVariable g.coordinates p.1 p.2) = 0)
    (_hphase : ∀ x y v t, t ∈ g.domain x y v →
      Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 x
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 -
        Φ (TransportKernel.chartCarrierVariable g.coordinates v t).1 y
          (TransportKernel.chartCarrierVariable g.coordinates v t).2 =
          inner ℝ (x - y) (g.forward x y v t))
    (S : ℕ → Euclidean n → Set (SourceChartVariables n)) (_hS : ∀ k x, IsCompact (S k x))
    (_hSC : ∀ k x y v t, (v, t) ∈ C k x y → (y, v, t) ∈ S k x)
    (_hSf : ∀ k x, ContinuousOn (fun p : SourceChartVariables n ↦
      g.forward x p.1 p.2.1 p.2.2) (S k x))
    , ∃ U : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
      ‖U‖ ≤ Q * A ∧
      (∀ f, U f =ᵐ[carrierMeasure n] fun u ↦
        chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f) ∧
      (∀ f : Lp (α := Euclidean n) ℂ 2, MemLp (fun u ↦
        chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f)
          2 (carrierMeasure n) ∧
        (eLpNorm (fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f)
          2 (carrierMeasure n)).toReal ≤ (Q * A) * ‖f‖) ∧
      ∀ W : Lp (α := Euclidean n) ℂ 2 →L[ℂ] CarrierL2 n,
        (∀ f, W f =ᵐ[carrierMeasure n] fun u ↦
          chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f) → W = U := by
  obtain ⟨M, _, hmj⟩ := exists_uniform_modifiedCarrierCutoff_reserve (n := n)
    (2 * (n + 1)) hg.threshold_pos
  obtain ⟨R, hR⟩ := hX.isBounded.exists_norm_le
  have hXR : ∀ x ∈ X, ∀ i, |x i| ≤ R := by
    intro x hx i
    exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  obtain ⟨Q, hQ, hq⟩ := exists_uniform_modifiedCarrierOperator_adjoint_bound Φ hΦ
    g s ρ B c L V hg X hX Z Ω M hn R hXR
  refine ⟨Q, hQ, ?_⟩
  intro a A hr hamp he C hC hCD hΨc hUc hJc hD hΨ hinj hU hsupp hphase S hS hSC hSf
  have ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2) :=
    hr.amplitude.continuous.comp
      (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
  have has : ∀ u : CarrierVariable n, ∀ x, x ∉ X → a u.1 x u.2 = 0 := by
    intro u x hx
    by_contra hne
    exact hx (hamp.compact_supports.amplitude_support _ _ _ hne).1
  have hreg (k : ℕ) : PrimitiveRegularity g a (modifiedCarrierCutoff k) :=
    ⟨hr.coordinates, hr.amplitude, contDiff_modifiedCarrierCutoff k, hr.jacobian,
      hr.determinant_ne_zero, hr.output_open, hr.inverse, hr.inverse_mem, hr.right_inverse⟩
  have hJ : ∀ x y v t, t ∈ g.domain x y v → (g.jacobian x y v t).det ≠ 0 :=
    fun x y v t ht ↦ hr.determinant_ne_zero ((x, y, t), v) ht
  let T (k : ℕ) := (modifiedCarrierOperator Φ a (modifiedCarrierCutoff k) hΦ ha
    (contDiff_modifiedCarrierCutoff k).continuous (hasCompactSupport_modifiedCarrierCutoff k)
    hX has).adjoint
  have hb (k : ℕ) : ‖T k‖ ≤ Q * A := hq a (modifiedCarrierCutoff k) A ha
    (contDiff_modifiedCarrierCutoff k).continuous (hasCompactSupport_modifiedCarrierCutoff k)
    has (hreg k) hamp (hmj k) he (C k) (hC k) (hCD k) (hΨc k) (hUc k) (hJc k)
    hD hΨ hinj hU hJ (hsupp k) hphase (S k) (hS k) (hSC k) (hSf k)
  have hl (f : Lp (α := Euclidean n) ℂ 2) : ∀ᵐ u ∂carrierMeasure n,
      Tendsto (fun k ↦ T k f u) atTop
        (𝓝 (chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f)) := by
    have heq : ∀ᵐ u ∂carrierMeasure n, ∀ k, T k f u =
        (modifiedCarrierCutoff k u : ℂ) *
          chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f :=
      ae_all_iff.mpr (fun k ↦ modifiedCarrierOperator_adjoint_ae Φ a
        (modifiedCarrierCutoff k) hΦ ha (contDiff_modifiedCarrierCutoff k).continuous
        (hasCompactSupport_modifiedCarrierCutoff k) hX has f)
    filter_upwards [heq] with u hu
    have hlim := ((Complex.continuous_ofReal.tendsto 1).comp
      (tendsto_modifiedCarrierCutoff u)).mul_const
        (chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f)
    simpa only [Function.comp_def, ← hu, Complex.ofReal_one, one_mul] using hlim
  obtain ⟨U, hUn, hUa, huniq⟩ := exists_modifiedAdjointLimit_operator T _
    (mul_nonneg hQ hamp.budget_nonneg) hb hl
  refine ⟨U, hUn, hUa, ?_, huniq⟩
  intro f
  refine ⟨(Lp.memLp (U f)).ae_eq (hUa f), ?_⟩
  rw [← eLpNorm_congr_ae (hUa f), ← Lp.norm_def]
  exact (U.le_opNorm f).trans (mul_le_mul_of_nonneg_right hUn (norm_nonneg f))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
