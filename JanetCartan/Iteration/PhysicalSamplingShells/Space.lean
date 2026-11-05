module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinementSpaces
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The original annular inputs on a disjoint finite shell space

Consumer: the scalar and matrix physical amplitude test
`app:ch_osc:eq:amplitude-row`. Each sample/band label retains its own copy of
the original annular Lebesgue measure. No overlapping frequencies are merged,
and no sample weight is divided out.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace JanetCartan.PhysicalSamplingShells
open RawInputRealization

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {n : ℕ} (radius : ι → ℝ)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A literal disjoint union of original annular frequency measures. The label
is retained even when two annuli coincide (`new:eq:amplitude-test`). -/
def annularShellMeasure : Measure (ι × Euclidean (n - 1)) :=
  Measure.sum (fun i ↦ (annularMeasure n (radius i)).map (Prod.mk i))

instance : IsFiniteMeasure (annularShellMeasure (n := n) radius) := by
  unfold annularShellMeasure
  rw [Measure.sum_fintype]
  infer_instance

/-- Restrict an actual shell-space datum to one original annulus. -/
def annularShellSlice (f : Lp V 2 (annularShellMeasure (n := n) radius)) (i : ι) :
    Lp V 2 (annularMeasure n (radius i)) :=
  (((Lp.memLp f).mono_measure (Measure.le_sum _ i)).comp_of_map
    (measurable_prodMk_left.aemeasurable)).toLp (fun η ↦ f (i, η))

omit [Fintype ι] [MeasurableSingletonClass ι] [InnerProductSpace ℂ V] in
/-- The slice uses the same datum representative on its original shell. -/
theorem annularShellSlice_ae
    (f : Lp V 2 (annularShellMeasure (n := n) radius)) (i : ι) :
    annularShellSlice radius f i =ᵐ[annularMeasure n (radius i)] fun η ↦ f (i, η) :=
  MemLp.coeFn_toLp _

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- Almost-everywhere identities on the disjoint space hold on every literal
annular component, including the zero-measure component. -/
theorem ae_annularShell_slice {P : ι × Euclidean (n - 1) → Prop}
    (h : ∀ᵐ x ∂annularShellMeasure radius, P x) (i : ι) :
    ∀ᵐ η ∂annularMeasure n (radius i), P (i, η) :=
  ae_of_ae_map measurable_prodMk_left.aemeasurable (ae_mono (Measure.le_sum _ i) h)

/-- Assemble the restrictions in the original finite Hilbert sum, without a
cardinality factor (`app:ch_waves:eq:sampling-prefix-normal`). -/
def annularShellUnpack : Lp V 2 (annularShellMeasure (n := n) radius) →ₗ[ℂ]
    PiLp 2 (fun i ↦ Lp V 2 (annularMeasure n (radius i))) where
  toFun f := WithLp.toLp 2 (annularShellSlice radius f)
  map_add' f g := by
    apply PiLp.ext
    intro i
    apply Lp.ext
    filter_upwards [annularShellSlice_ae radius (f + g) i,
      annularShellSlice_ae radius f i, annularShellSlice_ae radius g i,
      Lp.coeFn_add (annularShellSlice radius f i) (annularShellSlice radius g i),
      ae_annularShell_slice radius (Lp.coeFn_add f g) i] with η hs hf hg ha he
    change annularShellSlice radius (f + g) i η =
      (annularShellSlice radius f i + annularShellSlice radius g i) η
    rw [hs, he, ha]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply PiLp.ext
    intro i
    apply Lp.ext
    filter_upwards [annularShellSlice_ae radius (c • f) i,
      annularShellSlice_ae radius f i,
      Lp.coeFn_smul c (annularShellSlice radius f i),
      ae_annularShell_slice radius (Lp.coeFn_smul c f) i] with η hs hf ha he
    change annularShellSlice radius (c • f) i η = (c • annularShellSlice radius f i) η
    rw [hs, he, ha]
    simp only [Pi.smul_apply, hf]

/-- The shell decomposition preserves the literal Hilbert inner product. -/
theorem inner_annularShellUnpack
    (f g : Lp V 2 (annularShellMeasure (n := n) radius)) :
    inner ℂ (annularShellUnpack radius f) (annularShellUnpack radius g) = inner ℂ f g := by
  rw [PiLp.inner_apply, L2.inner_def]
  change (∑ i, inner ℂ (annularShellSlice radius f i) (annularShellSlice radius g i)) =
    ∫ x, inner ℂ (f x) (g x) ∂Measure.sum
      (fun i ↦ (annularMeasure n (radius i)).map (Prod.mk i))
  rw [integral_sum_measure (L2.integrable_inner f g), tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def, (measurableEmbedding_prodMk_left i).integral_map]
  apply integral_congr_ae
  filter_upwards [annularShellSlice_ae radius f i, annularShellSlice_ae radius g i] with η hf hg
  change inner ℂ (annularShellSlice radius f i η) (annularShellSlice radius g i η) = _
  rw [hf, hg]

/-- The disjoint-shell decomposition is isometric, not merely a bound with a
shell-count or logarithmic loss (`new:eq:amplitude-test`). -/
def annularShellIsometry : Lp V 2 (annularShellMeasure (n := n) radius) →ₗᵢ[ℂ]
    PiLp 2 (fun i ↦ Lp V 2 (annularMeasure n (radius i))) where
  toLinearMap := annularShellUnpack radius
  norm_map' f := by
    have he : ‖annularShellUnpack radius f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
        inner_annularShellUnpack]
    nlinarith [norm_nonneg f, norm_nonneg (annularShellUnpack radius f)]

omit [InnerProductSpace ℂ V] in
/-- The original finite annular data define an actual datum on the disjoint
space, with unchanged values on each frequency shell. -/
theorem memLp_annularShell_pack
    (f : PiLp 2 (fun i ↦ Lp V 2 (annularMeasure n (radius i)))) :
    MemLp (fun x : ι × Euclidean (n - 1) ↦ f x.1 x.2) 2 (annularShellMeasure radius) := by
  have hm : AEStronglyMeasurable (fun x : ι × Euclidean (n - 1) ↦ f x.1 x.2)
      (annularShellMeasure radius) := by
    apply aestronglyMeasurable_sum_measure_iff.mpr
    intro i
    exact (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
      (Lp.aestronglyMeasurable (f i))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  unfold annularShellMeasure
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (measurableEmbedding_prodMk_left i).integrable_map_iff.mpr
    ((Lp.memLp (f i)).integrable_norm_pow (by norm_num))

/-- The actual shell decomposition is onto the original finite annular input;
there is no discarded coordinate or changed input norm. -/
theorem annularShellIsometry_surjective :
    Function.Surjective (annularShellIsometry (V := V) (n := n) radius) := by
  intro f
  let g := (memLp_annularShell_pack radius f).toLp
    (fun x : ι × Euclidean (n - 1) ↦ f x.1 x.2)
  refine ⟨g, ?_⟩
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [annularShellSlice_ae radius g i,
    ae_annularShell_slice radius (memLp_annularShell_pack radius f).coeFn_toLp i] with η hs hg
  change annularShellSlice radius g i η = f i η
  exact hs.trans hg

/-- Exact complex L² identification of the original finite annular input with
its disjoint frequency realization. Both complex quadratures are retained. -/
def annularShellEquiv : Lp V 2 (annularShellMeasure (n := n) radius) ≃ₗᵢ[ℂ]
    PiLp 2 (fun i ↦ Lp V 2 (annularMeasure n (radius i))) :=
  LinearIsometryEquiv.ofSurjective (annularShellIsometry radius)
    (annularShellIsometry_surjective radius)

/-- Literal shell formula for the input identification. -/
theorem annularShellEquiv_ae
    (f : Lp V 2 (annularShellMeasure (n := n) radius)) (i : ι) :
    annularShellEquiv radius f i =ᵐ[annularMeasure n (radius i)] fun η ↦ f (i, η) :=
  annularShellSlice_ae radius f i

end JanetCartan.PhysicalSamplingShells
