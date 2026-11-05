module

public import JanetCartan.Iteration.PhysicalSamplingShells.Space

/-!
# Original sample and shell coordinates

The two sharp pieces of every original band remain grouped inside each sample
coordinate. These exact Hilbert equivalences retain all input coordinates for
`app:ch_waves:eq:sampling-prefix-normal` and `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace JanetCartan.PhysicalSamplingShells
open RawInputPartition RawInputRealization

variable {ι : Type*} [Fintype ι] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Flatten only the finite label pair. No frequency annuli are collapsed. -/
def sampledInputFlatten (n J : ℕ) :
    PiLp 2 (fun _ : ι ↦ PiLp 2 (fun i : RefinedIndex J ↦ Lp V 2 (annularMeasure n (refinedRadius i)))) ≃ₗᵢ[ℂ]
      PiLp 2 (fun i : ι × RefinedIndex J ↦ Lp V 2 (annularMeasure n (refinedRadius i.2))) where
  toFun f := WithLp.toLp 2 (fun i ↦ f i.1 i.2)
  invFun f := WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (fun j ↦ f (i, j)))
  left_inv f := by
    apply PiLp.ext
    intro i
    apply PiLp.ext
    intro j
    rfl
  right_inv f := by
    apply PiLp.ext
    intro i
    rfl
  map_add' f g := by
    apply PiLp.ext
    intro i
    rfl
  map_smul' c f := by
    apply PiLp.ext
    intro i
    rfl
  norm_map' f := by
    change ‖WithLp.toLp 2 (fun i : ι × RefinedIndex J ↦ f i.1 i.2)‖ = ‖f‖
    have hs : ‖WithLp.toLp 2 (fun i : ι × RefinedIndex J ↦ f i.1 i.2)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      exact (PiLp.norm_sq_eq_of_L2 _ (f i)).symm
    nlinarith [norm_nonneg f, norm_nonneg
      (WithLp.toLp 2 (fun i : ι × RefinedIndex J ↦ f i.1 i.2))]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Literal counting over original samples and shell copies, with the original
annular Lebesgue measure on each copy; square-root sample weights remain in the
kernel, not in this measure. -/
abbrev sampledShellMeasure (n J : ℕ) : Measure ((ι × RefinedIndex J) × Euclidean (n - 1)) :=
  annularShellMeasure (fun i : ι × RefinedIndex J ↦ refinedRadius i.2)

/-- The exact native scalar or vector L² realization of the original sampled
nested Hilbert input (`new:eq:amplitude-test`). -/
def sampledShellEquiv (n J : ℕ) :
    Lp V 2 (sampledShellMeasure (ι := ι) n J) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : ι ↦ PiLp 2 (fun i : RefinedIndex J ↦ Lp V 2 (annularMeasure n (refinedRadius i)))) :=
  (annularShellEquiv (fun i : ι × RefinedIndex J ↦ refinedRadius i.2)).trans
    (sampledInputFlatten n J).symm

/-- Exact same-frequency representative of every original sample/shell slice. -/
theorem sampledShellEquiv_ae (n J : ℕ)
    (f : Lp V 2 (sampledShellMeasure (ι := ι) n J)) (i : ι) (j : RefinedIndex J) :
    sampledShellEquiv n J f i j =ᵐ[annularMeasure n (refinedRadius j)] fun η ↦ f ((i, j), η) :=
  annularShellEquiv_ae (fun k : ι × RefinedIndex J ↦ refinedRadius k.2) f (i, j)

/-- The reverse realization preserves every original shell representative too;
this is the input reassembly used for the native matrix amplitude row. -/
theorem sampledShellEquiv_symm_ae (n J : ℕ)
    (f : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun i : RefinedIndex J ↦ Lp V 2 (annularMeasure n (refinedRadius i))))) :
    (sampledShellEquiv n J).symm f =ᵐ[sampledShellMeasure n J]
      fun x ↦ f x.1.1 x.1.2 x.2 := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  have he := sampledShellEquiv_ae n J ((sampledShellEquiv n J).symm f) i.1 i.2
  rw [(sampledShellEquiv n J).apply_symm_apply] at he
  exact he.symm

end JanetCartan.PhysicalSamplingShells
