module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.ZeroOrder
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Scale

/-!
# Smooth finite families for the current mean

The actual smooth periodic functions underlying `main:lem:mean-recurrence`.
The submodule requires smoothness, rather than bounds or conclusions of the
recurrence. Compactness then justifies the Cʳ seminorm laws.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CurrentMean

variable {d : ℕ} {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:mean-recurrence`: finite families of actual smooth periodic fields.
Specialize `F` to complex matrices with the Frobenius norm for derivative changes. -/
def smoothPeriodicFamily (d : ℕ) (ι F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Submodule ℝ (Torus d → ι → F) where
  carrier := {D | ∀ i, IsSmoothPeriodic (fun x ↦ D x i)}
  zero_mem' := fun _ ↦ ⟨continuous_const, contDiff_const⟩
  add_mem' hD hE i := ⟨(hD i).1.add (hE i).1, (hD i).2.add (hE i).2⟩
  smul_mem' c _ hD i := ⟨(hD i).1.const_smul c, (hD i).2.const_smul c⟩

/-- `main:lem:mean-recurrence`: the shared domain of all weighted seminorms. -/
abbrev SmoothPeriodicFamily (d : ℕ) (ι F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] := smoothPeriodicFamily d ι F

namespace SmoothPeriodicFamily

/-- `main:lem:mean-recurrence`: each component is genuinely smooth on the torus. -/
theorem smooth (D : SmoothPeriodicFamily d ι F) (i : ι) :
    IsSmoothPeriodic (fun x ↦ D.val x i) := D.property i

/-- `main:lem:mean-recurrence`: compactness supplies square integrability. -/
theorem memLp (D : SmoothPeriodicFamily d ι F) (i : ι) :
    MemLp (fun x ↦ D.val x i) 2 volume :=
  (smooth D i).1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `main:lem:mean-recurrence`: the individual Cʳ seminorm on the smooth domain. -/
def componentCSeminorm (r : ℕ) (i : ι) : Seminorm ℝ (SmoothPeriodicFamily d ι F) where
  toFun D := cNorm (fundamentalCell d) r (periodicLift (fun x ↦ D.val x i))
  map_zero' := cNorm_zero _ _
  add_le' D E := cNorm_add_le (isCompact_fundamentalCell d)
    ((smooth D i).2.of_le (by simp)) ((smooth E i).2.of_le (by simp))
  neg' D := cNorm_neg _ _ _
  smul' c D := cNorm_smul c ((smooth D i).2.of_le (by simp))

/-- `main:lem:mean-recurrence`: the component as an actual real L² class. -/
def componentL2 (i : ι) : SmoothPeriodicFamily d ι F →ₗ[ℝ] PeriodicL2 d F where
  toFun D := (memLp D i).toLp (fun x ↦ D.val x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `main:eq:full-recursion`: the L² realization retains its actual representative. -/
theorem componentL2_coe_ae (i : ι) (D : SmoothPeriodicFamily d ι F) :
    componentL2 i D =ᵐ[volume] (fun x ↦ D.val x i) := (memLp D i).coeFn_toLp

end SmoothPeriodicFamily

section Weighted

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [Fintype ι]

/-- `main:lem:mean-recurrence`: Euclidean vector of weighted component sizes. -/
def seminormVector (μ : ι → ℝ) (p : ι → Seminorm ℝ X) (x : X) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i ↦ Real.sqrt (μ i) * p i x)

/-- `main:lem:mean-recurrence`: Euclidean norm equals the weighted square sum. -/
theorem norm_seminormVector (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (p : ι → Seminorm ℝ X) (x : X) :
    ‖seminormVector μ p x‖ = Real.sqrt (∑ i, μ i * p i x ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp only [seminormVector, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs,
    mul_pow, Real.sq_sqrt (hμ _)]

/-- `main:lem:mean-recurrence`: square-sum aggregation of component seminorms.
Zero weights are allowed; its triangle constant is exactly one. -/
def weightedSquareSeminorm (μ : ι → ℝ) (_hμ : ∀ i, 0 ≤ μ i)
    (p : ι → Seminorm ℝ X) : Seminorm ℝ X where
  toFun x := ‖seminormVector μ p x‖
  map_zero' := by
    change ‖WithLp.toLp 2 (fun i ↦ Real.sqrt (μ i) * p i 0)‖ = 0
    simp only [map_zero, mul_zero]
    exact norm_zero
  add_le' x y := by
    apply le_trans _ (norm_add_le (seminormVector μ p x) (seminormVector μ p y))
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    simp only [seminormVector, PiLp.add_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    apply pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg (p i) _))
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (map_add_le_add (p i) x y)
      (Real.sqrt_nonneg (μ i))
  neg' x := by simp [seminormVector]
  smul' c x := by
    have h : seminormVector μ p (c • x) = ‖c‖ • seminormVector μ p x := by
      ext i
      simp [seminormVector, map_smul_eq_mul, mul_left_comm]
    rw [h, norm_smul, norm_norm]

/-- `main:lem:mean-recurrence`: exact agreement with the paper's square-sum convention. -/
theorem weightedSquareSeminorm_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (p : ι → Seminorm ℝ X) (x : X) :
    weightedSquareSeminorm μ hμ p x = Real.sqrt (∑ i, μ i * p i x ^ 2) :=
  norm_seminormVector μ hμ p x

end Weighted

namespace SmoothPeriodicFamily

variable [Fintype ι]

/-- `main:lem:mean-recurrence`: the actual weighted Cʳ seminorm for accumulated changes. -/
def cSeminorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (r : ℕ) :
    Seminorm ℝ (SmoothPeriodicFamily d ι F) :=
  weightedSquareSeminorm μ hμ (componentCSeminorm r)

/-- `main:lem:mean-recurrence`: exact agreement with the existing weighted Cʳ size. -/
theorem cSeminorm_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (r : ℕ)
    (D : SmoothPeriodicFamily d ι F) :
    cSeminorm μ hμ r D = weightedPeriodicCNorm μ r D.val :=
  weightedSquareSeminorm_eq μ hμ _ D

end SmoothPeriodicFamily
end JanetCartan.CurrentMean
