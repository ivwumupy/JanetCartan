module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Integrability
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison.Coordinates
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison.SmoothSymmetry
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison.SymmetricJetBound

/-!
# Comparison of Cartesian and Fréchet derivative energies

For `app:ch_regular_base:eq:ball-extension-sobolev`, the Cartesian and Fréchet
energies are equivalent with positive constants depending only on dimension and
order. Symmetry of smooth jets supplies the reverse pointwise estimate, which
we integrate on the open ball and on the whole space for the fixed Seeley
extension. Only closed-ball smoothness of the input is required. All dimensions,
including zero and one, are covered.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.BallExtension

variable {n : ℕ}

/-- A positive dimension-and-order constant for the easy direction of the
energy comparison in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
def cartesianEnergyComparisonConstant (n m : ℕ) : ℝ :=
  (sobolevMultiindices n m).card + 1

/-- The comparison constant is positive, including dimensions zero and one
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianEnergyComparisonConstant_pos (n m : ℕ) :
    0 < cartesianEnergyComparisonConstant n m := by
  unfold cartesianEnergyComparisonConstant
  positivity

/-- Squared Cartesian evaluations are bounded by squared Fréchet operator norms
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem sq_cartesianDerivativeWithin_le (α : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    cartesianDerivativeWithin α f s x ^ 2 ≤
      ‖iteratedFDerivWithin ℝ (∑ i, α i) f s x‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_cartesianDerivativeWithin_le α f s x) 2

/-- Pointwise comparison of the finite jets in the manuscript's derivative norm
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem sum_sq_cartesianDerivativeWithin_le (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ α ∈ sobolevMultiindices n m,
      cartesianDerivativeWithin (fun i ↦ α (some i)) f s x ^ 2) ≤
    cartesianEnergyComparisonConstant n m *
      ∑ j ∈ Finset.range (m + 1), ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2 := by
  have hterm : ∀ α ∈ sobolevMultiindices n m,
      cartesianDerivativeWithin (fun i ↦ α (some i)) f s x ^ 2 ≤
        ∑ j ∈ Finset.range (m + 1), ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2 := by
    intro α hα
    apply (sq_cartesianDerivativeWithin_le _ f s x).trans
    apply Finset.single_le_sum
      (f := fun j ↦ ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2)
      (a := ∑ i, α (some i)) (fun _ _ ↦ sq_nonneg _)
    have := mem_sobolevMultiindices.mp hα
    simp only [Finset.mem_range]
    omega
  calc
    _ ≤ ∑ _α ∈ sobolevMultiindices n m,
        ∑ j ∈ Finset.range (m + 1), ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2 :=
      Finset.sum_le_sum hterm
    _ = ((sobolevMultiindices n m).card : ℝ) *
        ∑ j ∈ Finset.range (m + 1), ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2 := by
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simp [cartesianEnergyComparisonConstant])
      (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

/-- Integrating the pointwise comparison gives the easy energy bound. The
integrability premises are discharged for the ball and actual Seeley extension
below (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianSobolevEnergy_le_mul_frechetSobolevEnergy
    (s : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hc : ∀ α ∈ sobolevMultiindices n m,
      IntegrableOn (fun x ↦ cartesianDerivativeWithin (fun i ↦ α (some i)) f s x ^ 2) s)
    (hf : ∀ j ∈ Finset.range (m + 1),
      IntegrableOn (fun x ↦ ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2) s) :
    cartesianSobolevEnergy s m f ≤
      cartesianEnergyComparisonConstant n m * frechetSobolevEnergy s m f := by
  unfold cartesianSobolevEnergy frechetSobolevEnergy
  rw [← integral_finsetSum _ hc, ← integral_finsetSum _ hf, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ hc)
    ((integrable_finsetSum _ hf).const_mul _) (sum_sq_cartesianDerivativeWithin_le m f s)

/-- A positive dimension-and-order constant for the reverse jet and energy
comparison in `app:ch_regular_base:eq:ball-extension-sobolev`. Its choice is
independent of the domain, function, and extension parameters. -/
def frechetEnergyComparisonConstant (n m : ℕ) : ℝ :=
  (exists_pos_symmetricJet_norm_sq_le_cartesian n m).choose

/-- Positivity of the reverse comparison constant, including dimensions zero
and one (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem frechetEnergyComparisonConstant_pos (n m : ℕ) :
    0 < frechetEnergyComparisonConstant n m :=
  (exists_pos_symmetricJet_norm_sq_le_cartesian n m).choose_spec.1

/-- Smoothness on the open domain gives symmetry of every jet and hence the
reverse pointwise comparison with canonical Cartesian evaluations, as needed
for `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem sum_sq_norm_iteratedFDerivWithin_le (m : ℕ)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f s)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) :
    (∑ j ∈ Finset.range (m + 1), ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2) ≤
      frechetEnergyComparisonConstant n m *
        ∑ α ∈ sobolevMultiindices n m,
          cartesianDerivativeWithin (fun i ↦ α (some i)) f s x ^ 2 := by
  exact (exists_pos_symmetricJet_norm_sq_le_cartesian n m).choose_spec.2
    (fun j ↦ iteratedFDerivWithin ℝ j f s x)
    (fun j _ v σ ↦ iteratedFDerivWithin_comp_perm_of_contDiffOn hs hf hx j v σ)

/-- Integrate the reverse comparison on an open set. The ball and fixed
extension specializations below discharge all integrability premises
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem frechetSobolevEnergy_le_mul_cartesianSobolevEnergy
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s) (m : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f s)
    (hc : ∀ α ∈ sobolevMultiindices n m,
      IntegrableOn (fun x ↦ cartesianDerivativeWithin (fun i ↦ α (some i)) f s x ^ 2) s)
    (hF : ∀ j ∈ Finset.range (m + 1),
      IntegrableOn (fun x ↦ ‖iteratedFDerivWithin ℝ j f s x‖ ^ 2) s) :
    frechetSobolevEnergy s m f ≤
      frechetEnergyComparisonConstant n m * cartesianSobolevEnergy s m f := by
  unfold cartesianSobolevEnergy frechetSobolevEnergy
  rw [← integral_finsetSum _ hc, ← integral_finsetSum _ hF, ← integral_const_mul]
  exact setIntegral_mono_on (integrable_finsetSum _ hF)
    ((integrable_finsetSum _ hc).const_mul _) hs.measurableSet
    (fun _ hx ↦ sum_sq_norm_iteratedFDerivWithin_le m hs hf hx)

namespace Parameters

variable (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- The input Cartesian energy is bounded by the intrinsic Fréchet energy with
a constant independent of the ball and function. Closed-ball smoothness suffices
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianSobolevEnergy_ball_le_mul_frechetSobolevEnergy
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    cartesianSobolevEnergy (ball p.center p.radius) m f ≤
      cartesianEnergyComparisonConstant n m *
        frechetSobolevEnergy (ball p.center p.radius) m f :=
  cartesianSobolevEnergy_le_mul_frechetSobolevEnergy _ m f
    (fun _ _ ↦ p.integrableOn_sq_cartesianDerivativeWithin_ball hf _)
    (fun _ _ ↦ p.integrableOn_sq_norm_iteratedFDerivWithin_ball hf _)

/-- The whole-space Cartesian energy of the fixed Seeley extension is bounded
by its Fréchet energy with the same dimension-and-order constant
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem cartesianSobolevEnergy_extend_le_mul_frechetSobolevEnergy
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
      cartesianEnergyComparisonConstant n m *
        frechetSobolevEnergy univ m (p.extend Seeley.coeff f) := by
  apply cartesianSobolevEnergy_le_mul_frechetSobolevEnergy
  · intro α _
    simpa only [IntegrableOn, Measure.restrict_univ] using
      p.integrable_sq_cartesianDerivativeWithin_extend hf (fun i ↦ α (some i))
  · intro j _
    simpa only [iteratedFDerivWithin_univ, IntegrableOn, Measure.restrict_univ] using
      p.integrable_sq_norm_iteratedFDeriv_extend hf j

/-- The Fréchet input energy is bounded by the Cartesian input energy, with no
symmetry or integrability premise beyond closed-ball smoothness
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem frechetSobolevEnergy_ball_le_mul_cartesianSobolevEnergy
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    frechetSobolevEnergy (ball p.center p.radius) m f ≤
      frechetEnergyComparisonConstant n m *
        cartesianSobolevEnergy (ball p.center p.radius) m f :=
  frechetSobolevEnergy_le_mul_cartesianSobolevEnergy isOpen_ball m
    (hf.mono ball_subset_closedBall)
    (fun _ _ ↦ p.integrableOn_sq_cartesianDerivativeWithin_ball hf _)
    (fun _ _ ↦ p.integrableOn_sq_norm_iteratedFDerivWithin_ball hf _)

/-- The whole-space Fréchet energy of the actual Seeley extension is bounded
by its Cartesian energy. The constant is independent of the extension parameters
and the input (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem frechetSobolevEnergy_extend_le_mul_cartesianSobolevEnergy
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    frechetSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
      frechetEnergyComparisonConstant n m *
        cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) := by
  apply frechetSobolevEnergy_le_mul_cartesianSobolevEnergy isOpen_univ m
    (p.contDiff_extend Seeley.coeff Seeley.summable_abs_coeff_moment
      Seeley.infinite_moment hf).contDiffOn
  · intro α _
    simpa only [IntegrableOn, Measure.restrict_univ] using
      p.integrable_sq_cartesianDerivativeWithin_extend hf (fun i ↦ α (some i))
  · intro j _
    simpa only [iteratedFDerivWithin_univ, IntegrableOn, Measure.restrict_univ] using
      p.integrable_sq_norm_iteratedFDeriv_extend hf j

end Parameters

/-- The Cartesian and Fréchet energies in
`app:ch_regular_base:eq:ball-extension-sobolev` are equivalent, both on the open
ball and on the whole space for its actual fixed Seeley extension. The same two
positive constants work for every choice of extension parameters and smooth
input in dimension `n` and order `m`, including `n = 0` and `n = 1`. -/
theorem exists_pos_sobolevEnergy_comparison (n m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (p : Parameters (EuclideanSpace ℝ (Fin n)))
        (f : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
        (c * frechetSobolevEnergy (ball p.center p.radius) m f ≤
            cartesianSobolevEnergy (ball p.center p.radius) m f ∧
          cartesianSobolevEnergy (ball p.center p.radius) m f ≤
            C * frechetSobolevEnergy (ball p.center p.radius) m f) ∧
        (c * frechetSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
            cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) ∧
          cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
            C * frechetSobolevEnergy univ m (p.extend Seeley.coeff f)) := by
  refine ⟨(frechetEnergyComparisonConstant n m)⁻¹,
    cartesianEnergyComparisonConstant n m,
    inv_pos.mpr (frechetEnergyComparisonConstant_pos n m),
    cartesianEnergyComparisonConstant_pos n m, ?_⟩
  intro p f hf
  exact ⟨⟨(inv_mul_le_iff₀ (frechetEnergyComparisonConstant_pos n m)).mpr
      (p.frechetSobolevEnergy_ball_le_mul_cartesianSobolevEnergy hf m),
    p.cartesianSobolevEnergy_ball_le_mul_frechetSobolevEnergy hf m⟩,
    ⟨(inv_mul_le_iff₀ (frechetEnergyComparisonConstant_pos n m)).mpr
      (p.frechetSobolevEnergy_extend_le_mul_cartesianSobolevEnergy hf m),
    p.cartesianSobolevEnergy_extend_le_mul_frechetSobolevEnergy hf m⟩⟩

end JanetCartan.BallExtension
