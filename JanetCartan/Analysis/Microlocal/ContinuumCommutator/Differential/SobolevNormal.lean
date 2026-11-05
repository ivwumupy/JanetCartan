module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.PeriodicExtension
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.SmoothNormal

/-!
# The full matrix and exterior commutator on periodic Sobolev data

The final conditional deduction of `app:ch_background:eq:bg-commutator`.
The literal chart entries and fixed exterior multiplication give an actual
continuous real-linear commutator from H^(s-1) to L². The high amplitude budget
multiplies only the L² norm. The reserve `2 * (d + 1)` is independent of s.

The normal-reduction producer must identify its operator with
`matrixWithExteriorOperator` and supply joint smoothness, fixed two-position
support, and the primitive low/high amplitude bounds. This module assumes no
commutator estimate or inverse regularity. Its consumer is the continuum
elliptic bootstrap; it does not identify initial Lebesgue data with torus data.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential.DifferentialChart
open PeriodicSobolevSpace
open JanetCartan.ContinuumCommutator
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "L²" => PeriodicL2 d ℂ
local notation "Rows" => PiLp 2 (fun _ : I ↦ L²)

section Construction
variable (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (M : ℝ)
  (b : I → I → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
  (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
  (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
  (is : List (Fin d)) (hpos : 0 < is.length)
  (hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
  (q : Torus d → ℝ) (hq : IsSmoothPeriodic q)

/-- The actual finite sum of completed scalar chart commutators and the
surviving exterior Leibniz terms (`app:ch_background:eq:bg-commutator`). -/
def matrixWithExteriorSobolevCommutator :
    PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ (is.length - 1)) →L[ℝ] Rows :=
  (∑ i : I, ∑ j : I, ((coordinateInjection (H := L²) i).toContinuousLinearMap.restrictScalars ℝ).comp
    ((torusSobolevCommutator hd r hr (is.length - 1) M (b i j) (hb i j) (hs i j)
      H (hM i j) is (by omega) (hH i j)).comp
      (PiLp.proj 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ (is.length - 1)) j))) +
  ∑ i : I, ((coordinateInjection (H := L²) i).toContinuousLinearMap.restrictScalars ℝ).comp
    ((Exterior.commutator (F := ℂ) q hq is).comp
      (PiLp.proj 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ (is.length - 1)) i))

/-- Row formula for the constructed all-data commutator
(`app:ch_background:eq:bg-commutator`). -/
theorem matrixWithExteriorSobolevCommutator_apply
    (u : PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ (is.length - 1))) (i : I) :
    matrixWithExteriorSobolevCommutator hd r hr M b hb hs H hM is hpos hH q hq u i =
      (∑ j, torusSobolevCommutator hd r hr (is.length - 1) M (b i j) (hb i j)
        (hs i j) H (hM i j) is (by omega) (hH i j) (u j)) +
      Exterior.commutator q hq is (u i) := by
  classical
  simp [matrixWithExteriorSobolevCommutator, coordinateInjection, Pi.single_apply]

end Construction

/-- The additive one-high estimate for the full finite matrix and fixed exterior
normal on every Hⁿ input. The constant is selected before b, H, the derivative
word, and the datum (`app:ch_background:eq:bg-commutator`). -/
theorem exists_matrixWithExterior_sobolev_commutator_bound
    (I : Type*) [Fintype I] (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2)
    (n : ℕ) (M : ℝ) (q : Torus d → ℝ) (hq : IsSmoothPeriodic q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : I → I → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
        (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (hlen : is.length = n + 1)
        (hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
        (u : PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ (is.length - 1))),
        ‖matrixWithExteriorSobolevCommutator hd r hr M b hb hs H hM is
          (by omega) hH q hq u‖ ≤
        C * (‖u‖ + max 1 H * ‖WithLp.toLp 2 (fun i ↦ toL2 (is.length - 1) (u i))‖) := by
  classical
  let C := (exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose
  have hC : 0 ≤ C :=
    (exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose_spec.1
  let Q := Exterior.commutatorConstant (F := ℂ) q hq (n + 1)
  have hQ : 0 ≤ Q := (Exterior.commutatorConstant_pos q hq (n + 1)).le
  refine ⟨(Fintype.card I : ℝ) * (Fintype.card I : ℝ) * C +
    (Fintype.card I : ℝ) * Q, by positivity, ?_⟩
  intro b hb hs H hM is hlen hH u
  let f : PiLp 2 (fun _ : I ↦ PeriodicL2 d ℂ) := WithLp.toLp 2 (fun i ↦ toL2 (is.length - 1) (u i))
  let A := ‖u‖ + max 1 H * ‖f‖
  let v := fun i j ↦ torusSobolevCommutator hd r hr (is.length - 1) M (b i j)
    (hb i j) (hs i j) H (hM i j) is (by omega) (hH i j) (u j)
  let e := fun i ↦ Exterior.commutator q hq is (u i)
  have hv (i j : I) : ‖v i j‖ ≤ C * A := by
    have hn : is.length - 1 = n := by omega
    have h := norm_torusSobolevCommutator_le hd r hr (is.length - 1) M (b i j)
      (hb i j) (hs i j) H (hM i j) is (by omega) (hH i j) (u j)
    have hc : (exists_torusL2Operator_sobolev_commutator_bound hd r hr (is.length - 1) M).choose = C := by
      rw [hn]
    rw [hc] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact add_le_add (PiLp.norm_apply_le u j)
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f j) (by positivity))
  have he (i : I) : ‖e i‖ ≤ Q * ‖u‖ := by
    have h := Exterior.norm_commutator_le q hq is (u i)
    have hc : Exterior.commutatorConstant (F := ℂ) q hq is.length = Q := by
      rw [hlen]
    rw [hc] at h
    exact h.trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) hQ)
  have heq : matrixWithExteriorSobolevCommutator hd r hr M b hb hs H hM is
      (by omega) hH q hq u =
      (∑ i, ∑ j, coordinateInjection (H := L²) i (v i j)) + ∑ i, coordinateInjection (H := L²) i (e i) := by
    simp only [matrixWithExteriorSobolevCommutator, add_apply,
      sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      LinearIsometry.coe_toContinuousLinearMap, PiLp.proj_apply, v, e]
  rw [heq]
  have hvn : ‖∑ i, ∑ j, coordinateInjection (H := L²) i (v i j)‖ ≤
      (Fintype.card I : ℝ) * (Fintype.card I : ℝ) * C * A := by
    calc
      _ ≤ ∑ i, ∑ j, ‖v i j‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ ↦ (coordinateInjection (H := L²) i).norm_map _ |>.le))
      _ ≤ ∑ _i : I, ∑ _j : I, C * A :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hv i j
      _ = _ := by simp [mul_assoc]
  have hen : ‖∑ i, coordinateInjection (H := L²) i (e i)‖ ≤ (Fintype.card I : ℝ) * Q * ‖u‖ := by
    calc
      _ ≤ ∑ i, ‖e i‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ (coordinateInjection (H := L²) i).norm_map _ |>.le)
      _ ≤ ∑ _i : I, Q * ‖u‖ := Finset.sum_le_sum fun i _ ↦ he i
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ‖∑ i, ∑ j, coordinateInjection (H := L²) i (v i j)‖ + ‖∑ i, coordinateInjection (H := L²) i (e i)‖ :=
      norm_add_le _ _
    _ ≤ (Fintype.card I : ℝ) * (Fintype.card I : ℝ) * C * A +
        (Fintype.card I : ℝ) * Q * ‖u‖ := add_le_add hvn hen
    _ ≤ _ := by
      change _ ≤ (_ + _) * A
      have hnon : 0 ≤ (Fintype.card I : ℝ) * Q * (max 1 H * ‖f‖) := by positivity
      dsimp only [A]
      nlinarith

section Distribution
variable (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (M : ℝ)
  (b : I → I → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
  (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
  (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
  (q : Torus d → ℝ) (hq : IsSmoothPeriodic q)

/-- The full distributional identity on every periodic H^(s-1) datum, row by
row. The PDO action on the top derivative is the independent first-order
kernel-transfer extension. The exterior action is the literal transposed
multiplication/derivative pairing (`app:ch_background:eq:bg-commutator`). -/
theorem matrixWithExteriorSobolevCommutator_distribution
    (a : Fin d) (js : List (Fin d))
    (hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + (a :: js).length) H)
    (u : PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace d ℂ ((a :: js).length - 1)))
    (i : I) (φ : Torus d → ℂ) (hφ : IsSmoothPeriodic φ) :
    let f : Rows := WithLp.toLp 2 (fun j ↦ toL2 ((a :: js).length - 1) (u j))
    let T := matrixWithExteriorOperator (matrixOperator (fun i j ↦
      torusL2Operator hd r (b i j) (hb i j) (hs i j) M
        (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))) q hq.1
    (-1 : ℝ) ^ (a :: js).length *
        (∫ x, ⟪T f i x, periodicCoordinateDerivList (a :: js).reverse φ x⟫) -
      ((∑ j, torusOnOrderedDerivative hd r (b i j) (hb i j) (hs i j) M (hM i j)
          ((a :: js).length - 1) a js (by simp) (u j) (ofSmooth 1 φ hφ)) +
        (-1 : ℝ) ^ (a :: js).length *
          (∫ x, ⟪f i x, periodicCoordinateDerivList (a :: js).reverse
            (fun y ↦ q y • φ y) x⟫)) =
      ∫ x, ⟪matrixWithExteriorSobolevCommutator hd r hr M b hb hs H hM (a :: js)
        (by simp) hH q hq u i x, φ x⟫ := by
  classical
  dsimp only
  let f : Rows := WithLp.toLp 2 (fun j ↦ toL2 ((a :: js).length - 1) (u j))
  let T := fun i j ↦ torusL2Operator hd r (b i j) (hb i j) (hs i j) M
    (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _))
  let v := fun j ↦ torusSobolevCommutator hd r hr ((a :: js).length - 1) M (b i j)
    (hb i j) (hs i j) H (hM i j) (a :: js) (by simp) (hH i j) (u j)
  let Q := fun j ↦ torusOnOrderedDerivative hd r (b i j) (hb i j) (hs i j) M (hM i j)
    ((a :: js).length - 1) a js (by simp) (u j) (ofSmooth 1 φ hφ)
  let Dφ := toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (a :: js).reverse φ)
    (hφ.coordinateDerivList _))
  let φ₀ := toL2 0 (ofSmooth 0 φ hφ)
  have hv (j : I) : (-1 : ℝ) ^ (a :: js).length * ⟪T i j (f j), Dφ⟫ - Q j =
      ⟪v j, φ₀⟫ := by
    simpa only [T, f, PiLp.toLp_apply, Dφ, Q, v, φ₀, inner_periodicL2_ofSmooth] using
      torusSobolevCommutator_distribution hd r (b i j) (hb i j) (hs i j) M (hM i j)
        hr ((a :: js).length - 1) H a js (by simp) (hH i j) (u j) φ hφ
  have hm : (-1 : ℝ) ^ (a :: js).length * ⟪∑ j, T i j (f j), Dφ⟫ -
      (∑ j, Q j) = ⟪∑ j, v j, φ₀⟫ := by
    simp only [sum_inner, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ hv j)
  have he := Exterior.commutator_inner q hq (a :: js) (u i) φ hφ
  have goal :
      (-1 : ℝ) ^ (a :: js).length *
        ⟪matrixWithExteriorOperator (matrixOperator T) q hq.1 f i, Dφ⟫ -
      ((∑ j, Q j) + (-1 : ℝ) ^ (a :: js).length *
        ⟪f i, toL2 0 (ofSmooth 0
          (periodicCoordinateDerivList (a :: js).reverse (fun y ↦ q y • φ y))
          ((Exterior.smooth_smul hq hφ).coordinateDerivList _))⟫) =
      ⟪matrixWithExteriorSobolevCommutator hd r hr M b hb hs H hM (a :: js)
        (by simp) hH q hq u i, φ₀⟫ := by
    rw [matrixWithExteriorOperator_apply, matrixOperator_apply,
      matrixWithExteriorSobolevCommutator_apply, inner_add_left, inner_add_left]
    change _ = ⟪∑ j, v j, φ₀⟫ + ⟪Exterior.commutator q hq (a :: js) (u i), φ₀⟫
    dsimp only [f, PiLp.toLp_apply, Dφ, φ₀] at hm ⊢
    linarith
  simpa only [f, T, Q, Dφ, φ₀, inner_periodicL2_ofSmooth] using goal

end Distribution
end JanetCartan.Pseudodifferential.DifferentialChart
