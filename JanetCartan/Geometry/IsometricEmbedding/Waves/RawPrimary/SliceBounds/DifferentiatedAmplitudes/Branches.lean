module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.GradedAtoms

/-!
# Exact physical differentiation branches

For `app:ch_waves:eq:individual-raw-slice`, each physical differentiation
either hits the oscillation or the remaining amplitude. The resulting finite
binary tree keeps the number of phase factors, before any triangle inequality.
The consumer is the differentiated slice construction. Physical directions
are arbitrary, so mixed derivatives and time derivatives are included.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.SliceBounds

/-- Choices of where the physical derivatives land in
`app:ch_waves:eq:individual-raw-slice`. `true` creates a phase factor. -/
def SliceDerivativeBranch : ℕ → Type
  | 0 => Unit
  | s + 1 => Bool × SliceDerivativeBranch s

instance (s : ℕ) : Fintype (SliceDerivativeBranch s) := by
  induction s with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ s ih => exact inferInstanceAs (Fintype (Bool × SliceDerivativeBranch s))

instance : Unique (SliceDerivativeBranch 0) := inferInstanceAs (Unique Unit)

/-- The exact phase-factor count in the proof of
`app:ch_waves:eq:individual-raw-slice`. -/
def SliceDerivativeBranch.phaseCount : {s : ℕ} → SliceDerivativeBranch s → ℕ
  | 0, _ => 0
  | _ + 1, (b, t) => b.toNat + t.phaseCount

/-- No order-`s` term has more than `s` phase factors
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem SliceDerivativeBranch.phaseCount_le {s : ℕ} (b : SliceDerivativeBranch s) :
    b.phaseCount ≤ s := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    rcases b with ⟨b, t⟩
    cases b <;> simp only [phaseCount, Bool.toNat_false, Bool.toNat_true] <;>
      have := ih t <;> omega

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The frequency-free amplitude of one differentiation branch. Its phase
is unchanged and its omitted prefactor is exactly `κ^phaseCount`
(`app:ch_waves:eq:individual-raw-slice`). -/
def sliceDerivativeAmplitude (φ : E → ℝ) (A : E → F) :
    {s : ℕ} → (Fin s → E) → SliceDerivativeBranch s → E → F
  | 0, _, _ => A
  | _ + 1, v, (b, t) =>
      if b then fun x ↦ (Complex.I * (fderiv ℝ φ x (v 0) : ℂ)) •
        sliceDerivativeAmplitude φ A (Fin.tail v) t x
      else fun x ↦ fderiv ℝ (sliceDerivativeAmplitude φ A (Fin.tail v) t) x (v 0)

/-- Every branch is smooth on the same original open chart. No differentiated
amplitude regularity is an input (`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiffOn_sliceDerivativeAmplitude {U : Set E} (hU : IsOpen U)
    {φ : E → ℝ} {A : E → F} (hφ : ContDiffOn ℝ ∞ φ U)
    (hA : ContDiffOn ℝ ∞ A U) {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) :
    ContDiffOn ℝ ∞ (sliceDerivativeAmplitude φ A v b) U := by
  induction s with
  | zero => exact hA
  | succ s ih =>
    rcases b with ⟨b, t⟩
    have ht := ih (Fin.tail v) t
    cases b
    · exact (ht.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
    · exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((hφ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
          contDiffOn_const))).smul ht

/-- Differentiation and multiplication by phase jets do not enlarge the
closed amplitude support (`app:ch_waves:eq:individual-raw-slice`). -/
theorem tsupport_sliceDerivativeAmplitude_subset (φ : E → ℝ) (A : E → F)
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) :
    tsupport (sliceDerivativeAmplitude φ A v b) ⊆ tsupport A := by
  induction s with
  | zero => exact Subset.rfl
  | succ s ih =>
    rcases b with ⟨b, t⟩
    cases b
    · exact (tsupport_fderiv_apply_subset ℝ (v 0)).trans (ih (Fin.tail v) t)
    · exact (tsupport_smul_subset_right _ _).trans (ih (Fin.tail v) t)

private theorem fderiv_oscillation_smul {φ : E → ℝ} {A : E → F} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hA : DifferentiableAt ℝ A x) (κ : ℝ) (v : E) :
    fderiv ℝ (fun y ↦ Complex.exp (Complex.I * (κ * φ y : ℝ)) • A y) x v =
      Complex.exp (Complex.I * (κ * φ x : ℝ)) •
        (fderiv ℝ A x v + (κ : ℂ) • ((Complex.I * (fderiv ℝ φ x v : ℂ)) • A x)) := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp x
    (hφ.hasFDerivAt.const_mul κ)).const_mul Complex.I).cexp
  have hh := h.fun_smul hA.hasFDerivAt
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hh
  rw [hh.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, smul_add, smul_smul]
  congr 1
  congr 1
  push_cast
  ring

/-- Exact all-order physical derivative identity, retaining each term's
`κ^q`. The same oscillation is factored from every branch, including mixed
physical derivatives (`app:ch_waves:eq:individual-raw-slice`). -/
theorem iteratedFDeriv_oscillation_smul_eq_branches {U : Set E} (hU : IsOpen U)
    {φ : E → ℝ} {A : E → F} (hφ : ContDiffOn ℝ ∞ φ U)
    (hA : ContDiffOn ℝ ∞ A U) (κ : ℝ) (s : ℕ) {x : E} (hx : x ∈ U)
    (v : Fin s → E) :
    iteratedFDeriv ℝ s (fun y ↦ Complex.exp (Complex.I * (κ * φ y : ℝ)) • A y) x v =
      Complex.exp (Complex.I * (κ * φ x : ℝ)) •
        ∑ b : SliceDerivativeBranch s,
          (κ : ℂ) ^ b.phaseCount • sliceDerivativeAmplitude φ A v b x := by
  have he : ContDiffOn ℝ ∞
      (fun y ↦ Complex.exp (Complex.I * (κ * φ y : ℝ)) • A y) U :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul hφ))).cexp.smul hA
  induction s generalizing x with
  | zero => simp only [iteratedFDeriv_zero_apply, Fintype.sum_unique,
      SliceDerivativeBranch.phaseCount, sliceDerivativeAmplitude, pow_zero, one_smul]
  | succ s ih =>
    have hb (b : SliceDerivativeBranch s) :
        ContDiffOn ℝ ∞ (sliceDerivativeAmplitude φ A (Fin.tail v) b) U :=
      contDiffOn_sliceDerivativeAmplitude hU hφ hA _ b
    have hsum : ContDiffOn ℝ ∞ (fun y ↦ ∑ b : SliceDerivativeBranch s,
        (κ : ℂ) ^ b.phaseCount • sliceDerivativeAmplitude φ A (Fin.tail v) b y) U :=
      ContDiffOn.sum fun b _ ↦ (hb b).const_smul _
    rw [((he.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (show (s : ℕ∞ω) < ∞ from by exact_mod_cast (ENat.natCast_lt_top s))).iteratedFDeriv_succ_apply_left']
    have heq : (fun y ↦ iteratedFDeriv ℝ s
        (fun z ↦ Complex.exp (Complex.I * (κ * φ z : ℝ)) • A z) y (Fin.tail v)) =ᶠ[𝓝 x]
        (fun y ↦ Complex.exp (Complex.I * (κ * φ y : ℝ)) •
          ∑ b : SliceDerivativeBranch s,
            (κ : ℂ) ^ b.phaseCount • sliceDerivativeAmplitude φ A (Fin.tail v) b y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy (Fin.tail v)
    rw [heq.fderiv_eq, fderiv_oscillation_smul
      ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ((hsum.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    rw [fderiv_fun_sum (A := fun b y ↦
      (κ : ℂ) ^ b.phaseCount • sliceDerivativeAmplitude φ A (Fin.tail v) b y)
      (fun b _ ↦ ((hb b).contDiffAt (hU.mem_nhds hx)).differentiableAt
        (by simp) |>.const_smul _)]
    simp only [sum_apply, fderiv_fun_const_smul
      (((hb _).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)),
      smul_apply]
    change _ = _ • ∑ b : Bool × SliceDerivativeBranch s, _
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, SliceDerivativeBranch.phaseCount,
      Bool.toNat_true, Bool.toNat_false, sliceDerivativeAmplitude,
      Bool.false_eq_true, ↓reduceIte, Finset.smul_sum, smul_smul, pow_add, pow_one, pow_zero, one_mul]
    congr 1
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ring

end JanetCartan.RawPrimary.SliceBounds
