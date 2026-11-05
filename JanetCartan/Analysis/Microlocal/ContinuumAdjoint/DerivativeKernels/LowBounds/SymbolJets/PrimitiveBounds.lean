module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.Integration
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Jets

/-!
# Finite weighted primitive reserve for the modified normal

The consumer is `graphNormalAmplitudeBounds_of_densityJets`, for the half-order
amplitudes in `app:ch_background:prop:bg-adjoint`. The frequency scale is frozen
at the point of differentiation. Thus the amplitude assumptions below concern
only fixed linear dilations of the original amplitude, never its composition
with a nonlinear inverse chart.

The geometry producer supplies jets of the inverse and the original Jacobian
through `N = 2 * (n + 1)`. If the latter is obtained by differentiating the
forward map, this requires forward derivatives through `N + 1`. The equality
with that derivative is retained explicitly. Neither reciprocal Jacobian jets
nor density jets are primitive assumptions.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow

variable {n : ℕ}

/-- Original amplitude variables for `app:ch_background:prop:bg-adjoint`. -/
abbrev AmplitudeVariables (n : ℕ) :=
  CarrierParameter × (Euclidean n × Euclidean (n - 1))

/-- A fixed frequency dilation of the original half-order amplitude; its
mixed jets encode the frequency derivative weights in
`app:ch_background:prop:bg-adjoint`. -/
def scaledOriginalAmplitude (a : AdjointAmplitude n) (r : ℝ)
    (q : AmplitudeVariables n) : ℂ := a q.1 q.2.1 (r • q.2.2)

/-- The same fixed dilation of a regularizer, for uniformity in the cutoff
parameter in `app:ch_background:prop:bg-adjoint`. -/
def scaledOriginalRegularizer (m : CarrierVariable n → ℝ) (r : ℝ)
    (u : CarrierVariable n) : ℝ := m (u.1, r • u.2)

/-- The original left amplitude arguments, before inverse substitution
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def Chart.leftArguments (g : Chart n) (q : JointVariables n) : AmplitudeVariables n :=
  ((g.carrier q).1, q.1.1, (g.carrier q).2)

/-- The original right amplitude arguments, before inverse substitution
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def Chart.rightArguments (g : Chart n) (q : JointVariables n) : AmplitudeVariables n :=
  ((g.carrier q).1, q.1.2.1, (g.carrier q).2)

/-- Linear rescalings of input coordinates and Jacobian columns, for the
degree-one conic Jacobian in `app:ch_background:eq:bg-Psi`. The column map has
determinant `1/r`, so the determinant of the normalized Jacobian is exactly
the original determinant divided by `r`. These data contain no amplitude. -/
structure JetRescaling (g : Chart n) where
  input : ℝ → JointVariables n ≃L[ℝ] JointVariables n
  columns : ℝ → Euclidean n →L[ℝ] Euclidean n
  columns_det : ∀ r, 0 < r → (columns r).det = r⁻¹
  carrier : ∀ r, 0 < r → ∀ q,
    g.carrier (input r q) = ((g.carrier q).1, r • (g.carrier q).2)
  left_position : ∀ r, 0 < r → ∀ q, (input r q).1.1 = q.1.1
  right_position : ∀ r, 0 < r → ∀ q, (input r q).1.2.1 = q.1.2.1

/-- The original Jacobian in linearly rescaled input coordinates, with
linearly rescaled columns. No inverse chart occurs here
(`app:ch_background:eq:bg-Psi`). -/
def JetRescaling.normalizedJacobian {g : Chart n} (s : JetRescaling g) (r : ℝ)
    (q : JointVariables n) : Euclidean n →L[ℝ] Euclidean n :=
  let w := s.input r q
  (g.jacobian w.1.1 w.1.2.1 w.2 w.1.2.2).comp (s.columns r)

/-- The inverse chart with its input frequency divided by a fixed scale
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def JetRescaling.normalizedPull {g : Chart n} (s : JetRescaling g) (r : ℝ)
    (p : JointVariables n) : JointVariables n := (s.input r).symm (g.pull p)

/-- Primitive weighted geometry through the finite order consumed by
`graphNormalAmplitudeBounds_of_densityJets`. Bounds are needed on the closed
image buffer, including its boundary. The high-frequency threshold is positive
and is imposed there, rather than on points where the extended density vanishes.
The direct original-Jacobian bound of order `N` requires forward order `N+1`
when it is produced from `jacobian_is_fderiv`. -/
structure PrimitiveJetGeometry (g : Chart n) (s : JetRescaling g)
    (N : ℕ) (ρ B c : ℝ) (L : Set (JointVariables n)) (K : Set (Euclidean 2)) : Prop where
  threshold_pos : 0 < ρ
  budget_nonneg : 0 ≤ B
  gap_pos : 0 < c
  input_open : IsOpen g.inputDomain
  jacobian_is_fderiv : ∀ q ∈ g.inputDomain,
    g.jacobian q.1.1 q.1.2.1 q.2 q.1.2.2 =
      fderiv ℝ (g.forward q.1.1 q.1.2.1 q.2) q.1.2.2
  determinant_gap : ∀ q ∈ g.inputDomain,
    c * ‖(g.carrier q).2‖ ≤ |(g.jacobian q.1.1 q.1.2.1 q.2 q.1.2.2).det|
  high_frequency : ∀ p ∈ g.push '' L, p.2 ∈ K → ρ ≤ ‖(g.carrier (g.pull p)).2‖
  inverse_jets : ∀ p ∈ g.push '' L, p.2 ∈ K →
    let r := ‖(g.carrier (g.pull p)).2‖
    ∀ j, 1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j (s.normalizedPull r) p‖ ≤ B
  jacobian_jets : ∀ p ∈ g.push '' L, p.2 ∈ K →
    let r := ‖(g.carrier (g.pull p)).2‖
    ∀ j ≤ N, ‖iteratedFDeriv ℝ j (s.normalizedJacobian r) (s.normalizedPull r p)‖ ≤ B
  carrier_jets : ∀ p ∈ g.push '' L, p.2 ∈ K →
    let r := ‖(g.carrier (g.pull p)).2‖
    ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j g.carrier (s.normalizedPull r p)‖ ≤ B
  left_jets : ∀ p ∈ g.push '' L, p.2 ∈ K →
    let r := ‖(g.carrier (g.pull p)).2‖
    ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j g.leftArguments (s.normalizedPull r p)‖ ≤ B
  right_jets : ∀ p ∈ g.push '' L, p.2 ∈ K →
    let r := ‖(g.carrier (g.pull p)).2‖
    ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j g.rightArguments (s.normalizedPull r p)‖ ≤ B

/-- Compact primitive supports and the finite order-one-half reserve in the
original carrier, measurement and frequency variables. Testing all mixed jets
of `a(z,x,rη)` on the unit sphere expresses the usual loss of one power of
frequency per frequency derivative. The intended finite order is
`N = 2 * (n + 1)` (`app:ch_background:prop:bg-adjoint`). -/
structure PrimitiveAmplitudeReserve (g : Chart n) (N : ℕ) (ρ A : ℝ)
    (X : Set (Euclidean n)) (K : Set (Euclidean 2))
    (Z : Set CarrierParameter) (Ω : Set (Euclidean (n - 1)))
    (L : Set (JointVariables n)) (a : AdjointAmplitude n) : Prop where
  budget_nonneg : 0 ≤ A
  compact_supports : CompactSupports a X K
  carrier_compact : IsCompact Z
  angular_compact : IsCompact Ω
  angular_unit : Ω ⊆ {η | ‖η‖ = 1}
  amplitude_support : ∀ z x η, a z x η ≠ 0 →
    z ∈ Z ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖
  buffered : BufferedSupport g a L
  mixed_jets : ∀ r, ρ ≤ r → ∀ q : AmplitudeVariables n, ‖q.2.2‖ = 1 →
    ∀ j ≤ N, ‖iteratedFDeriv ℝ j (scaledOriginalAmplitude a r) q‖ ≤ A * Real.sqrt r

/-- Uniform scaled mixed derivative bounds on the original smooth regularizer.
The budget is fixed before the choice of regularizer, including its cutoff
parameter (`app:ch_background:prop:bg-adjoint`). -/
structure PrimitiveRegularizerReserve (N : ℕ) (ρ M : ℝ)
    (m : CarrierVariable n → ℝ) : Prop where
  budget_nonneg : 0 ≤ M
  mixed_jets : ∀ r, ρ ≤ r → ∀ u : CarrierVariable n, ‖u.2‖ = 1 →
    ∀ j ≤ N, ‖iteratedFDeriv ℝ j (scaledOriginalRegularizer m r) u‖ ≤ M

/-- Exact degree-one determinant normalization, used to recover the factor
`1/r` after the reciprocal determinant estimate
(`app:ch_background:eq:bg-Psi`). -/
theorem JetRescaling.normalizedJacobian_det {g : Chart n} (s : JetRescaling g)
    {r : ℝ} (hr : 0 < r) (q : JointVariables n) :
    (s.normalizedJacobian r q).det =
      (g.jacobian (s.input r q).1.1 (s.input r q).1.2.1
        (s.input r q).2 (s.input r q).1.2.2).det * r⁻¹ := by
  change LinearMap.det (_ ∘ₗ _) = _
  rw [LinearMap.det_comp]
  exact congrArg _ (s.columns_det r hr)

/-- The original carrier after inverse substitution is recovered by the
fixed dilation, with no derivative of the pointwise scale
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem JetRescaling.carrier_normalizedPull {g : Chart n} (s : JetRescaling g)
    {r : ℝ} (hr : 0 < r) (p : JointVariables n) :
    g.carrier (g.pull p) =
      ((g.carrier (s.normalizedPull r p)).1, r • (g.carrier (s.normalizedPull r p)).2) := by
  simpa [normalizedPull] using s.carrier r hr ((s.input r).symm (g.pull p))

/-- The normalized input frequency is on the unit sphere at the base point
(`app:ch_background:prop:bg-adjoint`). -/
theorem JetRescaling.norm_carrier_normalizedPull {g : Chart n} (s : JetRescaling g)
    (p : JointVariables n) (hr : 0 < ‖(g.carrier (g.pull p)).2‖) :
    ‖(g.carrier (s.normalizedPull ‖(g.carrier (g.pull p)).2‖ p)).2‖ = 1 := by
  have he := congrArg (fun u : CarrierVariable n ↦ ‖u.2‖)
    (s.carrier_normalizedPull hr p)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at he
  nlinarith

/-- Exact recovery of the left original amplitude from a fixed dilation
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem JetRescaling.scaledOriginalAmplitude_left {g : Chart n} (s : JetRescaling g)
    (a : AdjointAmplitude n) {r : ℝ} (hr : 0 < r) (p : JointVariables n) :
    scaledOriginalAmplitude a r (g.leftArguments (s.normalizedPull r p)) =
      a (g.carrier (g.pull p)).1 p.1.1 (g.carrier (g.pull p)).2 := by
  have hx := s.left_position r hr (s.normalizedPull r p)
  simp only [normalizedPull, ContinuousLinearEquiv.apply_symm_apply, Chart.pull] at hx
  change p.1.1 = (s.normalizedPull r p).1.1 at hx
  rw [s.carrier_normalizedPull hr p]
  simp only [scaledOriginalAmplitude, Chart.leftArguments]
  rw [← hx]

/-- Exact recovery of the right original amplitude from a fixed dilation
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem JetRescaling.scaledOriginalAmplitude_right {g : Chart n} (s : JetRescaling g)
    (a : AdjointAmplitude n) {r : ℝ} (hr : 0 < r) (p : JointVariables n) :
    scaledOriginalAmplitude a r (g.rightArguments (s.normalizedPull r p)) =
      a (g.carrier (g.pull p)).1 p.1.2.1 (g.carrier (g.pull p)).2 := by
  have hx := s.right_position r hr (s.normalizedPull r p)
  simp only [normalizedPull, ContinuousLinearEquiv.apply_symm_apply, Chart.pull] at hx
  change p.1.2.1 = (s.normalizedPull r p).1.2.1 at hx
  rw [s.carrier_normalizedPull hr p]
  simp only [scaledOriginalAmplitude, Chart.rightArguments]
  rw [← hx]

/-- Exact recovery of the original regularizer from a fixed dilation
(`app:ch_background:prop:bg-adjoint`). -/
theorem JetRescaling.scaledOriginalRegularizer_carrier {g : Chart n} (s : JetRescaling g)
    (m : CarrierVariable n → ℝ) {r : ℝ} (hr : 0 < r) (p : JointVariables n) :
    scaledOriginalRegularizer m r (g.carrier (s.normalizedPull r p)) =
      m (g.carrier (g.pull p)) := by
  rw [s.carrier_normalizedPull hr p]
  rfl

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
