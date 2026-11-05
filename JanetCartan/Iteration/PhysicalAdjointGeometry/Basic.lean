module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Phase
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.LiteralIdentity.Gradient
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus

/-!
# The literal divided phase and its transverse trade directions

The consumer is `PhysicalMean.sampledAdjointMomentExpansion_realizes` in
`new:lem:mean-recurrence`. The displacement is the literal `δ = τ • η`.
All coefficient functions retain the entire physical variable, including
adapted time, and the carrier/displacement variables jointly. No homogeneous
phase is substituted and no extension is chosen separately for each frequency.

This leaf proves the algebraic and localization deductions. The actual
current-phase construction and its primitive uniform bounds are separate leaves.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.PhysicalAdjointGeometry

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m : ℕ}

/-- Full physical position, original carrier, and actual covector displacement.
The first component is never replaced by a frozen-time slice
(`new:lem:mean-recurrence`). -/
abbrev Point (X : Type) (m : ℕ) := X × (Euclidean m × Euclidean m)

/-- Fixed linear segment substitution in the literal divided phase
(`app:ch_seed:eq:seed-quotient-integral`). -/
def segment (t : ℝ) : Point X m →L[ℝ] X × Euclidean m :=
  let p := ContinuousLinearMap.snd ℝ X (Euclidean m × Euclidean m)
  (ContinuousLinearMap.fst ℝ X _).prod
    (((ContinuousLinearMap.fst ℝ _ _).comp p) +
      t • ((ContinuousLinearMap.snd ℝ _ _).comp p))

@[simp] theorem segment_apply (t : ℝ) (q : Point X m) :
    segment t q = (q.1, q.2.1 + t • q.2.2) := rfl

/-- Covector gradient extracted from the SAME joint phase differential.
This fixed extraction has norm at most one (`new:lem:mean-recurrence`). -/
def covectorGradient (S : X × Euclidean m → ℝ) (q : X × Euclidean m) :
    Euclidean m :=
  (InnerProductSpace.toDual ℝ (Euclidean m)).symm
    ((fderiv ℝ S q).comp (ContinuousLinearMap.inr ℝ X (Euclidean m)))

/-- Single jointly defined coefficient `Y` of the exact raw phase
`φ(x,η) = ⟪Y(x,ζ,τ η),η⟫` (`new:lem:mean-recurrence`). -/
def averagedCovector (S : X × Euclidean m → ℝ) (q : Point X m) : Euclidean m :=
  ∫ t in (0 : ℝ)..1, covectorGradient S (segment t q)

/-- Inject a transverse physical direction without moving the carrier or the
normalized displacement (`new:lem:mean-recurrence`). -/
def physicalInjection (W : Euclidean m →L[ℝ] X) : Euclidean m →L[ℝ] Point X m :=
  W.prod 0

@[simp] theorem physicalInjection_apply (W : Euclidean m →L[ℝ] X) (h : Euclidean m) :
    physicalInjection W h = (W h, 0) := rfl

/-- Actual transpose of the averaged transverse mixed derivative. Its
inverse, not its adjoint, is used below (`new:lem:mean-recurrence`). -/
def mixedTranspose (W : Euclidean m →L[ℝ] X) (Y : Point X m → Euclidean m)
    (q : Point X m) : Euclidean m →L[ℝ] Euclidean m :=
  (fderiv ℝ Y q).comp (physicalInjection W)

/-- Literal inverse-transpose derivative-trade direction before the common
joint localization (`new:lem:mean-recurrence`). -/
def tradeDirection (W : Euclidean m →L[ℝ] X) (Y : Point X m → Euclidean m)
    (q : Point X m) : Euclidean m →L[ℝ] X :=
  W.comp (Ring.inverse (mixedTranspose W Y q))

/-- Extracted covector gradient equals the original partial gradient wherever
that same phase is differentiable (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem covectorGradient_eq_gradient {S : X × Euclidean m → ℝ}
    {q : X × Euclidean m} (hS : DifferentiableAt ℝ S q) :
    covectorGradient S q = gradient (fun ξ ↦ S (q.1, ξ)) q.2 := by
  unfold covectorGradient gradient
  congr 1
  exact ((hS.hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv).symm

/-- The coefficient construction is smooth on every open set whose complete
closed segment remains in the original smooth phase domain. The compact
integral is differentiated jointly, including physical time
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem contDiffOn_averagedCovector [FiniteDimensional ℝ X] {S : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω) :
    ContDiffOn ℝ ∞ (averagedCovector S) V := by
  apply contDiffOn_fixedIntervalIntegral (a := 0) (b := 1)
    (F := fun w : ℝ × Point X m ↦ covectorGradient S (segment w.1 w.2)) hV
  intro z hz
  have hd := (hS.contDiffAt (hΩ.mem_nhds (hseg z.2 hz.2 z.1 (by simpa using hz.1)))).fderiv_right
    (m := ∞) (by simp)
  have hr : ContDiffAt ℝ ∞
      (fun q : X × Euclidean m ↦ (fderiv ℝ S q).comp
        (ContinuousLinearMap.inr ℝ X (Euclidean m))) (segment z.1 z.2) :=
    hd.clm_comp contDiffAt_const
  have hm : ContDiffAt ℝ ∞ (fun w : ℝ × Point X m ↦
      (w.2.1, w.2.2.1 + w.1 • w.2.2.2)) z := by fun_prop
  have hc := hr.comp z hm
  simpa only [Function.comp_def, segment_apply, covectorGradient] using
    (InnerProductSpace.toDual ℝ (Euclidean m)).symm.contDiff.contDiffAt.comp z hc

/-- The mixed coefficient is jointly smooth, not merely smooth for each
separately selected frequency (`new:lem:mean-recurrence`). -/
theorem contDiffOn_mixedTranspose {Y : Point X m → Euclidean m}
    {V : Set (Point X m)} (hV : IsOpen V) (hY : ContDiffOn ℝ ∞ Y V)
    (W : Euclidean m →L[ℝ] X) :
    ContDiffOn ℝ ∞ (mixedTranspose W Y) V := by
  exact (hY.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_comp contDiffOn_const

/-- Exact frozen-frequency trade identity for the literal coefficient `Y`.
The unit hypothesis is discharged by the actual current/frozen phase
comparison in the construction leaf; it is not a new final input
(`new:lem:mean-recurrence`). -/
theorem fderiv_phase_tradeDirection (W : Euclidean m →L[ℝ] X)
    {Y : Point X m → Euclidean m} {q : Point X m}
    (hY : DifferentiableAt ℝ Y q) (hu : IsUnit (mixedTranspose W Y q))
    (h η : Euclidean m) :
    fderiv ℝ (fun x ↦ inner ℝ (Y (x, q.2)) η) q.1
      (tradeDirection W Y q h) = inner ℝ h η := by
  have hd := hY.hasFDerivAt.comp q.1
    ((hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) q.2 q.1))
  have hi := hd.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) η q.1)
  dsimp only [Function.comp_def, id_eq] at hi
  rw [hi.fderiv]
  have hinv : mixedTranspose W Y q (Ring.inverse (mixedTranspose W Y q) h) = h := by
    have hh := congrArg (fun A : Euclidean m →L[ℝ] Euclidean m ↦ A h)
      (Ring.mul_inverse_cancel _ hu)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using hh
  simpa [tradeDirection, mixedTranspose, physicalInjection, ContinuousLinearMap.comp_apply]
    using congrArg (fun v ↦ inner ℝ v η) hinv

end JanetCartan.PhysicalAdjointGeometry
