module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RescaledDensity

/-!
# Original-domain square-root weights at both ODE labels

These identities insert the transported initial scalar into the existing
coefficient record. The label includes all original scalar coordinates;
there is no replacement of the ODE footpoint by the Hamilton transport.
Consumer: `NormalizedNormalLimit.FullAmplitude`, for
`app:ch_background:eq:bg-full-complex-amplitude` and `bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs.WideDensity

variable {n N : ℕ}

/-- The square-root initial multiplier contributes the two original density
factors, with all masks and both unweighted normal factors unchanged. This
form retains the full scalar-ODE label, including its carrier coordinates.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and `bg-Nsigma`.
Consumer: the frequency-uniform weighted shell bound. -/
theorem inputDensity_sqrtFootpoints
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (Y : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1) × Euclidean 3)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ) (p : InputVariables n)
    (hpos : ∀ side, 0 ≤ 1 + v (Y (densityEndpoint side p))) :
    inputDensity {a with normal := fun q ↦ Real.sqrt (1 + v (Y q)) • a.normal q} J p =
      densityPair v (fun side ↦ Y ∘ densityEndpoint side) p • inputDensity a J p := by
  have hl : 0 ≤ 1 + v (Y (p.1.1, p.2.1)) := hpos false
  have hr : 0 ≤ 1 + v (Y (p.1.2, p.2.1)) := hpos true
  ext i j
  simp only [inputDensity, inputWeight, Matrix.smul_apply, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Real.sq_sqrt hl, Real.sq_sqrt hr]
  simp only [densityPair, densityEndpoint, Bool.false_eq_true, ite_false, ite_true,
    Function.comp_apply]
  ring

/-- Smoothness of the literal density-weighted primitives follows from the
same original-domain footpoints and the original positive density interval.
The density need not be close to zero. Source:
`app:ch_background:prop:bg-frame`, Step 1; consumer: smooth zero extension in
the normalized full-amplitude comparison. -/
theorem primitiveRegularity_sqrtFootpoints
    {a : Coefficients n N} {J : InputVariables n → ℝ}
    {W : Set (InputVariables n)} (hreg : PrimitiveRegularity a J W)
    (Y : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1) × Euclidean 3)
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hY : ∀ side, ContDiffOn ℝ ∞ (Y ∘ densityEndpoint side) W)
    (hYL : ∀ side, MapsTo (Y ∘ densityEndpoint side) W L)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ∀ y ∈ L, ContDiffAt ℝ ∞ v y)
    (hpos : ∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) :
    PrimitiveRegularity
      {a with normal := fun q ↦ Real.sqrt (1 + v (Y q)) • a.normal q} J W := by
  have hsqrt (side : Bool) :
      ContDiffOn ℝ ∞ (fun p ↦ Real.sqrt (1 + v (Y (densityEndpoint side p)))) W := by
    intro p hp
    have hvY := (hv _ (hYL side hp)).comp_contDiffWithinAt p (hY side p hp)
    exact (contDiffWithinAt_const.add hvY).sqrt
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos _ (hYL side hp))))
  exact { hreg with
    leftNormal := (hsqrt false).smul hreg.leftNormal
    rightNormal := (hsqrt true).smul hreg.rightNormal }

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
