module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.NormalBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.PolynomialBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.DetectorBounds

/-!
# Primitive one-high bounds for the actual geometric component

The detector estimate is instantiated for the same projected stress as the
normal reconstruction. Only immersion norms, metric/normal gaps and the
retained nullvector coefficient bounds remain as varying inputs.
Consumer: the `C₀` profiles in `Geometry` for `bg-adjoint` and `bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open LeadingWave AmbientResponse GeometricProfile ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Primitive component bounds with a fixed loss six. The detector range is
derived from the same primitive immersion budget, without a further stress
threshold. All chart containments and cutoffs precede the immersion (`bg-adjoint`). -/
theorem exists_physicalGeometryComponent_bounds {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) {ρ σ a : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (ha : 0 < a)
    (hx : MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hcρ : closedBall ((0 : Euclidean n), z) ρ ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (hσX : closedBall (0 : Euclidean n) σ ⊆ X)
    (hσV : closedBall (chartCenter (n := n) z).2 σ ⊆ V)
    (hσK : closedBall (0 : Euclidean n) σ ⊆ K)
    (hcoef : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B : Fin n → ℕ → ℝ, (∀ j m, 0 < B j m) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 6 F ≤ M →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ col : Fin n,
      (∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
        ContDiffAt ℝ ∞ (carrierNullvector T Q col) w) →
      (∀ m, cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierNullvector T Q col) ≤
        A m * (1 + cNorm K (m + 5) F)) →
      ∀ j m, cNorm (closedBall (chartCenter z) σ) m
        (physicalGeometryComponent T Q F col z ha j) ≤ B j m * (1 + cNorm K (m + 6) F) := by
  let L := closedBall (chartCenter (n := n) z) σ
  have hL : IsCompact L := isCompact_closedBall ..
  have hLXV : L ⊆ X ×ˢ V := by
    rw [show L = closedBall (chartCenter z) σ from rfl,
      ← closedBall_prod_same (chartCenter (n := n) z).1 (chartCenter (n := n) z).2 σ]
    exact Set.prod_mono hσX hσV
  have hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :=
    fun p hp ↦ hcρ (hcoef hp)
  obtain ⟨Bν, hBν, hbν⟩ := exists_geometricNormal_bounds T (N := N) hP hK hKU hball z hσ
    hX hV hXU hσX hσV hσK hc hcoef A hA hM hκmet hκ
  obtain ⟨Bq, hBq, hbq⟩ := exists_geometricDetector_bounds T (N := N) hP
    z hρ hx hcρ hL (hcoef.mono_left hLXV) hK hKU hball M hκmet hκ
  let Mq := Bq 0 * (1 + M)
  choose D hD hd using fun j ↦ exists_cNorm_geometricPolynomial_le (N := N)
    z ha hσ (Bν 0 * (1 + M)) Mq j
  let B := fun j m ↦ D j m * (1 + Bν m + Bq m)
  have hB j m : 0 < B j m := by
    have := hD j m
    have := hBν m
    have := hBq m
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal col hnull hnullB
  let ν := fun p : Euclidean n × CarrierParameter ↦ geometricNormal T Q F col (p.2, p.1)
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2))
  have hν : ContDiffOn ℝ ∞ ν (X ×ˢ V) :=
    geometricNormal_contDiffOn T Q hP hF hi hrank col hX hV hXU hc hcoef hnull
  have hq : ContDiffOn ℝ ∞ q (X ×ˢ V) :=
    (CanonicalCarrier.quadratic_canonical_smooth T hP Q).mono
      (fun p hp ↦ ⟨⟨hXU hp.1, (hc hp).1⟩, (hc hp).2⟩)
  have hνB := hbν Q F hQ hF hi hrank hFM hmet hnormal col hnull hnullB
  have hν0 : cNorm L 0 ν ≤ Bν 0 * (1 + M) :=
    (hνB 0).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hFM) (hBν 0).le)
  have hfour : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hqB := hbq Q F hQ hF hi hrank hfour hmet hnormal
  have hq0 : cNorm L 0 q ≤ Mq :=
    (hqB 0).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hfour) (hBq 0).le)
  intro j m
  have hh := hd j (X ×ˢ V) (hX.prod hV) hLXV ν q hν hq hν0 hq0 m
  change cNorm L m (physicalGeometryComponent T Q F col z ha j) ≤ _ at hh
  have hqh : cNorm L m q ≤ Bq m * (1 + cNorm K (m + 6) F) :=
    (hqB m).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (cNorm_mono_order (by omega))) (hBq m).le)
  apply hh.trans
  have hsum : 1 + cNorm L m ν + cNorm L m q ≤
      (1 + Bν m + Bq m) * (1 + cNorm K (m + 6) F) := by
    have hn := hνB m
    nlinarith [cNorm_nonneg K (m + 6) F]
  simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left hsum (hD j m).le

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
