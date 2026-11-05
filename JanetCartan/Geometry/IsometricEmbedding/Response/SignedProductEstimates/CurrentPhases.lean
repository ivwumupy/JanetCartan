module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedPhases
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedSignedGeometry

/-!
# Literal constructed carriers in normalized signed-phase estimates

`ConstructedSignedGeometry` publishes the covectors `currentGroup` for one
fixed family of Hamilton charts and radial labels. Their gradients are
identified here with the corresponding scalar phases, on the original full
parameter cubes. The same pair witness then supplies the normalized source
phase's derivative band and angular set in `app:ch_pairs:setup:pairs-lag`.
No carrier family, frame, radial label or sample witness is reselected.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.SignedProductEstimates
open ActualCarriers CurrentFullPhase FrozenMenu ConstructedSignedGeometry InnerProductSpace

/-- Smoothness of the selected Hamilton carrier supplies its physical
slice derivative on the original full parameter cube
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
private theorem differentiableAt_constructed_carrier
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (Q : _) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) T.physicalRadius) (hz : z ∈ parameterCube P.radius) :
    DifferentiableAt ℝ (fun y ↦ T.carrier Q y z) x := by
  have hz' := parameterCube_subset_doubledInterior hP.1 hz
  have hj : ContDiffAt ℝ ∞ (fun p : Euclidean n × Euclidean 3 ↦ T.carrier Q p.1 p.2) (x, z) :=
    (T.carrier_smooth hP Q).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds ⟨hx, hz'⟩)
  have hpair : ContDiffAt ℝ ∞ (fun y : Euclidean n ↦ (y, z)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  have hslice : ContDiffAt ℝ ∞ (fun y ↦ T.carrier Q y z) x :=
    hj.comp (g := fun p : Euclidean n × Euclidean 3 ↦ T.carrier Q p.1 p.2)
      (f := fun y : Euclidean n ↦ (y, z)) x hpair
  exact hslice.differentiableAt (by simp)

/-- The original signed geometry's group covector is the gradient of the
SAME radially labelled constructed carrier (`app:ch_seed:prop:seed-actual-menu`,
Step 2). Differentiability is derived from the selected chart's smoothness;
there is no new phase, frame or radial-label choice. -/
theorem currentGroup_eq_gradient_radial_carrier
    {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {G : Type*} (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
    (g : G) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) (T (assign g)).physicalRadius)
    (hz : z ∈ groupCube D assign g) :
    currentGroup T assign R Q hQ hlow x g z =
      gradient (fun y ↦ R g * (T (assign g)).carrier ⟨Q, hQ, hlow (assign g)⟩ y z) x := by
  have hP := (hD.2.2.2.2.1 (assign g).1 (assign g).2).1
  have hf := differentiableAt_constructed_carrier (T (assign g)) hP
    ⟨Q, hQ, hlow (assign g)⟩ hx hz
  change R g • gradient (fun y ↦ (T (assign g)).carrier ⟨Q, hQ, hlow (assign g)⟩ y z) x =
    gradient (fun y ↦ R g * (T (assign g)).carrier ⟨Q, hQ, hlow (assign g)⟩ y z) x
  unfold gradient
  rw [(hf.hasFDerivAt.const_mul (R g)).fderiv]
  exact (map_smul (toDual ℝ (Euclidean n)).symm (R g) _).symm

/-- Apply the original `currentGroup` band and angular protection to the
literal normalized phase of the SAME constructed signed pair
(`app:ch_pairs:setup:pairs-lag`). The primitive geometric inputs are exactly
those supplied by `exists_constructed_signed_geometry`; all phase-gradient
identifications and differentiability are proved here. This supplies the
first-derivative data consumed by the full complementary source estimate. -/
theorem normalized_current_pair_phase_geometry
    {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {G : Type*} (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
    (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
    (q : SignedPairs.Pair G (Euclidean 3) (groupCube D assign))
    {x : Euclidean n} (hx : ∀ i, x ∈ ball (0 : Euclidean n) (T i).physicalRadius)
    {a b : ℝ} {K : Set (Euclidean n)}
    (hband : a * q.beat ≤ ‖q.vector (currentGroup T assign R Q hQ hlow x)‖ ∧
      ‖q.vector (currentGroup T assign R Q hQ hlow x)‖ ≤ b * q.beat)
    (hK : NormedSpace.normalize (q.vector (currentGroup T assign R Q hQ hlow x)) ∈ K) :
    let d := fderiv ℝ (fun y ↦ q.vector (fun g z ↦
      R g * (T (assign g)).carrier ⟨Q, hQ, hlow (assign g)⟩ y z) / q.beat) x
    a ≤ ‖d‖ ∧ ‖d‖ ≤ b ∧ NormedSpace.normalize d ∈ (toDual ℝ (Euclidean n)) '' K := by
  let φ : G → Euclidean 3 → Euclidean n → ℝ := fun g z y ↦
    R g * (T (assign g)).carrier ⟨Q, hQ, hlow (assign g)⟩ y z
  have hφ (g : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign g) :
      DifferentiableAt ℝ (φ g z) x :=
    (differentiableAt_constructed_carrier (T (assign g))
      (hD.2.2.2.2.1 (assign g).1 (assign g).2).1
      ⟨Q, hQ, hlow (assign g)⟩ (hx (assign g)) hz).const_mul (R g)
  have he (g : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign g) :
      currentGroup T assign R Q hQ hlow x g z = gradient (φ g z) x :=
    currentGroup_eq_gradient_radial_carrier hD T assign R Q hQ hlow g (hx (assign g)) hz
  have heq : q.vector (fun g z ↦ gradient (φ g z) x) =
      q.vector (currentGroup T assign R Q hQ hlow x) := by
    cases q with
    | difference g z w hne =>
      simp only [SignedPairs.Pair.vector, ← he g z z.property, ← he g w w.property]
    | sum g z w =>
      simp only [SignedPairs.Pair.vector, ← he g z z.property, ← he g w w.property]
    | cross g h hne z w s t hs ht =>
      simp only [SignedPairs.Pair.vector, ← he g z z.property, ← he h w w.property]
  exact normalized_signed_pair_phase_geometry q φ hφ (by rwa [heq]) (by rwa [heq])

end JanetCartan.SignedProductEstimates
