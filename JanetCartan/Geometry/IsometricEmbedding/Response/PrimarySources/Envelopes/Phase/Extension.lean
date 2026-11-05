module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds

/-!
# Extending the retained full primary phase

For `app:ch_response:thm:response-literal-transfer` and
`app:ch_response:cor:current-atoms`, a joint cutoff preserves the same
`FullModulation.phase` near the entire compact source and parameter set.
The parameter is the original pair `(z, ζ)`; the free covector is never
replaced by the carrier graph. The original source cutoff is unchanged.
The construction and quantitative instantiation are assembled in `Envelopes.Phase`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponsePrimarySources
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer.GradedPrimitives
open FullPhaseCharts.ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The globally extended phase of the same full primary atom, with a single
joint cutoff fixed before the current frame (`app:ch_response:cor:current-atoms`). -/
def retainedPhaseExtension
    (θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    (x : Euclidean n) (c : Euclidean 3 × Euclidean (n - 1)) : ℝ :=
  cutoffExtension θ (fun w ↦ phase T Q w.1 w.2.2) (x, c)

/-- Local smoothness of the actual Hamilton phase suffices for global joint
smoothness of its cutoff extension (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_retainedPhaseExtension
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hs : tsupport θ ⊆ domain T) :
    ContDiff ℝ ∞ (Function.uncurry (retainedPhaseExtension T Q θ)) :=
  contDiff_cutoffExtension (isOpen_domain T) hθ hs
    (RawPrimary.contDiffOn_fullPhase T Q (fun _ h ↦ h))

/-- A plateau preserves the phase on a neighborhood of every point, including
the boundary of the full shifted-carrier support
(`app:ch_response:thm:response-literal-transfer`). -/
theorem retainedPhaseExtension_eventuallyEq
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ interior {v | θ v = 1}) :
    Function.uncurry (retainedPhaseExtension T Q θ) =ᶠ[𝓝 w]
      (fun v ↦ phase T Q v.1 v.2.2) := by
  apply cutoffExtension_eventuallyEq _ isOpen_interior _ hw
  intro v hv
  have hv' : v ∈ {w | θ w = 1} := interior_subset hv
  exact hv'

/-- All physical jets of the extension equal those of the original free-covector
phase on the full plateau (`app:ch_response:prop:response-graded`). -/
theorem retainedPhaseExtension_physical_eventuallyEq
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    {x : Euclidean n} {c : Euclidean 3 × Euclidean (n - 1)}
    (hx : (x, c) ∈ interior {v | θ v = 1}) :
    (fun y ↦ retainedPhaseExtension T Q θ y c) =ᶠ[𝓝 x]
      (fun y ↦ phase T Q y c.2) :=
  (retainedPhaseExtension_eventuallyEq T Q hx).comp_tendsto
    (continuousAt_id.prodMk continuousAt_const).tendsto

/-- The physical differential is preserved on the complete plateau, not merely
on an identity core (`app:ch_response:prop:response-graded`). -/
theorem fderiv_retainedPhaseExtension_eq
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    {x : Euclidean n} {c : Euclidean 3 × Euclidean (n - 1)}
    (hx : (x, c) ∈ interior {v | θ v = 1}) :
    fderiv ℝ (fun y ↦ retainedPhaseExtension T Q θ y c) x =
      fderiv ℝ (fun y ↦ phase T Q y c.2) x :=
  (retainedPhaseExtension_physical_eventuallyEq T Q hx).fderiv_eq

/-- Every physical phase grade is preserved on the original support
(`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_retainedPhaseExtension_eq
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    {x : Euclidean n} {c : Euclidean 3 × Euclidean (n - 1)}
    (hx : (x, c) ∈ interior {v | θ v = 1}) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y ↦ retainedPhaseExtension T Q θ y c) x =
      iteratedFDeriv ℝ j (fun y ↦ phase T Q y c.2) x :=
  ((retainedPhaseExtension_physical_eventuallyEq T Q hx).iteratedFDeriv ℝ j).self_of_nhds

/-- Restriction of the same full extension to an original carrier recovers
its phase and gradient exactly. The free-covector construction above still
applies on the whole shifted buffer (`app:ch_response:eq:response-exact-phase`). -/
theorem retainedPhaseExtension_on_carrier
    {θ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ}
    {x : Euclidean n} {z : Euclidean 3}
    (hx : (x, (z, T.reference.spatialPatch z)) ∈ interior {v | θ v = 1}) :
    retainedPhaseExtension T Q θ x (z, T.reference.spatialPatch z) = T.carrier Q x z ∧
      gradient (fun y ↦ retainedPhaseExtension T Q θ y (z, T.reference.spatialPatch z)) x =
        T.carrierGradient Q x z := by
  have he := retainedPhaseExtension_physical_eventuallyEq T Q hx
  exact ⟨he.self_of_nhds.trans (phase_on_carrier T Q x z),
    he.gradient_eq.trans (phaseGradient_on_carrier T Q x z)⟩

omit Q in
/-- Use a supplied retained joint working ball to check the complete source
and shifted-carrier support. Its center and radius are unchanged; this lemma
does not select a smaller family (`app:ch_response:cor:current-atoms`). -/
theorem retained_source_product_subset_working_ball
    {S : Set (Euclidean n)} {C : Set (Euclidean 3 × Euclidean (n - 1))}
    {c₀ : Euclidean 3 × Euclidean (n - 1)} {R : ℝ}
    (hworking : closedBall ((0 : Euclidean n), c₀) R ⊆ domain T)
    (hS : S ⊆ closedBall 0 R) (hC : C ⊆ closedBall c₀ R) :
    S ×ˢ C ⊆ domain T := by
  rintro ⟨x, c⟩ ⟨hx, hc⟩
  apply hworking
  change dist (x, c) (0, c₀) ≤ R
  rw [Prod.dist_eq, max_le_iff]
  exact ⟨hS hx, hC hc⟩

omit Q in
/-- The original retained physical ball and full covector ball imply the
joint-domain containment used below. This keeps every supplied carrier label
and its shifted buffer (`app:ch_response:cor:current-atoms`). -/
theorem retained_source_product_subset_domain
    {S : Set (Euclidean n)} {C : Set (Euclidean 3 × Euclidean (n - 1))}
    (hS : S ⊆ ball 0 T.physicalRadius)
    (hC : ∀ c ∈ C, c.2 ∈ ball (covectorCenter T) T.family.radius) :
    S ×ˢ C ⊆ domain T := by
  rintro ⟨x, c⟩ ⟨hx, hc⟩
  have hR : T.physicalRadius < T.family.radius := by
    have hmin := min_le_left T.family.radius (3 * T.family.sourceRadius)
    have hpos := T.physicalRadius_pos
    dsimp only [PatchQuantitativeFamily.physicalRadius] at hpos ⊢
    linarith
  change dist (x, c.2) (0, covectorCenter T) < T.family.radius
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨(hS hx).trans hR, hC c hc⟩

end JanetCartan.ResponsePrimarySources
