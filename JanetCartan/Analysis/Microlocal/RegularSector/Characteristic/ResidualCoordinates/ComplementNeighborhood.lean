module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Symbols

/-!
# A common physical and spectral complement neighborhood

The same selected minor used in the physical columns defines an open domain
for the off-root inverse. Its completion is nonsingular at the actual root,
so a product neighborhood of physical points and frequencies is constructed,
not assumed. This supplies the common support needed by
`CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:complement-inverse` and
`app:ch_regular_base:eq:complement-symbol` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- The original root matrices and actual off-root spectral displacement.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
def complementData (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (p : E × E) : (Mat × Mat) × ℝ :=
  let w := rootState p.1 (spatialPart p.2)
  ((rootPencil (coordinateSplit i) Q h w, rootTimeCoefficient (coordinateSplit i) Q w),
    p.2 0 - h w)

/-- The actual domain of the selected-minor inverse, including its root chart.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def complementDomain (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (r c : Fin (d + 1))
    (D : Set (RootState (Euclidean d))) : Set (E × E) :=
  {p | rootState p.1 (spatialPart p.2) ∈ D} ∩
    complementData i Q h ⁻¹' minorComplementDomain r c

private theorem contDiff_rootState_frequency :
    ContDiff ℝ ∞ (fun p : E × E ↦ rootState p.1 (spatialPart p.2)) := by
  exact (((EuclideanSpace.proj 0).contDiff.comp contDiff_fst).prodMk
    (((coordinateSplit 0).contDiff.comp contDiff_fst).snd.prodMk
      ((coordinateSplit 0).contDiff.comp contDiff_snd).snd))

/-- Smoothness of the literal complement data only on its actual root chart.
The inputs are exactly the root regularity and physical containment exported
by `exists_pencil_leading_amplitude`.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
theorem contDiffOn_complementData
    (i : Fin (d + 1)) {Ω : Set E} {Q : E → Fin (d + 1) → Mat}
    (hQ : ContDiffOn ℝ ∞ Q Ω) {D : Set (RootState (Euclidean d))}
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω) :
    ContDiffOn ℝ ∞ (complementData i Q h)
      {p : E × E | rootState p.1 (spatialPart p.2) ∈ D} := by
  have hw := (contDiff_rootState_frequency (d := d)).contDiffOn
    (s := {p : E × E | rootState p.1 (spatialPart p.2) ∈ D})
  exact (((contDiffOn_rootPencil _ hQ hh hmap).comp hw (fun _ hp ↦ hp)).prodMk
    ((contDiffOn_rootTimeCoefficient _ hQ hmap).comp hw (fun _ hp ↦ hp))).prodMk
      ((((coordinateSplit 0).contDiff.comp contDiff_snd).fst).contDiffOn.sub
        (hh.comp hw (fun _ hp ↦ hp)))

/-- The physical/spectral complement domain is open; no global extension of
the root or inverse is used. Source: `app:ch_regular_base:eq:complement-inverse`. -/
theorem isOpen_complementDomain
    (i : Fin (d + 1)) {Ω : Set E} {Q : E → Fin (d + 1) → Mat}
    (hQ : ContDiffOn ℝ ∞ Q Ω) {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) : IsOpen (complementDomain i Q h r c D) :=
  (contDiffOn_complementData i hQ hh hmap).continuousOn.isOpen_inter_preimage
    (hD.preimage contDiff_rootState_frequency.continuous)
    (minorComplementDomain_regular r c (m := ∞)).1

/-- The actual restricted inverse satisfies the complement equation throughout
its open domain, with the original oblique projector. The root equation is
an output of the same root producer, not an assumed complement identity.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
theorem complement_identity_on_domain
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (r c : Fin (d + 1))
    {D : Set (RootState (Euclidean d))}
    (hroot : ∀ w ∈ D, (rootPencil (coordinateSplit i) Q h w).det = 0)
    {x ξ : E} (hp : (x, ξ) ∈ complementDomain i Q h r c D) :
    (∑ a, (ξ a : ℂ) • (coefficient i Q x a).map Complex.ofReal) *
      bminus i Q h r c x ξ = 1 - projector i Q h r c x (spatialPart ξ) := by
  obtain ⟨_, hl, hn, _⟩ := minor_normalization (hroot _ hp.1) hp.2.1.1 hp.2.1.2
  have hid := complementInverse_identity hl hn hp.2.2
  rw [principalMatrix_eq, pencil_eq_root_add i Q h]
  ext j k
  have hij := congrArg (fun M : Mat ↦ (M j k : ℂ)) hid
  simpa [complementData, bminus, minorComplementInverse, projector,
    complementProjection, Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.one_apply, apply_ite Complex.ofReal] using hij

/-- Select one physical neighborhood and one frequency neighborhood on which
the same off-root complement exists. This closes the quantifier gap between
pointwise spectral intervals and a fixed right multiplier. The original root,
minor and transport denominator are the same chart's exported outputs.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_common_complement_neighborhood
    (i : Fin (d + 1)) {Ω : Set E} {Q : E → Fin (d + 1) → Mat}
    (hQ : ContDiffOn ℝ ∞ Q Ω) {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) (x : E) (η : Euclidean d)
    (hx : rootState x η ∈ D)
    (hroot : (rootPencil (coordinateSplit i) Q h (rootState x η)).det = 0)
    (hm : (rootPencil (coordinateSplit i) Q h (rootState x η)).adjugate r c ≠ 0)
    (ht : fderiv ℝ Matrix.det (rootPencil (coordinateSplit i) Q h (rootState x η))
      (rootTimeCoefficient (coordinateSplit i) Q (rootState x η)) ≠ 0) :
    ∃ X F : Set E, IsOpen X ∧ x ∈ X ∧ IsOpen F ∧
      timeSpacePoint (h (rootState x η)) η ∈ F ∧
      X ×ˢ F ⊆ complementDomain i Q h r c D := by
  have htr := minorTransportCoefficient_ne_zero_of_root hroot hm ht
  obtain ⟨_, hl, hn, hk⟩ := minor_normalization hroot hm htr
  have hd := pencilCompletion_det_ne_zero hl hn hk
  have hp : (x, timeSpacePoint (h (rootState x η)) η) ∈
      complementDomain i Q h r c D := by
    simpa [complementDomain, complementData, minorComplementDomain] using
      And.intro hx (And.intro (And.intro hm htr) hd)
  exact mem_nhds_prod_iff'.mp ((isOpen_complementDomain i hQ hD hh hmap r c).mem_nhds hp)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
