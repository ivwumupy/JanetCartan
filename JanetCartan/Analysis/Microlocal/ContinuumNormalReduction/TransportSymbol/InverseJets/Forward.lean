module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Homogeneity
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables

/-!
# The forward transport map with all parameters

The actual averaged gradient of `app:ch_background:eq:bg-Psi`. Its augmentation
retains both physical positions and the spectator, so the inverse theorem can
be applied to joint jets rather than only to a fixed parameter slice.
-/

@[expose] public noncomputable section
open Set MeasureTheory

namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- The literal averaged gradient of `Y(x,s,v) · η`, from
`app:ch_background:eq:bg-Psi`. -/
def transportAveragedGradient
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) : Euclidean n :=
  ∫ t in (0 : ℝ)..1, gradient
    (fun x ↦ inner ℝ (Y (x, p.2.1)) p.2.2)
    (p.1.2 + t • (p.1.1 - p.1.2))

/-- Augment the forward map by the unchanged positions and spectator in
`app:ch_background:eq:bg-Psi`. This is the map inverted by
`inverseCoordinates`, with the original ordering of all variables. -/
def augmentedTransportGradient
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) : Variables n × Euclidean 2 :=
  ((p.1.1, p.1.2, transportAveragedGradient Y p), p.2.1.2)

/-- The geometric inverse identity implies the full augmented right-inverse
identity, retaining the spectator and both positions
(`app:ch_background:eq:bg-Psi`). -/
theorem augmentedTransportGradient_inverseCoordinates
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    {Ω : Set (Variables n × Euclidean 2)}
    (hu : ∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) :
    EqOn (augmentedTransportGradient Y ∘ inverseCoordinates u) id Ω := by
  intro p hp
  rcases p with ⟨⟨x, x', k⟩, v⟩
  simp only [Function.comp_apply, augmentedTransportGradient, inverseCoordinates,
    id_eq] at hu ⊢
  rw [hu _ hp]

/-- Positive scaling of the transverse covector gives degree one for the
genuine averaged gradient. No scaling identity for an unspecified forward
map is assumed (`app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_smul
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (t : ℝ) (p : InputVariables n) :
    transportAveragedGradient Y (scaleInput t p) = t • transportAveragedGradient Y p := by
  unfold transportAveragedGradient
  have he : (fun x ↦ inner ℝ (Y (x, p.2.1)) (t • p.2.2)) =
      fun x ↦ t • inner ℝ (Y (x, p.2.1)) p.2.2 := by
    funext x
    exact inner_smul_right _ _ _
  simp only [scaleInput, he, gradient]
  simp_rw [show (fun x ↦ t • inner ℝ (Y (x, p.2.1)) p.2.2) =
    t • (fun x ↦ inner ℝ (Y (x, p.2.1)) p.2.2) from rfl,
    fderiv_const_smul_field, Pi.smul_apply, map_smul]
  exact intervalIntegral.integral_smul t _

/-- The augmented forward map scales only its output covector
(`app:ch_background:eq:bg-Psi`). -/
theorem augmentedTransportGradient_scaleInput
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (t : ℝ) (p : InputVariables n) :
    augmentedTransportGradient Y (scaleInput t p) =
      (scaleFrequency t (augmentedTransportGradient Y p).1,
        (augmentedTransportGradient Y p).2) := by
  change ((p.1.1, p.1.2, transportAveragedGradient Y (scaleInput t p)), p.2.1.2) = _
  rw [transportAveragedGradient_smul]
  rfl

/-- Uniqueness on the conic chart forces the genuine inverse's radial scaling
law. This discharges the inverse scaling input of `extendedDensity_homogeneous`
in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem inverseCoordinates_scale_of_injective
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    {Ω : Set (Variables n × Euclidean 2)} {W : Set (InputVariables n)}
    (hright : ∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2)
    (hrange : MapsTo (inverseCoordinates u) Ω W)
    (hinj : InjOn (augmentedTransportGradient Y) W)
    (t : ℝ) (hscale : MapsTo (scaleInput t) W W)
    {p : Variables n × Euclidean 2} (hp : p ∈ Ω)
    (htp : (scaleFrequency t p.1, p.2) ∈ Ω) :
    u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2) := by
  have hright' := augmentedTransportGradient_inverseCoordinates Y u hright
  have he : inverseCoordinates u (scaleFrequency t p.1, p.2) =
      scaleInput t (inverseCoordinates u p) := by
    apply hinj (hrange htp) (hscale (hrange hp))
    rw [augmentedTransportGradient_scaleInput]
    change (augmentedTransportGradient Y ∘ inverseCoordinates u)
        (scaleFrequency t p.1, p.2) = _
    rw [hright' htp]
    have h := hright' hp
    dsimp only [Function.comp_apply, id_eq] at h ⊢
    rw [h]
  exact congrArg (fun q : InputVariables n ↦ (q.2.1.1, q.2.2)) he

end JanetCartan.ContinuumNormalReduction.TransportSymbol
