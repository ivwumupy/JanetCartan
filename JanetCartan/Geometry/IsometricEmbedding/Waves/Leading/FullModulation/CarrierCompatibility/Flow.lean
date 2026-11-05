module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Coefficients
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Uniqueness on the carrier graph

For `app:ch_waves:thm:leading`, compare supplied flows of the literal full and
carrier directions. The actual producers are the full modulation transport
construction and `NullTransport.exists_projected_local_positive_amplitude`.
Only their initial values, velocities, and range properties are used here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius NNReal

namespace JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Embed a carrier label in the full modulation graph
(`app:ch_waves:thm:leading`). -/
def carrierLabel (p : Euclidean (n - 1) × Euclidean 3) :
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)) :=
  (p.1, p.2, T.reference.spatialPatch p.2)

/-- The literal full normalized velocity in adapted label coordinates;
used only to compare the two supplied flows (`app:ch_waves:thm:leading`). -/
def fullVelocity (row col : Fin n) (t : ℝ)
    (p : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) :
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)) :=
  ((adaptedCoordinates T.data.adapted (transportDirection T Q row col
    ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, p)))).2, 0)

/-- The original normalized carrier velocity, with zero label velocity
(`app:ch_waves:thm:leading`). -/
def carrierVelocity (row col : Fin n) (t : ℝ)
    (p : Euclidean (n - 1) × Euclidean 3) : Euclidean (n - 1) × Euclidean 3 :=
  ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
    ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, p)))).2, 0)

/-- The spatial components of the literal velocities agree on the graph
(`app:ch_waves:thm:leading`). -/
theorem fullVelocity_on_carrier (row col : Fin n) (t : ℝ)
    (p : Euclidean (n - 1) × Euclidean 3) :
    fullVelocity T Q row col t (carrierLabel T p) =
      ((carrierVelocity T Q row col t p).1, 0) := rfl

/-- Zero parameter velocity fixes every spectator parameter. This is used
for both of the supplied flows (`app:ch_waves:thm:leading`). -/
theorem parameters_eq_initial {X Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {γ : ℝ → X × Z} {v : ℝ → X} {a b : ℝ}
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t, 0) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : (γ t).2 = (γ 0).2 := by
  have hz (s) (hs : s ∈ Ioo a b) : HasDerivAt (fun t ↦ (γ t).2) 0 s :=
    (hd s hs).snd
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun s hs ↦ (hz s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hz s hs).deriv) ht h0

/-- ODE uniqueness identifies the full trajectory with the SAME carrier
trajectory, and hence preserves the carrier graph. Both trajectories must
lie in the indicated Lipschitz domain; `Buffers` supplies local quantitative
range deductions (`app:ch_waves:thm:leading`). -/
theorem forward_eq_on_carrier (row col : Fin n)
    {Φ : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    {φ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {p : Euclidean (n - 1) × Euclidean 3} {a b : ℝ} {K : ℝ≥0}
    {S : ℝ → Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fullVelocity T Q row col t) (S t))
    (hΦ₀ : Φ (0, carrierLabel T p) = carrierLabel T p) (hφ₀ : φ (0, p) = p)
    (hΦ : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ Φ (s, carrierLabel T p))
      (fullVelocity T Q row col t (Φ (t, carrierLabel T p))) t)
    (hφ : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ φ (s, p))
      (carrierVelocity T Q row col t (φ (t, p))) t)
    (hΦS : ∀ t ∈ Ioo a b, Φ (t, carrierLabel T p) ∈ S t)
    (hφS : ∀ t ∈ Ioo a b, carrierLabel T (φ (t, p)) ∈ S t) :
    ∀ t ∈ Ioo a b, Φ (t, carrierLabel T p) = carrierLabel T (φ (t, p)) := by
  have hz (t) (ht : t ∈ Ioo a b) : (φ (t, p)).2 = p.2 := by
    simpa only [hφ₀] using parameters_eq_initial h0 hφ ht
  let γ := fun t ↦ ((φ (t, p)).1, (p.2, T.reference.spatialPatch p.2))
  have hg (t) (ht : t ∈ Ioo a b) : γ t = carrierLabel T (φ (t, p)) := by
    simp only [γ, carrierLabel, hz t ht]
  have hd (t) (ht : t ∈ Ioo a b) :
      HasDerivAt γ (fullVelocity T Q row col t (γ t)) t := by
    rw [hg t ht, fullVelocity_on_carrier]
    exact (hφ t ht).fst.prodMk (hasDerivAt_const t _)
  have heq := ODE_solution_unique_of_mem_Ioo hlip h0
    (fun t ht ↦ ⟨hΦ t ht, hΦS t ht⟩)
    (fun t ht ↦ ⟨hd t ht, (hg t ht).symm ▸ hφS t ht⟩)
    (show Φ (0, carrierLabel T p) = γ 0 by rw [hΦ₀]; simp only [γ, hφ₀, carrierLabel])
  intro t ht
  exact (heq ht).trans (hg t ht)

end JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
