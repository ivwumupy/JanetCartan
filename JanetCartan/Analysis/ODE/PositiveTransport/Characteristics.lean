module

public import JanetCartan.Analysis.ODE.PositiveTransport.TimeRegularity

/-!
# Families of scalar characteristic solutions

For `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-positive`, the
label type `P` retains both initial spatial variables and carrier parameters.
The coefficient is evaluated along the given flow, and the initial datum is
constant along each characteristic. A footpoint map transfers the result back
to physical coordinates. No construction of that flow or its inverse is needed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Topology

namespace JanetCartan

variable {P X : Type*}

/-- `app:ch_waves:thm:leading`: pull back the zeroth-order coefficient along the
fixed characteristic flow. Carrier parameters can be retained in the state `X`. -/
def flowTransportCoefficient (c : ℝ × X → ℝ) (Φ : ℝ × P → X) (q : ℝ × P) : ℝ :=
  c (q.1, Φ q)

/-- `app:ch_waves:thm:leading`: the characteristic formula, with initial spatial
and carrier variables collected in `P`. -/
def characteristicTransport (c : ℝ × P → ℝ) (t₀ : ℝ) (r : P → ℝ)
    (q : ℝ × P) : ℝ :=
  scalarTransport (fun s ↦ c (s, q.2)) t₀ (r q.2) q.1

/-- `app:ch_waves:thm:leading`: initial values are attained for every label. -/
@[simp] theorem characteristicTransport_initial (c : ℝ × P → ℝ) (t₀ : ℝ)
    (r : P → ℝ) (p : P) : characteristicTransport c t₀ r (t₀, p) = r p := by
  simp [characteristicTransport]

/-- `app:ch_background:prop:bg-positive`: positivity is retained for every label. -/
theorem characteristicTransport_pos (c : ℝ × P → ℝ) (t₀ t : ℝ)
    {r : P → ℝ} {p : P} (hr : 0 < r p) :
    0 < characteristicTransport c t₀ r (t, p) := scalarTransport_pos _ _ _ hr

/-- `app:ch_waves:thm:leading`: transport is a linear operator on initial functions. -/
def characteristicTransportLinearMap (c : ℝ × P → ℝ) (t₀ : ℝ) :
    (P → ℝ) →ₗ[ℝ] (ℝ × P → ℝ) where
  toFun := characteristicTransport c t₀
  map_add' r q := funext fun w ↦ scalarTransport_add _ t₀ (r w.2) (q w.2) w.1
  map_smul' k r := funext fun w ↦ scalarTransport_smul _ t₀ k (r w.2) w.1

/-- `app:ch_background:eq:bg-affine-mean`: transport of a density, extended
linearly to all real densities. -/
def characteristicDensityLinearMap (c : ℝ × P → ℝ) (t₀ : ℝ) :
    (P → ℝ) →ₗ[ℝ] (ℝ × P → ℝ) where
  toFun ρ q := transportFactor (fun s ↦ c (s, q.2)) t₀ q.1 ^ 2 * ρ q.2
  map_add' ρ σ := funext fun q ↦ mul_add _ (ρ q.2) (σ q.2)
  map_smul' k ρ := by ext; dsimp; ring

/-- `app:ch_waves:thm:leading`: the density operator gives the square of the
actual amplitude, without using a square root to define the operator. -/
theorem characteristicTransport_sq (c : ℝ × P → ℝ) (t₀ : ℝ) (r : P → ℝ)
    (q : ℝ × P) : characteristicTransport c t₀ r q ^ 2 =
      characteristicDensityLinearMap c t₀ (fun p ↦ r p ^ 2) q := by
  exact scalarTransport_sq _ _ _ _

/-- `app:ch_waves:thm:leading`: the constructed family satisfies the scalar
transport equation on every given characteristic. -/
theorem hasDerivAt_characteristicTransport {c : ℝ × P → ℝ} {I : Set ℝ}
    {t₀ t : ℝ} (hI : IsOpen I) (hIc : OrdConnected I) (p : P)
    (hc : ContinuousOn (fun s ↦ c (s, p)) I) (ht₀ : t₀ ∈ I) (ht : t ∈ I)
    (r : P → ℝ) :
    HasDerivAt (fun s ↦ characteristicTransport c t₀ r (s, p))
      (-c (t, p) * characteristicTransport c t₀ r (t, p)) t :=
  hasDerivAt_scalarTransport hI hIc hc ht₀ ht (r p)

/-- `app:ch_waves:thm:leading`: uniqueness for families, including spectator
parameters, throughout the prescribed label and time domain. -/
theorem characteristicTransport_unique {c u : ℝ × P → ℝ} {r : P → ℝ}
    {I : Set ℝ} {U : Set P} {t₀ : ℝ} (hI : IsOpen I) (hIc : OrdConnected I)
    (hc : ∀ p ∈ U, ContinuousOn (fun t ↦ c (t, p)) I) (ht₀ : t₀ ∈ I)
    (hu : ∀ p ∈ U, ∀ t ∈ I, HasDerivAt (fun s ↦ u (s, p)) (-c (t, p) * u (t, p)) t)
    (hu₀ : ∀ p ∈ U, u (t₀, p) = r p) :
    EqOn u (characteristicTransport c t₀ r) (I ×ˢ U) := by
  intro q hq
  exact scalarTransport_unique hI hIc (hc q.2 hq.2) ht₀ (hu q.2 hq.2)
    (hu₀ q.2 hq.2) hq.1

/-- `app:ch_waves:thm:leading`: the family is smooth in time for each label. -/
theorem contDiffOn_characteristicTransport_time {c : ℝ × P → ℝ} {I : Set ℝ}
    {t₀ : ℝ} (hI : IsOpen I) (hIc : OrdConnected I) (p : P)
    (hc : ContDiffOn ℝ ∞ (fun s ↦ c (s, p)) I) (ht₀ : t₀ ∈ I) (r : P → ℝ) :
    ContDiffOn ℝ ∞ (fun t ↦ characteristicTransport c t₀ r (t, p)) I :=
  contDiffOn_scalarTransport hI hIc hc ht₀ (r p)

/-- `app:ch_waves:thm:leading`: evaluate the characteristic solution at the
footpoint in the fixed inverse chart. -/
def transportFromFootpoint (c : ℝ × P → ℝ) (t₀ : ℝ) (r : P → ℝ)
    (Y : ℝ × X → P) (q : ℝ × X) : ℝ :=
  characteristicTransport c t₀ r (q.1, Y q)

/-- `app:ch_waves:thm:leading`: a left inverse chart recovers the solution
on the given characteristic; the inverse relation is geometric input. -/
theorem transportFromFootpoint_along_flow (c : ℝ × P → ℝ) (t₀ : ℝ) (r : P → ℝ)
    {Y : ℝ × X → P} {Φ : ℝ × P → X} {t : ℝ} {p : P}
    (hY : Y (t, Φ (t, p)) = p) :
    transportFromFootpoint c t₀ r Y (t, Φ (t, p)) =
      characteristicTransport c t₀ r (t, p) := by
  simp only [transportFromFootpoint, hY]

/-- `app:ch_background:prop:bg-positive`: the physical amplitude is positive
whenever the initial datum at its footpoint is positive. -/
theorem transportFromFootpoint_pos (c : ℝ × P → ℝ) (t₀ : ℝ) (r : P → ℝ)
    (Y : ℝ × X → P) (q : ℝ × X) (hr : 0 < r (Y q)) :
    0 < transportFromFootpoint c t₀ r Y q := characteristicTransport_pos _ _ _ hr

/-- `app:ch_waves:thm:leading`: the physical amplitude satisfies the transport
equation along the supplied flow, using its actual inverse footpoint chart. -/
theorem hasDerivAt_transportFromFootpoint_along_flow {c : ℝ × P → ℝ}
    {I : Set ℝ} {t₀ t : ℝ} (hI : IsOpen I) (hIc : OrdConnected I) (p : P)
    (hc : ContinuousOn (fun s ↦ c (s, p)) I) (ht₀ : t₀ ∈ I) (ht : t ∈ I)
    (r : P → ℝ) {Y : ℝ × X → P} {Φ : ℝ × P → X}
    (hY : ∀ s ∈ I, Y (s, Φ (s, p)) = p) :
    HasDerivAt (fun s ↦ transportFromFootpoint c t₀ r Y (s, Φ (s, p)))
      (-c (t, p) * transportFromFootpoint c t₀ r Y (t, Φ (t, p))) t := by
  have he : (fun s ↦ transportFromFootpoint c t₀ r Y (s, Φ (s, p))) =ᶠ[𝓝 t]
      (fun s ↦ characteristicTransport c t₀ r (s, p)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact transportFromFootpoint_along_flow c t₀ r (hY s hs)
  rw [transportFromFootpoint_along_flow c t₀ r (hY t ht)]
  exact (hasDerivAt_characteristicTransport hI hIc p hc ht₀ ht r).congr_of_eventuallyEq he

section SmoothCoefficient

variable [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `app:ch_waves:thm:leading`: a given smooth flow pulls a smooth coefficient
back to a jointly smooth function of time, initial variables, and carriers. -/
theorem contDiffOn_flowTransportCoefficient {c : ℝ × X → ℝ} {Φ : ℝ × P → X}
    {D : Set (ℝ × P)} {V : Set (ℝ × X)}
    (hc : ContDiffOn ℝ ∞ c V) (hΦ : ContDiffOn ℝ ∞ Φ D)
    (hV : MapsTo (fun q ↦ (q.1, Φ q)) D V) :
    ContDiffOn ℝ ∞ (flowTransportCoefficient c Φ) D :=
  hc.comp (contDiffOn_fst.prodMk hΦ) hV

end SmoothCoefficient

end JanetCartan
