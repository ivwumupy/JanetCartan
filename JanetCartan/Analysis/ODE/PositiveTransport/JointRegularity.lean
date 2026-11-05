module

public import JanetCartan.Analysis.ODE.PositiveTransport.Characteristics
public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral

/-!
# Joint regularity of positive scalar transport

For `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-positive`,
the exponential-integral formula is smooth jointly in time, initial spatial
variables, and carrier parameters. All orders use the same open domain and
the same compact subsets. The bounds below are compactness bounds for a fixed
coefficient and datum; they do not assert the manuscript's tame estimates.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan

variable {P X : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `app:ch_waves:thm:leading`: joint smoothness of the actual characteristic
solution, retaining all initial and carrier variables on the original domain. -/
theorem contDiffOn_characteristicTransport {c : ℝ × P → ℝ} {r : P → ℝ}
    {I : Set ℝ} {U : Set P} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ ∞ (characteristicTransport c t₀ r) (I ×ˢ U) := by
  exact (contDiffOn_parametricIntervalIntegral hI hIc hU hc ht₀).neg.exp.mul
    (hr.comp contDiffOn_snd (fun _ hq ↦ hq.2))

/-- `app:ch_waves:thm:leading`: a supplied smooth flow and smooth physical
coefficient give a jointly smooth solution without any integral regularity premise. -/
theorem contDiffOn_flowCharacteristicTransport {c : ℝ × X → ℝ} {Φ : ℝ × P → X}
    {r : P → ℝ} {I : Set ℝ} {U : Set P} {V : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c V) (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ U))
    (hV : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ U) V)
    (hr : ContDiffOn ℝ ∞ r U) (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ ∞ (characteristicTransport (flowTransportCoefficient c Φ) t₀ r)
      (I ×ˢ U) :=
  contDiffOn_characteristicTransport hI hIc hU
    (contDiffOn_flowTransportCoefficient hc hΦ hV) hr ht₀

/-- `app:ch_waves:thm:leading`: smoothness in physical and carrier variables
after evaluating at the supplied smooth footpoint chart. -/
theorem contDiffOn_transportFromFootpoint {c : ℝ × P → ℝ} {r : P → ℝ}
    {Y : ℝ × X → P} {I : Set ℝ} {U : Set P} {D : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U)) :
    ContDiffOn ℝ ∞ (transportFromFootpoint c t₀ r Y) D :=
  (contDiffOn_characteristicTransport hI hIc hU hc hr ht₀).comp
    (contDiffOn_fst.prodMk hY) hYU

/-- `app:ch_background:prop:bg-positive`: a uniform strictly positive lower
bound on any fixed compact time-label box, with no extra lower-bound premise. -/
theorem exists_pos_le_characteristicTransport_on_compact {c : ℝ × P → ℝ} {r : P → ℝ}
    {I : Set ℝ} {U : Set P} {K : Set (ℝ × P)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (hrpos : ∀ p ∈ U, 0 < r p)
    (hK : IsCompact K) (hKD : K ⊆ I ×ˢ U) :
    ∃ m > 0, ∀ q ∈ K, m ≤ characteristicTransport c t₀ r q := by
  exact hK.exists_forall_le'
    ((contDiffOn_characteristicTransport hI hIc hU hc hr ht₀).continuousOn.mono hKD)
    (fun q hq ↦ characteristicTransport_pos c t₀ q.1 (hrpos q.2 (hKD hq).2))

/-- `app:ch_waves:thm:leading`: every joint derivative is bounded on the same
fixed compact box. These are existence bounds, not one-high-norm tame estimates. -/
theorem exists_bound_iteratedFDeriv_characteristicTransport_on_compact
    {c : ℝ × P → ℝ} {r : P → ℝ} {I : Set ℝ} {U : Set P}
    {K : Set (ℝ × P)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (hK : IsCompact K) (hKD : K ⊆ I ×ˢ U) (n : ℕ) :
    ∃ C, ∀ q ∈ K, ‖iteratedFDeriv ℝ n (characteristicTransport c t₀ r) q‖ ≤ C := by
  exact hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv
      (contDiffOn_characteristicTransport hI hIc hU hc hr ht₀)
      (hI.prod hU) (by simp)).mono hKD)

/-- `app:ch_background:prop:bg-positive`: positivity is uniform on a fixed
compact physical box, including its carrier parameters. -/
theorem exists_pos_le_transportFromFootpoint_on_compact {c : ℝ × P → ℝ} {r : P → ℝ}
    {Y : ℝ × X → P} {I : Set ℝ} {U : Set P} {D K : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (hrpos : ∀ p ∈ U, 0 < r p)
    (hY : ContDiffOn ℝ ∞ Y D) (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ m > 0, ∀ q ∈ K, m ≤ transportFromFootpoint c t₀ r Y q := by
  exact hK.exists_forall_le'
    ((contDiffOn_transportFromFootpoint hI hIc hU hc hr ht₀ hY hYU).continuousOn.mono hKD)
    (fun q hq ↦ transportFromFootpoint_pos c t₀ r Y q (hrpos (Y q) (hYU (hKD hq)).2))

/-- `app:ch_waves:thm:leading`: physical and carrier derivatives of every
order are bounded on one fixed compact subset of the open physical chart. -/
theorem exists_bound_iteratedFDeriv_transportFromFootpoint_on_compact
    {c : ℝ × P → ℝ} {r : P → ℝ} {Y : ℝ × X → P}
    {I : Set ℝ} {U : Set P} {D K : Set (ℝ × X)} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U) (hD : IsOpen D)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (hr : ContDiffOn ℝ ∞ r U)
    (ht₀ : t₀ ∈ I) (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ U))
    (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) :
    ∃ C, ∀ q ∈ K, ‖iteratedFDeriv ℝ n (transportFromFootpoint c t₀ r Y) q‖ ≤ C := by
  exact hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv
      (contDiffOn_transportFromFootpoint hI hIc hU hc hr ht₀ hY hYU)
      hD (by simp)).mono hKD)

end JanetCartan
