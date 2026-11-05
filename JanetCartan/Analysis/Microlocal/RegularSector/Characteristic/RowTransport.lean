module

public import JanetCartan.Analysis.ODE.PositiveTransport.FlowSolution

/-!
# Signed row transport with a variable initial time

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, construct
the row amplitude by the exponential integral on a supplied characteristic.
The coefficient may depend on the initial time as well as the characteristic
label, as it does when the nullvector is evaluated at the two-time phase.
The initial row is arbitrary: no positivity of `lᵀ σ` is required.

The same explicit formula is smooth in both times and all label variables,
attains the diagonal data, solves the transport equation, and has the expected
support and low bound. Pullback through a supplied inverse flow gives the
physical directional equation. The regular-sector construction still owes the
actual two-time Hamilton flow, its inverse chart and the fixed-shift symbol
budgets for its potential and row data; none of those is asserted here.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.RegularSector.Characteristic

variable {P X ι : Type*} [Fintype ι]

/-- The signed row in the characteristic-kernel construction. Its arguments are
`(t, (s, p))`, and `c (u, (s, p))` is the potential on the same characteristic.
The oriented integral also defines the solution when `t < s`. -/
def rowTransport (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ)
    (q : ℝ × (ℝ × P)) : ι → ℝ :=
  transportFactor (fun u ↦ c (u, q.2)) q.2.1 q.1 • r q.2

omit [Fintype ι] in
/-- The diagonal row is the prescribed signed datum
(`app:ch_regular_base:lem:characteristic-kernel`, transport step). -/
@[simp] theorem rowTransport_diagonal (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) (s : ℝ) (p : P) :
    rowTransport c r (s, (s, p)) = r (s, p) := by
  simp [rowTransport]

omit [Fintype ι] in
/-- The constructed row vanishes exactly on the zero set of its initial row.
This retains the source cutoff in the characteristic-kernel construction. -/
@[simp] theorem rowTransport_eq_zero_iff (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) (q : ℝ × (ℝ × P)) :
    rowTransport c r q = 0 ↔ r q.2 = 0 := by
  simp [rowTransport, (transportFactor_pos _ _ _).ne']

omit [Fintype ι] in
/-- The pointwise support is transported from the original source datum
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem support_rowTransport (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) :
    Function.support (rowTransport c r) = Prod.snd ⁻¹' Function.support r := by
  ext q
  simp [Function.mem_support]

/-- The actual row solves the scalar transport equation in every component,
without a sign restriction on the data
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_rowTransport {c : ℝ × (ℝ × P) → ℝ}
    (r : ℝ × P → ι → ℝ) {I : Set ℝ} {s t : ℝ} {p : P}
    (hI : IsOpen I) (hIc : OrdConnected I)
    (hc : ContinuousOn (fun u ↦ c (u, (s, p))) I)
    (hs : s ∈ I) (ht : t ∈ I) :
    HasDerivAt (fun u ↦ rowTransport c r (u, (s, p)))
      (-c (t, (s, p)) • rowTransport c r (t, (s, p))) t := by
  simpa only [rowTransport, mul_smul] using
    (hasDerivAt_transportFactor hI hIc hc hs ht).smul_const (r (s, p))

/-- Uniqueness of the constructed signed row on the given characteristic,
proved componentwise from the scalar ODE
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rowTransport_unique {c : ℝ × (ℝ × P) → ℝ}
    (r : ℝ × P → ι → ℝ) {I : Set ℝ} {s : ℝ} {p : P}
    {a : ℝ → ι → ℝ} (hI : IsOpen I) (hIc : OrdConnected I)
    (hc : ContinuousOn (fun u ↦ c (u, (s, p))) I) (hs : s ∈ I)
    (ha : ∀ t ∈ I, HasDerivAt a (-c (t, (s, p)) • a t) t)
    (hainit : a s = r (s, p)) :
    EqOn a (fun t ↦ rowTransport c r (t, (s, p))) I := by
  intro t ht
  funext i
  apply scalarTransport_unique (u := fun u ↦ a u i) hI hIc hc hs
    (fun u hu ↦ ?_) (congrFun hainit i) ht
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt u (ha u hu))

/-- The low row bound follows from the potential bound on the actual time
segment; its constant is independent of the signed initial datum
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_rowTransport_le {c : ℝ × (ℝ × P) → ℝ}
    (r : ℝ × P → ι → ℝ) {s t K T : ℝ} {p : P}
    (hK : 0 ≤ K) (ht : |t - s| ≤ T)
    (hc : ∀ u ∈ uIoc s t, |c (u, (s, p))| ≤ K) :
    ‖rowTransport c r (t, (s, p))‖ ≤ Real.exp (K * T) * ‖r (s, p)‖ := by
  have hint : |∫ u in s..t, c (u, (s, p))| ≤ K * T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun u hu ↦ show ‖c (u, (s, p))‖ ≤ K by
        simpa only [Real.norm_eq_abs] using hc u hu)
    have h' : |∫ u in s..t, c (u, (s, p))| ≤ K * |t - s| := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_left ht hK)
  have he : transportFactor (fun u ↦ c (u, (s, p))) s t ≤ Real.exp (K * T) := by
    apply Real.exp_le_exp.mpr
    exact (neg_le_abs _).trans hint
  rw [rowTransport, norm_smul, Real.norm_eq_abs,
    abs_of_pos (transportFactor_pos _ _ _)]
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

section Smooth

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι] in
/-- Express the variable-lower-endpoint integral using one fixed primitive.
This identity supplies regularity in the source time; it is not inferred from
regularity at each fixed source time
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rowTransport_eq_fixed_primitive {c : ℝ × (ℝ × P) → ℝ}
    (r : ℝ × P → ι → ℝ) {I : Set ℝ} {U : Set P} {t₀ : ℝ}
    (hIc : OrdConnected I) (hc : ContinuousOn c (I ×ˢ (I ×ˢ U)))
    (ht₀ : t₀ ∈ I) {q : ℝ × (ℝ × P)} (hq : q ∈ I ×ˢ (I ×ˢ U)) :
    rowTransport c r q =
      Real.exp (-((∫ u in t₀..q.1, c (u, q.2)) -
        ∫ u in t₀..q.2.1, c (u, q.2))) • r q.2 := by
  have hct : ContinuousOn (fun u ↦ c (u, q.2)) I :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu ↦ ⟨hu, hq.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hct.mono (hIc.uIcc_subset ht₀ hq.2.1)).intervalIntegrable
    (hct.mono (hIc.uIcc_subset hq.2.1 hq.1)).intervalIntegrable
  have he : (∫ u in q.2.1..q.1, c (u, q.2)) =
      (∫ u in t₀..q.1, c (u, q.2)) - ∫ u in t₀..q.2.1, c (u, q.2) := by
    linarith
  simp only [rowTransport, transportFactor, he]

/-- Joint smoothness in both times and all characteristic labels of the actual
signed row, including the diagonal
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rowTransport {c : ℝ × (ℝ × P) → ℝ}
    {r : ℝ × P → ι → ℝ} {I : Set ℝ} {U : Set P} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ (I ×ˢ U)))
    (hr : ContDiffOn ℝ ∞ r (I ×ˢ U)) (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ ∞ (rowTransport c r) (I ×ˢ (I ×ˢ U)) := by
  have hi := contDiffOn_parametricIntervalIntegral hI hIc (hI.prod hU) hc ht₀
  have his : ContDiffOn ℝ ∞
      (fun q : ℝ × (ℝ × P) ↦ ∫ u in t₀..q.2.1, c (u, q.2))
      (I ×ˢ (I ×ˢ U)) :=
    hi.comp (contDiffOn_snd.fst.prodMk contDiffOn_snd)
      (fun _ hq ↦ ⟨hq.2.1, hq.2⟩)
  apply ((hi.sub his).neg.exp.smul
    (hr.comp contDiffOn_snd (fun _ hq ↦ hq.2))).congr
  intro q hq
  exact rowTransport_eq_fixed_primitive r hIc hc.continuousOn ht₀ hq

end Smooth

/-- Pull the constructed row back through the inverse characteristic chart.
The arguments remain `(t, (s, x))`; the same chart is used for every row entry
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def physicalRowTransport (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ)
    (Y : ℝ × (ℝ × X) → P) (q : ℝ × (ℝ × X)) : ι → ℝ :=
  rowTransport c r (q.1, (q.2.1, Y q))

omit [Fintype ι] in
/-- Exact evaluation on the same characteristic, retaining the source time
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem physicalRowTransport_along_flow (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) {Y : ℝ × (ℝ × X) → P}
    {Φ : ℝ × (ℝ × P) → X} {t s : ℝ} {p : P}
    (hY : Y (t, (s, Φ (t, (s, p)))) = p) :
    physicalRowTransport c r Y (t, (s, Φ (t, (s, p)))) =
      rowTransport c r (t, (s, p)) := by
  simp only [physicalRowTransport, hY]

omit [Fintype ι] in
/-- The physical row takes the exact initial data on the diagonal of the
two-time flow (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem physicalRowTransport_diagonal (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) {Y : ℝ × (ℝ × X) → P}
    {Φ : ℝ × (ℝ × P) → X} {s : ℝ} {p : P}
    (hY : Y (s, (s, Φ (s, (s, p)))) = p) :
    physicalRowTransport c r Y (s, (s, Φ (s, (s, p)))) = r (s, p) := by
  rw [physicalRowTransport_along_flow c r hY, rowTransport_diagonal]

omit [Fintype ι] in
/-- The row's support is the inverse image of the signed source data's support,
so a source cutoff remains attached to its actual flowout
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem support_physicalRowTransport (c : ℝ × (ℝ × P) → ℝ)
    (r : ℝ × P → ι → ℝ) (Y : ℝ × (ℝ × X) → P) :
    Function.support (physicalRowTransport c r Y) =
      (fun q ↦ (q.2.1, Y q)) ⁻¹' Function.support r := by
  ext q
  simp [physicalRowTransport, Function.mem_support]

/-- The constructed physical row satisfies its ODE along the supplied flow
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_physicalRowTransport_along_flow {c : ℝ × (ℝ × P) → ℝ}
    (r : ℝ × P → ι → ℝ) {I : Set ℝ} {s t : ℝ} {p : P}
    {Y : ℝ × (ℝ × X) → P} {Φ : ℝ × (ℝ × P) → X}
    (hI : IsOpen I) (hIc : OrdConnected I)
    (hc : ContinuousOn (fun u ↦ c (u, (s, p))) I)
    (hs : s ∈ I) (ht : t ∈ I)
    (hY : ∀ u ∈ I, Y (u, (s, Φ (u, (s, p)))) = p) :
    HasDerivAt (fun u ↦ physicalRowTransport c r Y (u, (s, Φ (u, (s, p)))))
      (-c (t, (s, p)) • physicalRowTransport c r Y (t, (s, Φ (t, (s, p))))) t := by
  have he : (fun u ↦ physicalRowTransport c r Y (u, (s, Φ (u, (s, p))))) =ᶠ[𝓝 t]
      (fun u ↦ rowTransport c r (u, (s, p))) := by
    filter_upwards [hI.mem_nhds ht] with u hu
    exact physicalRowTransport_along_flow c r (hY u hu)
  rw [physicalRowTransport_along_flow c r (hY t ht)]
  exact (hasDerivAt_rowTransport r hI hIc hc hs ht).congr_of_eventuallyEq he

section SmoothPhysical

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Pullback preserves joint smoothness of the actual row in output time,
source time and physical variables
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_physicalRowTransport {c : ℝ × (ℝ × P) → ℝ}
    {r : ℝ × P → ι → ℝ} {I : Set ℝ} {U : Set P} {t₀ : ℝ}
    {Y : ℝ × (ℝ × X) → P} {D : Set (ℝ × (ℝ × X))}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ (I ×ˢ U)))
    (hr : ContDiffOn ℝ ∞ r (I ×ˢ U)) (ht₀ : t₀ ∈ I)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, (q.2.1, Y q))) D (I ×ˢ (I ×ˢ U))) :
    ContDiffOn ℝ ∞ (physicalRowTransport c r Y) D :=
  (contDiffOn_rowTransport hI hIc hU hc hr ht₀).comp
    (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hY)) hYU

/-- The physical equation is obtained by differentiating the same flow, with
zero source-time velocity. This is the signed row equation used for `W₀ = ka`
in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem fderiv_physicalRowTransport_along_flow {c : ℝ × (ℝ × P) → ℝ}
    {r : ℝ × P → ι → ℝ} {I : Set ℝ} {U : Set P} {s t : ℝ} {p : P}
    {Y : ℝ × (ℝ × X) → P} {Φ : ℝ × (ℝ × P) → X}
    {D : Set (ℝ × (ℝ × X))} {v : X}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U) (hD : IsOpen D)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ (I ×ˢ U)))
    (hr : ContDiffOn ℝ ∞ r (I ×ˢ U)) (hs : s ∈ I) (ht : t ∈ I) (hp : p ∈ U)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, (q.2.1, Y q))) D (I ×ˢ (I ×ˢ U)))
    (hYΦ : ∀ u ∈ I, Y (u, (s, Φ (u, (s, p)))) = p)
    (hq : (t, (s, Φ (t, (s, p)))) ∈ D)
    (hΦ : HasDerivAt (fun u ↦ Φ (u, (s, p))) v t) :
    fderiv ℝ (physicalRowTransport c r Y) (t, (s, Φ (t, (s, p)))) (1, (0, v)) =
      -c (t, (s, p)) • physicalRowTransport c r Y (t, (s, Φ (t, (s, p)))) := by
  have ha := (contDiffOn_physicalRowTransport hI hIc hU hc hr hs hY hYU).contDiffAt
    (hD.mem_nhds hq)
  have hd := (ha.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk ((hasDerivAt_const t s).prodMk hΦ))
  have hct : ContinuousOn (fun u ↦ c (u, (s, p))) I :=
    hc.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu ↦ ⟨hu, hs, hp⟩)
  exact hd.unique (hasDerivAt_physicalRowTransport_along_flow r hI hIc hct hs ht hYΦ)

end SmoothPhysical

end JanetCartan.RegularSector.Characteristic
