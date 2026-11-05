module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement

/-!
# Local density weights on the same carrier geometry

The genuine zero-source density is evaluated at a divided ODE footpoint.
Changing the normal field leaves the carrier measure and conic substitution
unchanged. Local measurable representatives suffice on the original mask
support; no regularity of an arbitrary off-support extension is required.
Consumer: the source-density limit realization, for
`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol` and `bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ContinuumRow ContinuumNormalReduction TransportSymbol TransportKernel

variable {n N : ℕ}

/-- Insert the actual spatial density weight into the normal field, retaining
all phase, cutoff, chart and measure data (`bg-Nsigma`, `bg-T`). -/
def weightNormal (d : CarrierData n N) (w : Euclidean n × CarrierParameter → ℝ) :
    CarrierData n N :=
  {d with normalField := fun x z ↦ w (x, z) • d.normalField x z}

/-- Literal primitive coefficients of the weighted carrier
(`bg-full-complex-amplitude`). -/
theorem coefficients_weightNormal (d : CarrierData n N)
    (w : Euclidean n × CarrierParameter → ℝ) (measurement : Euclidean n → ℝ) :
    coefficientsOfCarrier (weightNormal d w) measurement =
      {coefficientsOfCarrier d measurement with
        normal := fun p ↦ w p • (coefficientsOfCarrier d measurement).normal p} := rfl

/-- The carrier amplitude acquires the square of the normal weight. Both
quadratures use this same amplitude (`bg-T`, `bg-real-symbol`). -/
theorem carrierAmplitude_weightNormal (d : CarrierData n N)
    (w : Euclidean n × CarrierParameter → ℝ) (x : Torus n) (z : CarrierVariable n) :
    carrierAmplitude (weightNormal d w) x z =
      w (d.chartPoint x, z.1) ^ 2 • carrierAmplitude d x z := by
  simp only [carrierAmplitude, weightNormal, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, smul_smul]
  congr 1
  ring

/-- Literal kernel multiplication, with no change of carrier measure
(`bg-T`, `bg-Nsigma`). -/
theorem carrierKernel_weightNormal (d : CarrierData n N)
    (w : Euclidean n × CarrierParameter → ℝ) (x : Torus n) (z : CarrierVariable n) :
    carrierKernel (weightNormal d w) x z =
      (w (d.chartPoint x, z.1) ^ 2 : ℂ) • carrierKernel d x z := by
  classical
  by_cases hx : x ∈ d.outputChart
  · simp only [carrierKernel, weightNormal, indicator_of_mem hx]
    change Complex.exp _ • euclideanComplexInclusion
      (carrierAmplitude (weightNormal d w) x z) = _
    rw [carrierAmplitude_weightNormal, map_smul]
    rw [smul_comm]
    simp only [← Complex.ofReal_pow, Complex.coe_smul]
    rfl
  · simp [carrierKernel, weightNormal, hx]

/-- The two-position density retains both squared weights, separately
evaluated at its two physical positions (`bg-full-complex-amplitude`). -/
theorem normalDensityEntry_weightNormal (d : CarrierData n N)
    (w : Euclidean n × CarrierParameter → ℝ) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (z : CarrierVariable n) (i j : Fin n) :
    normalDensityEntry (weightNormal d w) m x y z i j =
      (w (d.chartPoint x, z.1) ^ 2 * w (d.chartPoint y, z.1) ^ 2) *
        normalDensityEntry d m x y z i j := by
  simp only [normalDensityEntry, weightNormal, reducedCovector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- A measurable representative need agree with the density weight only on
the actual measurement/angular support. This gives the same literal normal
entry without global assumptions on the density extension (`bg-Nsigma`). -/
theorem normalDensityEntry_weightNormal_congr (d : CarrierData n N)
    (w w' : Euclidean n × CarrierParameter → ℝ)
    (heq : ∀ x z η, d.measurementCutoff x ≠ 0 → d.angularCutoff z η ≠ 0 →
      w (d.chartPoint x, z) = w' (d.chartPoint x, z))
    (m : CarrierVariable n → ℝ) (x y : Torus n) (z : CarrierVariable n) (i j : Fin n) :
    normalDensityEntry (weightNormal d w) m x y z i j =
      normalDensityEntry (weightNormal d w') m x y z i j := by
  by_cases hx : d.measurementCutoff x = 0
  · simp [normalDensityEntry, weightNormal, hx]
  by_cases hy : d.measurementCutoff y = 0
  · simp [normalDensityEntry, weightNormal, hy]
  by_cases hz : d.angularCutoff z.1 (‖z.2‖⁻¹ • z.2) = 0
  · simp [normalDensityEntry, weightNormal, hz]
  simp only [normalDensityEntry_weightNormal, heq x z.1 _ hx hz, heq y z.1 _ hy hz]

/-- Reuse the SAME substitution chart after weighting the normal. Only the
elementary density measurability changes; the inverse, derivative, phase and
support are retained (`bg-full-complex-amplitude`, `bg-frame`). -/
def weightedChartInputs {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {x y : Torus n} (c : ChartInputs d m x y)
    (w w' : Euclidean n × CarrierParameter → ℝ) (hw' : Measurable w')
    (heq : ∀ x z η, d.measurementCutoff x ≠ 0 → d.angularCutoff z η ≠ 0 →
      w (d.chartPoint x, z) = w' (d.chartPoint x, z)) :
    ChartInputs (weightNormal d w) m x y :=
  {c with
    support := by
      intro v t ht i j
      rw [normalDensityEntry_weightNormal, c.support v t ht i j, mul_zero]
    density_measurable := by
      intro i j
      have hx : Measurable (fun z : CarrierVariable n ↦ w' (d.chartPoint x, z.1)) :=
        hw'.comp (measurable_const.prodMk measurable_fst)
      have hy : Measurable (fun z : CarrierVariable n ↦ w' (d.chartPoint y, z.1)) :=
        hw'.comp (measurable_const.prodMk measurable_fst)
      have h := ((hx.pow_const 2).mul (hy.pow_const 2)).mul (c.density_measurable i j)
      convert h using 1
      funext z
      exact (normalDensityEntry_weightNormal_congr d w w' heq m x y z i j).trans
        (normalDensityEntry_weightNormal d w' m x y z i j) }

/-- Reuse the exact symbol geometry after weighting the normal. The only
new smoothness obligations are its two primitive normal evaluations; the
zero-density coefficient producer discharges these (`bg-Nsigma`,
`bg-full-complex-amplitude`). -/
def weightedSymbolInputs {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {x y : Torus n} {c : ChartInputs d m x y} (s : SymbolInputs c)
    (w w' : Euclidean n × CarrierParameter → ℝ) (hw' : Measurable w')
    (heq : ∀ x z η, d.measurementCutoff x ≠ 0 → d.angularCutoff z η ≠ 0 →
      w (d.chartPoint x, z) = w' (d.chartPoint x, z))
    (hleft : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦
      w (p.1.1, p.2.1) • d.normalField p.1.1 p.2.1) s.inputDomain)
    (hright : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦
      w (p.1.2, p.2.1) • d.normalField p.1.2 p.2.1) s.inputDomain) :
    SymbolInputs (weightedChartInputs c w w' hw' heq) :=
  {s with regularity := {s.regularity with leftNormal := hleft, rightNormal := hright}}

/-- Localize only the primitive symbol domain to the original physical
density region. At the two supplied output points this leaves the conic
substitution unchanged. The original support, inverse and Jacobian are
retained (`bg-full-complex-amplitude`, `bg-Nsigma`). -/
def weightedLocalSymbolInputs {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {x y : Torus n} {c : ChartInputs d m x y} (s : SymbolInputs c)
    (w w' : Euclidean n × CarrierParameter → ℝ) (hw' : Measurable w')
    (heq : ∀ x z η, d.measurementCutoff x ≠ 0 → d.angularCutoff z η ≠ 0 →
      w (d.chartPoint x, z) = w' (d.chartPoint x, z))
    {E : Set (Euclidean n)} (hE : IsOpen E)
    (hx : d.chartPoint x ∈ E) (hy : d.chartPoint y ∈ E)
    {U : Set (InputVariables n)} (hU : U ⊆ s.inputDomain)
    (hmap : MapsTo (inverseCoordinates s.inverse)
      (s.domain ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E}) U)
    (hleft : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦
      w (p.1.1, p.2.1) • d.normalField p.1.1 p.2.1) U)
    (hright : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦
      w (p.1.2, p.2.1) • d.normalField p.1.2 p.2.1) U) :
    SymbolInputs (weightedChartInputs c w w' hw' heq) :=
  {s with
    domain := s.domain ∩ {p | p.1.1 ∈ E ∧ p.1.2.1 ∈ E}
    inputDomain := U
    domain_open := s.domain_open.inter
      ((hE.preimage continuous_fst.fst).inter (hE.preimage continuous_fst.snd.fst))
    domain_eq := by
      intro v k
      change (((d.chartPoint x, d.chartPoint y, k), v) ∈ s.domain ∧
        d.chartPoint x ∈ E ∧ d.chartPoint y ∈ E) ↔ k ∈ c.phaseMap v '' c.domain v
      simpa only [hx, hy, and_self, and_true] using s.domain_eq v k
    regularity := {
      leftMeasurement := s.regularity.leftMeasurement.mono hU
      rightMeasurement := s.regularity.rightMeasurement.mono hU
      angular := s.regularity.angular
      high := s.regularity.high
      leftNormal := hleft
      rightNormal := hright
      leftReduced := fun i ↦ (s.regularity.leftReduced i).mono hU
      rightReduced := fun i ↦ (s.regularity.rightReduced i).mono hU
      jacobian := s.regularity.jacobian.mono hU
      jacobian_ne_zero := fun p hp ↦ s.regularity.jacobian_ne_zero p (hU hp)
      covector_ne_zero := fun p hp ↦ s.regularity.covector_ne_zero p (hU hp) }
    inverse_smooth := s.inverse_smooth.mono inter_subset_left
    inverse_maps := hmap
    right_inverse := fun p hp ↦ s.right_inverse p hp.1
    primitive_support := fun p hp ↦ s.primitive_support p (hU hp)
    slice_buffer := fun k v hp ↦ ⟨s.slice_buffer k v hp, hx, hy⟩ }

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
