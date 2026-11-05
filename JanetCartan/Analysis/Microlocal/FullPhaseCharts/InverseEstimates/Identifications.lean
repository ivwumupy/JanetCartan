module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.PhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily

/-!
# Identification with the constructed full and transverse inverse families

These identities connect the literal maps of `InverseFamily` with the
primitive-phase estimate in `PhaseBounds`. They retain physical and normalized
data coordinates exactly, as required in `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
namespace JanetCartan.FullPhaseCharts.InverseEstimates
variable {P E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full map constructed by `InverseFamily` is literally the quotient chart
estimated in `PhaseBounds` (`app:ch_seed:prop:seed-phase-charts`). The phase is
independent of the adjoined spectator/data coordinates. -/
theorem carrierQuotientChart_eq_fullChartFamily
    (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (q : (ℝ × (P × WithLp 2 (ℝ × E) × WithLp 2 (ℝ × E))) × (ℝ × E)) :
    carrierQuotientChart (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap
      (fun p ξ ↦ S (p.2, ξ)) (fun p : P × (ℝ × E) ↦ ζ (p.1, p.2.1))
      (fun p : P × (ℝ × E) ↦ p.2.2) q = fullChartFamily S ζ q.1 q.2 := by
  rfl

/-- The transverse map uses the same estimate with time and `z₁` retained
among the parameters. Only the coordinate order changes; the physical segment
and normalized eta derivative are literal
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem carrierQuotientChart_eq_transverseChartFamily
    (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (q : (ℝ × ((P × ℝ × ℝ) × E × E)) × E) :
    carrierQuotientChart (ContinuousLinearMap.id ℝ E)
      (fun p ξ ↦ S (WithLp.toLp 2 (p.1.1.2.1, p.2), ξ))
      (fun p : (P × ℝ × ℝ) × E ↦ ζ (p.1.1, p.1.2.2))
      (fun p : (P × ℝ × ℝ) × E ↦ p.2) q =
        transverseChartFamily S ζ
          (q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2, q.1.2.2.1, q.1.2.2.2) q.2 := by
  rfl

end JanetCartan.FullPhaseCharts.InverseEstimates
