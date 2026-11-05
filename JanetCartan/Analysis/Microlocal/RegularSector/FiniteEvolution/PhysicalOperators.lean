module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.LocalOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff

/-!
# Actual selected-chart evolutions with the physical Fourier cutoff

Instantiate `PhysicalCutoff.exists_physical_local_solver_and_residual` with
the original coefficient producer on the same selected chart. The right
multiplier is the pullback of the original physical partition, including
its doubled radial threshold. Source multiplication remains before Fourier
multiplication. Every phase and amplitude hypothesis is discharged here.
The algebraic and endpoint PDO terms remain separate assembly obligations.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.AmplitudeBounds
open Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LocalSobolev
open Characteristic.RetardedLocalization
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
variable {Ω : Set (Euclidean (d+1))} {x ξ : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)}

/-- Same constructed chart and operators with the literal pullback of the
physical right multiplier, including its radial shoulder. This is an output
of the constructor below, not an additional analytic assumption
(`app:ch_regular_base:eq:energy-complete-residual`). -/
abbrev SelectedChartPhysicalEvolution
    (lc : LocalChart Ω x RQ Aref ξ M) (mask : E → ℝ)
    (Ksource Usource : Set E) : Prop :=
  SelectedChartEvolutionFor lc
    (fun L ζ ↦ (dilatedConicMask mask (2 * L) (physicalCoordinates lc.index ζ) : ℂ))
    Ksource Usource

/-- Construct the actual solver evolution and the literal `PW₁` evolution
with the exact physical right multiplier from one selected chart. Only original coefficient smoothness, value range
and one fixed finite coefficient norm remain as varying inputs. In particular
no root, flow, amplitude, phase or operator bound is assumed. The full `B`
term, same supported phase, signed estimates and reversed adjoint triangles
are retained (`retarded-kernel`, `energy-complete-residual`). -/
theorem exists_selected_chart_physical_operators
    (lc : LocalChart Ω x RQ Aref ξ M)
    (hρb : lc.bufferRadius ≤ lc.targetRadius)
    (hsrcρ : lc.maskRadius ≤ lc.bufferRadius/4) (hM : 0 ≤ M)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport mask ⊆ lc.angularNeighborhood)
    {Ksource Usource : Set E} (hKs : IsCompact Ksource)
    (hUs : IsOpen Usource) (hKUs : Ksource ⊆ Usource) :
    SelectedChartPhysicalEvolution lc mask Ksource Usource := by
  unfold SelectedChartPhysicalEvolution SelectedChartEvolutionFor SelectedChartEvolutionAt
  dsimp only
  let e := coordinateSplit lc.index
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  obtain ⟨aperture, hAp, hcar⟩ :=
    exists_chart_temporal_aperture lc hρb hsrcρ mask hcarrier
  obtain ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, hconstruct⟩ :=
    PhysicalCutoff.exists_physical_local_solver_and_residual lc.radialSection z lc.targetRadius_pos
      lc.bufferRadius_pos lc.maskRadius_pos hρb hsrcρ hAp lc.timeMask lc.timeMask_plateau
      hKs hUs hKUs lc.index mask hm hcar lc.phaseCost lc.phaseCost_pos M hM
  refine ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho, hs, hoc, hsc, hop, hsp, hos, hss, hκout, ?_⟩
  intro L' hLL
  obtain ⟨hplateau, ra, hra, rb, hrab, hoperators⟩ := hconstruct L' hLL
  obtain ⟨D, hD, hevolution⟩ := lc.evolution angular hang hangpos ra hra rb
  obtain ⟨A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, hop⟩ := hoperators D hD
  obtain ⟨H1, hH1, hlocal⟩ := exists_retained_local_residual_H1_constant d (d+1)
  refine ⟨hplateau, ra, hra, rb, hrab, D, hD, A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd,
    H1, hH1, ?_⟩
  intro Q hQ hQrange hQlow
  have hQret : cNorm (closedBall x RQ) (retardedCoefficientOrder d) Q ≤ M :=
    (cNorm_mono_order (sectorLowOrder_bounds d).1).trans hQlow
  have hQ10 : cNorm (closedBall x RQ) 10 Q ≤ M :=
    (cNorm_mono_order (retardedCoefficientOrder_bounds (d := d) (Or.inl rfl)).1).trans hQret
  obtain ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, hevoB⟩ :=
    hevolution Q hQ hQrange hQ10
  refine ⟨Φ, C, hh, hhom, hUL, hgap, hC, hsource, hinvsmooth, hbuffer, hphase,
    hdiff, hinv, hstate, hdiag, hnear, hphaseBudget, houter, hflow, ?_⟩
  intro B hB hBlow
  have hBret : cNorm (closedBall x RQ) (retardedCoefficientOrder d) B ≤ M :=
    (cNorm_mono_order (sectorLowOrder_bounds d).1).trans hBlow
  have hB9 : cNorm (closedBall x RQ) 9 B ≤ M :=
    (cNorm_mono_order (retardedCoefficientOrder_bounds (d := d) (Or.inl rfl)).2.1).trans hBret
  obtain ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead, hphysical, hW⟩ := hevoB B hB hB9
  have hoperators := hop lc.row lc.col lc.sourceMask (closedBall x RQ) Q B hQret hBret
    _ Φ C hbuffer hphase hdiff hnear hphaseBudget (fun p hp ↦ (hinv p hp).2.1)
    (fun j ↦ ⟨(hW j).2.2.2.2.1, (hW j).2.2.2.2.2.1, (hW j).2.2.2.2.2.2.2.2⟩)
    hphysical G hG hGres
  obtain ⟨Solver, Residual, hSolver, hResidual, hPW⟩ := hoperators
  refine ⟨G, hGs, hGdiag, hG, hGres, hcancel, hlead,
    ⟨Solver, Residual, hSolver, hResidual, hPW, ?_⟩, hphysical, hW⟩
  intro U Vout hU hVout
  obtain ⟨hf, hg⟩ := hlocal (closedBall x RQ) Q B _ _ _ _ _ _ _ hs _ _ Residual
    hResidual U Vout hU hVout
  have hprofile := retarded_gain_one_profile_le (closedBall x RQ) Q B hQlow hBlow
  have hconstant := mul_le_mul_of_nonneg_left hprofile
    (mul_pos hH1 (hBnd 1)).le
  exact ⟨fun f ↦ ⟨(hf f).1, (hf f).2.trans
    (mul_le_mul_of_nonneg_right hconstant (norm_nonneg f))⟩,
    fun g ↦ ⟨(hg g).1, (hg g).2.trans
    (mul_le_mul_of_nonneg_right hconstant (norm_nonneg g))⟩⟩

end JanetCartan.RegularSector.FiniteEvolution
