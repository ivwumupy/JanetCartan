module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.InitializedDensityProducts
public import JanetCartan.Iteration.PhysicalSeed.NormalizedCharts
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-! Original same-cell density products with the strengthened leading continuation. -/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSeed
open ContinuumRow.NormalizedSelection
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

open PositiveReference PositiveReference.FlowConstruction
open CanonicalCarrier

/-- Add the original physical density products without changing the selected
centers, rows, domains or generic map continuation (`app:ch_background:eq:bg-Psi`). -/
theorem exists_density_products_with_generic_leading {n : ℕ} (hn : 5 ≤ n) :
    retain_physical_seed%
      (ContinuumRow.NormalizedSelection.exists_common_initializer_with_normalized_charts_and_density_products hn)
      before εframe retaining
      (∃ η : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
        (∀ i, 0 < η i) ∧ ∀ i,
        GenericLeading (T i) (K := closedBall (0 : Euclidean n) b)
          (η i) (centers i) (row i) (col i) (ρlead i) (L i) (τ i)
          (Rc i) (τc i) (Mc i) (rcomp i) (δcomp i) (σcover i)
          (Ωc i) (ρc i) (Bc i) (gc i) (Bfull i)) := by
  classical
  have initialized := exists_normalized_charts_with_generic_leading hn
  choose G₀ hG₀ b R hb hbR hR D c C hD kCenter hkCenter hkDomain
    T hposition hphysical hgeometry γ hγ hgap r hr hrb hradius
    εlead hεlead centers row col ρlead L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsourceGeometry hfullTime
    hgeometryc hworking εcarrier ρdet hcell hcarrierCover V hV hgeneric hinit using initialized
  have productResult (i) (j : centers i) :=
    exists_retained_density_product_geometry (N := embeddingDimension n) (T i) j.1.1
      (hpositive i j).2.1 (hpositive i j).2.2.2.1 (hgeometryc i j).2.1.le
      (lt_min (hcell i j).1 (lt_min (T i).physicalRadius_pos (hb.trans hbR)))
      (hgeometryc i j).2.2.2.2.2.2.2.2.1
      (hgeometryc i j).2.2.2.1 (isCompact_closedBall _ _)
      (hgeometryc i j).2.2.2.2.1 (hgeometryc i j).2.2.2.2.2.2.2.1
      (hpositive i j).2.2.2.2.2.2.2.2 (hworking i j).1
      (ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j))
      ((hcell i j).2.2.1.mono_left (Set.prod_mono
        (ball_subset_ball (min_le_left (εcarrier i j) (min (T i).physicalRadius R))) Subset.rfl))
      ((hcell i j).2.2.2.1.mono_left (Set.prod_mono
        (ball_subset_ball (min_le_left (εcarrier i j) (min (T i).physicalRadius R))) Subset.rfl))
      (hrc i j)
  choose Mproduct Rproduct hMproduct hRproduct hRproductCap hRproductTime
    hzero hflow hlabel htime hcharts using productResult
  have hRproductε (i) (j : centers i) : Rproduct i j ≤ εcarrier i j :=
    (hRproductCap i j).trans (min_le_left _ _)
  have hRproductPhysical (i) (j : centers i) : Rproduct i j ≤ (T i).physicalRadius :=
    (hRproductCap i j).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRproductU (i) (j : centers i) : ball (0 : Euclidean n) (Rproduct i j) ⊆ ball 0 R :=
    ball_subset_ball ((hRproductCap i j).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hVP (i) (j : centers i) :
      ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) ⊆
        CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * (D.patches i.1 i.2).radius / 2) := by
    intro z hz
    exact ((hcell i j).2.2.2.2.2.1
      (show ((0 : Euclidean n), z) ∈ ball 0 (εcarrier i j) ×ˢ
        ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) from
          ⟨mem_ball_self (hcell i j).1, hz⟩)).2
  have hcoverProduct (i) (z) (hz : z ∈ parameterCube (D.patches i.1 i.2).radius) :
      ∃ j : centers i, ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
        ball (0 : Euclidean n) (Rproduct i j) ×ˢ
          ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) := by
    obtain ⟨j, hj⟩ := hcarrierCover i z hz
    exact ⟨j, mem_ball_self (hRproduct i j), hj.2⟩
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, kCenter, hkCenter, hkDomain,
    T, hposition, hphysical, hgeometry, γ, hγ, hgap, r, hr, hrb, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsourceGeometry, hfullTime,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover, V, hV,
    Mproduct, Rproduct, ?_, hcoverProduct, hgeneric, hinit⟩
  intro i j
  refine ⟨hMproduct i j, hRproduct i j, hRproductε i j, hRproductPhysical i j,
    hRproductU i j, hRproductTime i j,
    Set.prod_mono (ball_subset_ball (hRproductε i j)) Subset.rfl,
    ?_, hVP i j, hflow i j, hlabel i j, htime i j, hcharts i j⟩
  intro z
  simp only [mem_prod, mem_ball_self (hRproduct i j), mem_ball_self (hcell i j).1, true_and]

end JanetCartan.PhysicalSeed
