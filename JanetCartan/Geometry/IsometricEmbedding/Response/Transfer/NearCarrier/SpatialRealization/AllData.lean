module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.CompactTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.VectorDensity

/-!
# Spatial transfer for all first-derivative L² data

For `app:ch_response:eq:direct-envelope-profile`, bounded operators realizing
the SAME literal compact-test kernels satisfy the forward and reverse weak
derivative identities on every datum with first L² derivatives. Smooth compact
amplitudes discharge all analytic integration-by-parts inputs. The low L²
construction supplies only the displayed almost-everywhere kernel agreements;
no derivative identity, Sobolev membership, or graph estimate is assumed.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem distribution_pairing_of_ae {u : H} {f : E → V}
    (h : u =ᵐ[volume] f) (φ : 𝓢(E, ℂ)) :
    (u : 𝓢'(E, V)) φ = ∫ x, φ x • f x := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Passing proved literal compact-test pairings through bounded realizations
and the proved simultaneous density theorem. This limit lemma is used below
with the actual forward and reverse integration-by-parts theorems, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem graph_transfer_of_compactTest_pairings
    (K R : graphTestSpace n r → E → V) (D : Fin n → graphTestSpace n r → E → V)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H) (i : Fin n)
    (hT : ∀ t, T (graphTestToLp t) =ᵐ[volume] K t)
    (hU : ∀ t, U (graphTestToLp t) =ᵐ[volume] R t)
    (hW : ∀ j t, W j (graphTestToLp t) =ᵐ[volume] D j t)
    (hpair : ∀ t (φ : 𝓢(E, ℂ)),
      (∫ x, partialDeriv φ x i • K t x) =
        -((∫ x, φ x • R t x) +
          ∑ j, ∫ x, φ x • D j (graphTestPartialDeriv j t) x))
    (u : H) (du : Fin n → H)
    (hdu : ∀ j, lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (u : 𝓢'(E, V)) =
      (du j : 𝓢'(E, V))) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (T u : 𝓢'(E, V)) =
      (U u + ∑ j, W j (du j) : H) := by
  let J := Lp.toTemperedDistributionCLM V (volume : Measure E) 2
  have ht (t : graphTestSpace n r) :
      lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (T (graphTestToLp t) : 𝓢'(E, V)) =
        (U (graphTestToLp t) + ∑ j, W j (graphTestToLp (graphTestPartialDeriv j t)) : H) := by
    ext φ : 1
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
    change -((T (graphTestToLp t) : 𝓢'(E, V)) (lineDerivOp _ φ)) =
      J (U (graphTestToLp t) + ∑ j, W j (graphTestToLp (graphTestPartialDeriv j t))) φ
    rw [map_add, map_sum]
    simp only [add_apply, sum_apply]
    change -((T (graphTestToLp t) : 𝓢'(E, V)) (lineDerivOp _ φ)) =
      (U (graphTestToLp t) : 𝓢'(E, V)) φ +
        ∑ j, (W j (graphTestToLp (graphTestPartialDeriv j t)) : 𝓢'(E, V)) φ
    rw [distribution_pairing_of_ae (hT t), distribution_pairing_of_ae (hU t)]
    simp_rw [distribution_pairing_of_ae (hW _ _)]
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      neg_eq_iff_eq_neg.mpr (hpair t φ)
  obtain ⟨t, hu, hd⟩ := exists_graphTest_coordinateDerivatives_tendsto u du hdu
  let L := (lineDerivOpCLM ℂ (𝓢'(E, V)) (EuclideanSpace.single i (1 : ℝ))).comp J
  have hl := (L.continuous.tendsto (T u)).comp ((T.continuous.tendsto u).comp hu)
  have hr := (J.continuous.tendsto (U u + ∑ j, W j (du j))).comp
    (((U.continuous.tendsto u).comp hu).add
      (tendsto_finsetSum Finset.univ (fun j _ ↦ (W j).continuous.tendsto (du j) |>.comp (hd j))))
  exact tendsto_nhds_unique hl (hr.congr (fun k ↦ (ht (t k)).symm))

/-- Forward all-data spatial transfer for the actual full compact amplitude.
The remainder is `∂x A + Σ B ∂y A`; all original weights and selectors remain
inside `A`. Bounded realizations of these exact kernels are the independent
low-calculus input. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardGraph_allData_derivative
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : E → E → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B : E → E → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hB : ∀ j, ContDiff ℝ ∞ (fun p : E × E ↦ B p.1 p.2 i j))
    (hgrad : ∀ x δ, partialDeriv (fun z ↦ Φ z δ) x i = ∑ j, B x δ i j * δ j)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H)
    (hT : ∀ t : graphTestSpace n r, T (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ A (fun y ↦ (t.val y).ofLp) x))
    (hU : ∀ t : graphTestSpace n r, U (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ (forwardRemainderAmplitude B A i)
        (fun y ↦ (t.val y).ofLp) x))
    (hW : ∀ j (t : graphTestSpace n r), W j (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ (forwardDatumAmplitude B A i j)
        (fun y ↦ (t.val y).ofLp) x))
    (u : H) (du : Fin n → H)
    (hdu : ∀ j, lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (u : 𝓢'(E, V)) =
      (du j : 𝓢'(E, V))) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (T u : 𝓢'(E, V)) =
      (U u + ∑ j, W j (du j) : H) :=
  graph_transfer_of_compactTest_pairings _ _ _ T U W i hT hU hW
    (forwardGraph_compactTest_weak_pairing hX hY hF hΦ hA i hB hgrad) u du hdu

/-- Reverse all-data spatial transfer for the actual full compact amplitude.
The remainder is `∂y A + Σ ∂x(C A)`, retaining the derivatives of the inverse
and, when supplied as `A`, the entire weight `j_S U⁻¹`. The inverse and phase
identities are required only on the full amplitude's source support.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseGraph_allData_derivative
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : E} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B C : E → E → Matrix (Fin n) (Fin n) ℝ} (i : Fin n)
    (hC : ∀ j, ContDiff ℝ ∞ (fun p : E × E ↦ C p.1 p.2 i j))
    (hinv : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), C x δ * B x δ = 1)
    (hgrad : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H)
    (hT : ∀ t : graphTestSpace n r, T (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ A
        (fun x ↦ (t.val x).ofLp) y))
    (hU : ∀ t : graphTestSpace n r, U (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (ReverseDerivative.remainderAmplitude C A i) (fun x ↦ (t.val x).ofLp) y))
    (hW : ∀ j (t : graphTestSpace n r), W j (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ
        (ReverseDerivative.datumAmplitude C A i j) (fun x ↦ (t.val x).ofLp) y))
    (u : H) (du : Fin n → H)
    (hdu : ∀ j, lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (u : 𝓢'(E, V)) =
      (du j : 𝓢'(E, V))) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (T u : 𝓢'(E, V)) =
      (U u + ∑ j, W j (du j) : H) :=
  graph_transfer_of_compactTest_pairings _ _ _ T U W i hT hU hW
    (reverseGraph_compactTest_weak_pairing hX hY hF hΦ hA i hC hinv hgrad) u du hdu

end JanetCartan.ResponseTransfer.SpatialRealization
