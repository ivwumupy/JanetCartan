module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Masks
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SourceGeometry
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.InitializedApplication
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualCollar

/-!
# Even nested proof masks for selected physical relations

`SelectedEvenProofMasks.exists_selectedSector_even_nested_proof_masks`
constructs even real physical masks on the SAME supplied `ActualMaskFamily`,
initialized reference, current-map lift and extended pencil. The constants,
radial proof cover, collar and all-order grades precede the varying current
map and history. The masks retain the original source plateau and buffer,
complete signed relation, full diagonal, compact annulus, canonical pullbacks,
source recuts, conic extensions and positive interior/boundary phase gaps.
`selectedSectorNestedMaskConclusion_of_even` recovers every field of the
existing selected-sector conclusion without selecting independent witnesses.

For the literal direct residual, first use
`exists_selectedSector_even_nested_proof_masks_with_prior_annulus` to fix
the common physical annulus `[a,b]`. With these endpoints,
`exists_selected_direct_residual_phase_carriers` gives `tlo, thi > 0`.
Pass `fun j ↦ ra j / thi` and `fun j ↦ ra j / tlo` to the initialized
phase-band selector. It constructs the radial proof cover and the masks
once, before coefficients and histories vary.

`exists_selected_even_retained_phase_gaps` proves lower bounds on the
supported carrier for both the original conic phase and its selected
`Gext`, before any auxiliary phase or derivative profile is supplied.
`exists_selected_even_residual_collar_domains` then gives the open collar
domains and quantitative bounds of
`ResidualLocalization.exists_directResidual_integral_fourier_bound_of_primitive_grades`
on `selectedRetainedResidualCarrier`. Use `le_rfl` for both scalar band
comparisons. The input and output proof symbols are canonical pullbacks of
the consecutive masks of `hEven.choose_spec.choose`. Their parity, source
recuts and derivative bounds are all available from `hEven.choose_spec.choose_spec`.
The closure and dilation proof retains the same elapsed times, bases and
three covectors in every differentiated kernel. The original source-time
buffer bounds the closed support by the chart slab. Beyond six physical
radii the temporal graph covector derivative supplies the gap directly.

The proof uses an explicitly reflected relation solely to choose the masks.
Its protected closed shoulders follow from the dimension-dependent parity of
the SAME normalized determinant and signed Hamilton curves with the SAME
absolute speed bound. No symmetry of the arbitrary finite chart relation is
assumed and no actual operator, source mask or inverse is replaced.

The initial source must be compatible with its reflection inside the original
prescribed buffer. `SourceGeometry` proves necessity and derives compatibility
from an even frequency cutoff's literal closed support. The initialized
producer supplies symmetry of the retained source angular neighborhood. The
`both-localized-response` parent owns concrete source/cutoff admission and the
final same-solver factor application; arbitrary legacy source compacts and
buffers do not imply compatibility. No source mask or inverse is replaced to
obtain it. This leaf proves the relative mask construction, not an unconditional
residual estimate or Theorem 1.1.

Consumers: `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`hieven`, `hoeven`) and `SelectedLocalization.real_pairedCompleteError_local_factor_bound`.
Sources: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/
