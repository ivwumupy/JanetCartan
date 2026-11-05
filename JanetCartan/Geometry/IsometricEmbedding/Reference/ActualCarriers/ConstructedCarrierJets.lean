module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.Assembly

/-!
# Jet budgets for the canonical constructed carriers

The restriction and incidence pullbacks retain exactly the carrier and chart
selected in `ConstructedPhases`, as required by `app:ch_seed:prop:seed-actual-menu`,
Steps 2–3, and `app:ch_seed:eq:seed-phase-tame`.

* `exists_carrierGradient_frame_bound` gives joint order `m` from frame order `m+2`.
* `exists_projected_carrierGradient_sharp_bound` gives immersion order `m+4`.
* `exists_projected_incidence_high_budgets` supplies the literal frame, gradient,
  and testing-covector bounds consumed by
  `exists_cNorm_incidence_root_le_reserve_six`.
* `exists_incidence_low_budgets` derives fixed compact ranges and the uniform
  joint `C¹` budget from primitive frame `C⁶` closeness and the same family's
  low continuity. `incidence_fields_smooth` supplies smoothness on its fixed
  open domain.

`exists_projected_incidence_budgets` assembles these outputs directly from the
original immersion hypotheses, including every low range and smoothness input.

All geometric inputs concern fixed buffers and elementary coordinate
containments. The projected estimates retain the original immersion smoothness,
separate metric/normal gaps, low `C⁴` bound and primitive frame neighborhood.
The root construction, root-jet application and finite common constants belong
to the parent assembly. In particular `max r 2 + 4 ≤ r + 6` keeps its reserve
independent of the differentiated order.
-/
