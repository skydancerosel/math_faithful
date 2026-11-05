# Docstring errata (2026-09-18)

While writing *Milnor, proof by proof* (`Exposition/ProofByProof.md`), each writer compared the
docstrings of the Lean files with the formal statements they describe. The discrepancies that
concerned `Exposition/Verification.md` were fixed there on 2026-09-18. The ones below are in the
Lean sources and are still open. None of them affects a proof: every item is a comment, a file
name, or a hypothesis that is stated but not needed.

## Theorem letters

The project uses older letters than Milnor. Milnor's letters are:

- §4: one unlettered Theorem (independence of the regular value, and homotopy invariance).
- §5: Theorem A is independence of the regular value (`degAt_eq_of_isRegularValue`). Theorem B is
  homotopy invariance (`degAt_eq_of_homotopy`, `deg_eq_of_homotopy`).
- §7: Lemma 1 is the basis lemma. Theorem A is independence of the regular value and the basis
  (`framedCobordant_of_regularValues`). Lemma 3 is covered by `framedCobordant_of_homotopic`.
  Theorem B is "homotopic iff framed cobordant" (`framedCobordant_of_homotopic` and the converse
  in `ThmAconv.lean`). Theorem C is "every framed submanifold is a Pontryagin manifold"
  (`exists_map_of_framedSub`). The Product Neighborhood Theorem is unlettered.

Stale letters appear in:

- `Chapter5/HomotopyInv.lean` (module docstring, `degAt_eq_of_homotopy`,
  `degAt_eq_of_homotopy_of_isRegularValue`, `deg_eq_of_homotopy`), `Chapter5/Degree.lean`
  (module docstring, `degAt_eq_of_isRegularValue`), `Chapter5/HairyBall.lean` (module docstring).
- `Chapter7/Lemma2.lean` ("Lemma 2" for Milnor's Theorem A), `Chapter7/Cobordism.lean`
  ("Lemma 3"), `Chapter7/ThmA.lean` ("Theorem A, first half"), `Chapter7/Hopf.lean` ("Theorem A
  of §5", "Theorem A of §7"), `Chapter7/Stereo.lean` (uses Milnor's letters, unlike its
  neighbours).
- File names `ThmA.lean`, `ThmAconv.lean`, `ThmB.lean`, `ThmBsupp.lean`.
- `Chapter8/CohomotopyProduct.lean`, `Chapter8/CohomotopyGroup.lean`, and the reflexivity
  docstring in `Chapter8/FramedOps.lean`.

## Docstrings that say more or less than the code

Chapters 1 to 4

- `Chapter2/WithBoundary.lean`, `isHalfSliceSubmanifold_levelSet`: says "0 a regular value of g".
  There is no such hypothesis; the theorem is stronger. The same phrase is in the module
  docstring of `Chapter5/LemmaOne.lean`, which also says "X = {g ≥ 0} compact"; only
  {f = y, g ≥ 0} compact is assumed.
- `Chapter2/Brouwer.lean`, module docstring: "f⁻¹(y) is a compact 1-manifold with boundary"
  should be f⁻¹(y) ∩ D.
- `Chapter1/RiemannSphere.lean`: asserts S² ≅ ℂ ∪ {∞} as a diffeomorphism. This is not
  formalized.
- `Chapter2/LevelSet.lean` imports `Chapter2/Brown.lean`, and through it Sard, without using it.
- `Chapter3/Step1.lean`, module docstring: says "iff"; the code proves one direction.
- `Chapter4/Degree.lean`, module docstring: states Theorem B without the Hausdorff and second
  countable hypotheses.
- `Chapter4/Homogeneity.lean`, module docstring (lines 9–10) and `isotopic_of_preconnected`
  (lines 258–260): mention only the ends of the isotopy. `Isotopic` requires every stage to be a
  diffeomorphism, so the full isotopy is proved.

Chapter 5 and 6

- `Chapter5/Orient.lean`: the docstring of `signAt_prodReal` is garbled.
- `Chapter6/Invariance1.lean`, module docstring: lists `signAt_aff_sphere`, which does not exist.
  The lemma is `Sphere.signAt_ψaff`.
- `Chapter6/SignLemmas.lean`, module docstring: the last bullet describes `signAt_levelOrientM_map`,
  which is in `LevelMap.lean`.
- `Chapter6/LevelSignM.lean`: `signAt_levelOrientM_eq'` says "for a₀" (the code uses oM);
  `degAt_levelOrientM_eq_zero` says X ⊆ E (it is X ⊆ M). Both were copied from `LevelSign.lean`.
- `Chapter6/Region.lean`, `sum_indexAt_eq_deg`, and `Chapter6/Hopf.lean`, `hopf_lemma`: say the
  zeros are "exactly" the zᵢ; `hzero` needs only inclusion.

Chapter 7

- `Chapter7/Framed.lean`, module docstring (lines 6, 13–15): says M compact and describes a
  cobordism as a compact manifold with boundary in M × [0, 1]. The code requires neither M
  compact nor a boundary: S ⊆ M × ℝ is boundaryless, with ends N₀ × (−∞, ε) and
  N₁ × (1 − ε, ∞). The `FramedCob` docstring claims S ∩ (M × [0, 1]) is a compact manifold
  with boundary "(Chapter 2, Lemma 4)"; this is never proved or used.
- `Chapter7/Equiv.lean`: says "equivalence relation"; Chapter 7 proves symmetry and transitivity,
  and reflexivity only for 0-manifolds (`FramedCobordant.refl'`, `Reach.lean`). General
  reflexivity is `framedCobordant_refl` in `Chapter8/FramedOps.lean`.
- `Chapter7/ThmBsupp.lean`, `exists_map_of_framedSub_subset`: the docstring was copied from
  `FramedSub.ext'` and describes that lemma instead.
- `Chapter7/Deform.lean`, header: τ should be ρ(τ); "throughout" should be "at time 1".
- `Chapter7/Clamp.lean`, header: says "finite-dimensional", which is not assumed.
- `Chapter7/StdMap.lean`: "stereographic-type" should be inverse central (gnomonic) projection.
- `Chapter7/ProdNbhd.lean`: "dim X = n + p" is not a hypothesis.

Chapter 8

- `Chapter8/HopfMap.lean`, module docstring: says `hopfI`, `hopfJ`, `hopfK` are "used to compute
  the Hopf invariant". They are not used outside `HopfMap.lean`.
- `Chapter8/HopfComp.lean`, `degAt_comp_eq_finsum`: says "all of the same dimension n"; only M
  and N are fixed.
- `Chapter8/Retraction.lean`, module docstring: states r(x + v) = x at radius `tubε`. `tubr_spec`
  proves it only for small multiples; the full identity is `normalRetraction_eq` in
  `NormalBundle.lean`, for ‖v‖ < `normalε`.
- `Chapter8/DegComp.lean`: says "N, P connected"; the code assumes preconnected.
- `Chapter8/OrientFrame.lean`, module docstring: states `sphOrStd = ± sphOr` and the antipodal
  degree without n > 0.
- `Chapter8/Transversality.lean`, `exists_local_inter`: "submersion with zero set" holds only at
  points of S ∩ S′ in U.
- `Chapter8/CohomotopyGroup.lean`, `dense_compl_image` and the file header: say n < p and "dense
  open"; the code assumes n + 1 < p and proves density only.

Appendix, `Appendix/OneManifold.lean`

- `arcOfChart`: mentions "a point y in its source"; there is no such parameter.
- `Arc`: says "an interval of ℝ"; the definition requires a bounded interval with more than one
  point.

## Page references that are off (added 2026-09-28)

Found while writing the comparison edition, each checked against the book. Page numbers are the
book's own.

- `Chapter2/Brown.lean`: the module header says "pp. 10–11" and a docstring says "Milnor p. 11".
  Sard's theorem for the Euclidean case, its density corollary and the Brown corollary are all on
  p. 10.
- `Chapter2/LevelSet.lean`: cites p. 12 for Milnor's Lemma 2. The lemma is stated at the foot of
  p. 11; p. 12 carries only its proof.
- `Chapter4/Degree.lean`: cites p. 21 for `even_ncard_add_ncard_of_isRegularValue`,
  `degMod2_eq_of_homotopy` and `surjective_of_degMod2_ne_zero`. The Theorem of §4 and its
  surroundings are on p. 24; p. 21 is the Homotopy Lemma, which `Chapter4/Homotopy.lean` cites
  correctly.
- `Chapter5/Degree.lean` and `Chapter5/HomotopyInv.lean`: cite p. 28 for Theorem A and for
  Milnor's Lemma 2. Theorems A and B are on p. 27, Lemma 1 on p. 28, Lemma 2 on p. 29.
  `surjective_of_deg_ne_zero` also cites p. 28, but §5 has no such statement; the nearest remark
  is on p. 29.
- `Chapter6/Tubular3.lean`: cites "§8, the ε-neighborhood theorem, p. 53". It is Problems 11 and
  12 of §8, on p. 52.
- `Chapter7/Cancel.lean`, `Hopf.lean`, `Main.lean`, `Move.lean`, `Reach.lean`: all cite "§7,
  p. 51". Page 51 is the first page of §8; the Hopf theorem and the clause these files carry out
  are on p. 50.

## Added 2026-09-28, from the classification of one-manifolds

- `Appendix/Smooth/Affine.lean`, module docstring: refers twice to `milnor_lemma_one`; the theorem
  is `milnor_appendix_lemma_one`.

## Hypotheses that are stated but not needed

Harmless, listed for a later cleanup.

- `step1_local`: the nontriviality hypothesis.
- `cylinder_transversality`: regularity of y for the homotopy F; only the end map is used.
- `exists_mfd_eq_zero_of_isRegularPoint_level`: `hf`.
- `lemmaOne_ambient'` and `exists_isotopy_signAt_eq_one`: N Hausdorff.
- `degAt_phiR_eq_linkingNumberRot`: `_hR`. `isRegularValue_phiR`: `_hd`, `_hdisj`, `_hR`, `_hRy`,
  `_hRz`. `linkPre_comp_posDiffeo`: `hg'`, `hy'`, `hf'`, `hz'`. `linkPre_eq_of_norm_lt`: `hyz`
  follows from `hclose`.
- `exists_admissible_rotation`: a, b ≥ 1 (only a, b < k + 1 is needed).
- `framedCobordant_of_homotopic`: smoothness of the end maps. `framedCobordant_of_homotopy`: z
  regular for f and g. `framedCobordant_comp`: `hbij`, `hsign`. `framedCobordant_arc`: `hz`.
- `signAt_ofFrame`: `_hf`. `BoundaryCompatible` is assumed for every chart; only `chartAt` is
  used.
- `inter_eq_empty_of_transverse`: n + p = m and n′ + p′ = m.
- `cohomotopyGroup`: p ≥ 1 is implied by m + 2 ≤ 2p.
- `exists_contDiff_approx_of_isCompact`: finite dimension.

Unused lemmas: `vanishSet_one_subset_critSet`, `signAt_pairMap_mul`, `degAt_comp_diffeo`,
`degAt_levelOrient_eq_zero`, `degAt_levelOrientM_eq_zero`, `IsRegularValue.comp_subtype_val_opens`,
`indexN_eq`, `count_of_move`, `card_unmatched_pos_iff`, `hull_eq_of_sSup_eq`, `hull_eq_of_sInf_eq`,
`interior_eq_Ioo_of_ordConnected`, `overlap_neg_right`, `arcOfChart_source`, `arcOfChart_target`,
`arcOfChart_toFun`, `Arc.source_nonempty`, `subsingleton_of_finrank_eq_zero`.
