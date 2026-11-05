# Milnor's remark at the end of §7: maps of a connected non-orientable manifold, and the degree modulo 2

*A formalization plan. Written 2026-09-28 after reading the endgame of chapter 7 against the new
files `Milnor/Chapter7/OrientTransport.lean` and `Milnor/Chapter7/Orientable.lean`.*

Milnor, p. 50, states as a theorem, without proof: **if `M` is connected but non-orientable, two
smooth maps `M → Sᵐ` are smoothly homotopic if and only if they have the same degree modulo 2**, and
gives the reason in one clause — sliding a point around an orientation-reversing loop changes the
sign of its frame, so only the parity of the number of points survives. The oriented case is
`Milnor.Framed.hopf_homotopic` (`Milnor/Chapter7/Hopf.lean`, line 31). Nothing of the mod 2 case is
formalized. `Leftovers.md` item 6 sketches the work in two parts (6a orientability, 6b the endgame,
estimate 1,200); 6a is now done up to one missing piece identified in §3.3 below, and the estimate
for 6b has to be revised upward to ≈ 2,600 for the two reasons in §3.

---

## 0. The recommendation in one paragraph

Replace the orientation-dependent sign `frameSign` in the *local* lemmas (moving a point inside a
chart ball, cancelling two points in a chart ball, adding a point) by the **chart sign**: the sign of
the determinant of the frame read in the chart of the ball. This mentions no orientation, it is what
those proofs already manipulate internally, and it makes the hypothesis `hpos` ("the chart is
orientation-preserving on the ball") disappear, since its only use is to certify that a chart
derivative is invertible — which `Milnor.bijective_mfd_extChartAt` now gives for free. Along a chain
of chart balls the chart sign is multiplied by an explicit `±1` per ball, the product of two
determinant signs of the chart at the ball's centre; this ±1 *is* the orientation transport of
`OrientTransport.lean`, read arithmetically. Then prove the **frame-flip lemma**: a framed point slid
around a loop of balls whose total sign is `-1` returns to its place with its chart sign reversed.
With the flip, every sign hypothesis in the cancellation machinery is dischargeable and the parity of
the number of points is the only invariant. Two pieces are genuinely new rather than reworkings:
the dichotomy of `Orientable.lean` must be re-proved for loops of *balls* (§3.3), and the loop must
be made to **avoid the other points of the framed 0-manifold** (§3.4), which needs
`2 ≤ m` and the fact that a connected manifold of dimension ≥ 2 minus a finite set is still
connected and still non-orientable.

---

## 1. Audit: where an orientation of `M` actually enters

Conventions. "states only" = the orientation occurs in a hypothesis or conclusion about signs, and
the proof uses nothing about it beyond `±1` arithmetic and the two lemmas
`orSign_comp`, `orSign_self_eq_sgn_det`. "proof-essential" = the orientation is used to construct
something or to run an argument. Line numbers are as of 2026-09-28.

### 1.1 Files with no orientation of `M` at all (reused verbatim)

`Framed.lean`, `Pontryagin.lean`, `PontFrame.lean`, `ThmB.lean`, `ThmBsupp.lean`, `Equiv.lean`,
`Cobordism.lean`, `CobMap.lean`, `SamePont.lean`, `Identify.lean`, `Glue.lean`, `Segment.lean`,
`Neighbour.lean`, `Chain.lean`, `MoveMap.lean`, `CancelMap.lean`, `Collapse.lean`, `Scale.lean`,
`TuplePath.lean`, `BasisPath.lean`, `GLplus.lean`, `Lemma1.lean`, `Lemma2.lean`, `Isotopy.lean`,
`Deform.lean`, `ProdNbhd*.lean`, `TubeData.lean`, `Homotopy.lean`, `ThmA.lean`, `ThmAconv.lean`.
(The occurrences of `Orientation`/`orSign` in `Compose.lean`, `Lemma2.lean`, `GLplus.lean`,
`Isotopy.lean`, `CancelMap.lean` concern orientations of `ℝᵖ` or of the sphere, never of `M`.)
In particular `smoothHomotopic_of_framedCobordant` (`ThmAconv.lean` line 109) needs orientations
only on the sphere, and `exists_map_of_framedSub_subset` (`ThmBsupp.lean` line 36) needs none.

### 1.2 `Hopf0.lean` — the definitions

| decl | line | orientation | local reformulation | cost |
|---|---|---|---|---|
| `stdOr`, `chartCoord`, `mfd_val_chartCoord` | 83–101 | none | — | — |
| `frameSign oM v x` | 106 | **the** definition: `orSign (stdOr m) (oM.or x) (basisCLM (chartCoord v))` | uses `oM` **at the single point `x` only**; so `frameSign hM oM v x = orEps oM x * selfSign hM x v` with `orEps oM x := orSign (stdOr m) (oM.or x) id ∈ {±1}` and `selfSign hM x v := sgn (det (basisCLM (chartCoord hM x (v ·))))` | bridge lemma, ≈ 15 lines |
| `count oM F` | 112 | essential (the signed invariant) | not needed for mod 2: the invariant is `F.finite_N.toFinset.card` | — |
| `frameSign_ne_zero` | 137 | states only | `selfSign_ne_zero` | ≈ 8 lines |
| `frameSign_pontryagin`, `count_pontryagin` | 167, 208 | essential (bridge to `deg`) | untouched; the mod 2 bridge is a different, much shorter lemma (§4.8) | — |
| `orSign_stdOr_basisCLM`, `basisCLM_comp_eq`, `linearIndependent_chartCoord`, `basisCLM_single_eq_id`, `At_apply_mfd_val` | 119–267 | none | — | — |

**Observation that drives everything:** `frameSign` reads the orientation at *one* point. A "local
orientation defined on a chart domain" is therefore more structure than any statement in this
chapter needs; one `±1` per point is enough, and the only thing the proofs ever compare is a product
of two such signs, i.e. a determinant sign of a *fixed* transition map.

### 1.3 `MoveAux.lean` — frames in chart coordinates

| decl | line | orientation | verdict |
|---|---|---|---|
| `chartFrameCLM` | 32 | none | keep: `dφ_{x_c}|_x ∘ basisCLM (chartCoord_x v)` is the object the local theory is about |
| `mfd_extChartAt_bijective` | 42 | states only, and **spuriously**: hypothesis `orSign (oM.or x) (oM.or x_c) (dφ|_x) = 1`, conclusion "bijective", proof `orSign_ne_zero_iff` | **delete**; `Milnor.bijective_mfd_extChartAt` (`OrientTransport.lean` line 67) proves it from `x ∈ (extChartAt I x_c).source` |
| `chartFrameCLM_bijective` | 54 | same | replace `hx` by `x ∈ source` |
| `orSign_chartFrameCLM` | 64 | states only (relates the hub-relative sign to `frameSign`) | keep as the *bridge*; with hub orientation `stdOr m` it becomes the definition of `chartSign` |
| `exists_dualTuple` | 77 | `oM` only via `hx` (invertibility) and in the last conjunct | restate the last conjunct as `sgn (det (basisCLM τ)) = chartSign hM x_c x v`; the rest is orientation-free |
| `orientation_eq_of_orSign_basisCLM_eq` | 130 | takes an arbitrary `o : Orientation ℝ (EuclideanSpace ℝ (Fin m)) (Fin m)`, no manifold orientation | instantiate at `o := stdOr m`; unchanged |

### 1.4 `MoveH.lean` and `CancelH.lean` — the glued homotopies

Section variables `oM` and
`hpos : ∀ z ∈ ballU hM x_c R, orSign (oM.or z) (oM.or x_c) (dφ_{x_c}|_z) = 1`.

| decl | lines | orientation | verdict |
|---|---|---|---|
| `moveΦ_south_of_le`, `contMDiff_moveH`, `moveH_eq_north_iff`, `mfd_moveH_slice_of_mem` | MoveH 57–99 | none | unchanged |
| `bijective_mfd_moveH_slice_of_mem` | MoveH 117 | `oM`, `hpos` used **once**, as `mfd_extChartAt_bijective oM (hpos x hx)` | delete `oM`, `hpos`; use `bijective_mfd_extChartAt ((mem_ballU.1 hx).1)` |
| `isRegularValue_moveH_slice`, `isRegularValue_moveH` | MoveH 138, 160 | ditto (the second also at line 195) | delete `oM`, `hpos` |
| `cancelΦ_south_of_le`, `contMDiff_cancelH`, `cancelH_eq_north_iff`, `mfd_cancelH_slice_of_mem` | CancelH 56–95 | none | unchanged |
| `bijective_mfd_cancelH_slice_of_mem`, `isRegularValue_cancelH_slice`, `isRegularValue_cancelH` | CancelH 113, 135, 164 | same single use (lines 131, 199) | delete `oM`, `hpos` |

**Both files become orientation-free.** This is a strict simplification: six theorems lose two
hypotheses each, and `exists_move`/`exists_cancel` lose the obligation to supply `hpos` to the
regularity lemmas.

### 1.5 `Move.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `moveH_slice_preimage`, `pontV_moveH_slice_of_notMem`, `pontV_moveH_slice_of_mem` | 49, 72, 90 | none | unchanged |
| `exists_move` | 130 | (i) `hpos`; (ii) `exists_dualTuple oM (hpos …)` twice; (iii) the hypothesis `hsign : frameSign v₁ x₁ = frameSign (F.v x₀) x₀`, used **only** at line 168–170 to get `e₀.orientation = e₁.orientation` for the two dual tuples, which is what `exists_tuplePath` needs | states only; restate `hsign` as `chartSign hM x_c x₁ v₁ = chartSign hM x_c x₀ (F.v ⟨x₀,·⟩)` and delete `oM`, `hpos` |

*What the proof needs about the two points.* Both in `ballU hM x_c (R/4)`; `closedBall (φ x_c x_c) R
⊆ φ.target`; every other point of `F.N` outside `closure (ballU hM x_c R)`; frames tangent,
independent, equal chart-determinant sign. **No path, no connectedness, no orientation.** One chart
containing both points, with room for the radii, is all.

### 1.6 `Cancel.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `basisCLM_smul`, `cancelH_slice_preimage_zero/one`, `pontV_cancelH_slice_of_notMem` | 32–116 | none | unchanged |
| `frameSign_cancelH_slice` | 136 | `oM` in the statement and in the proof: `hmul3` together with `hpos x_t hx_t` is what moves the sign from `oM.or x_t` to `oM.or x_c`; the conclusion is `sgn l * orSign (oM.or x_c) (stdOr m) id` | restate as `chartSign hM x_c x_t (pontV …) = sgn l`; `hmul3` and `hpos` **disappear**, and the trailing `orSign (oM.or x_c) (stdOr m) id` factor with it (it was exactly `orEps x_c⁻¹`). ≈ 25 lines shorter |
| `exists_cancel` | 209 | `hpos` plus the two `frameSign` conclusions | restate the conclusions as `chartSign hM x_c x₁ (F₀.v x₁) = 1` and `chartSign hM x_c x₂ (F₀.v x₂) = -1`; delete `oM`, `hpos` |

*What the proof needs about the two points.* One chart at `x_c` with `closedBall (φ x_c x_c) R ⊆
target`; the two points at chart positions `c₀ + a • w` and `c₀ - a • w` with `‖w‖ = 1`, `0 < a`,
`8 * a ≤ R`, `‖c₀ - φ x_c x_c‖ < R / 8`, both in the chart source; all other points of `F.N` off
`closure (ballU hM x_c R)`. So the essential geometric input is that the two points are **symmetric
about a centre in one chart** — `cancel_step` manufactures this by taking `c₀` to be the midpoint of
the two chart images and `a` half their distance. No arc, no connectedness, no orientation.

### 1.7 `Reach.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `linearIndependent_single`, `FramedCobordant.refl'`, `injective_mfd_val`, `chartCoord_mfd_val`, `AgreesOff` | 32–191 | none | unchanged |
| `exists_frame_of_sign` | 84 | states only (frames of both `frameSign`s at a point) | `exists_frame_of_selfSign`: the standard frame has `selfSign = 1` (`basisCLM_single_eq_id`, `det id = 1`), the `Tcan w₀ (-1/2)`-reflected one `-1` (`det_Tcan`); the `by_cases hsε : s = ε` split disappears. ≈ 20 lines shorter |
| `exists_goodBall` | 153 | `oM` only to produce the `hpos` conjunct, from `oM.cont y` | delete `oM` and that conjunct; the remaining content (a chart ball inside a given open set whose closure misses a finite set) is orientation-free. ≈ 12 lines shorter |
| `move_in_ball` | 196 | `oM` via `exists_goodBall` and via the `hsign` hypothesis | restate `hsign` with `chartSign` relative to the ball's centre |
| `exists_reach` | 245 | **the one place where a global sign runs an argument**: the set `Reach` (line 267) is defined by `frameSign (F'.v z) z = s`, and `exists_frame_of_sign` supplies frames of sign `s` at each newly reached point. The orientation is the bookkeeping that makes the clopen argument close up | see §2.3 and §3.2: drop the sign (reach with *some* frame) or replace it by the chain sign (`exists_slide`) |

*What the proof needs about the two points.* Only `y ∈ compl' F.N x₀`, i.e. `y` in the connected
component of `x₀` in `M ∖ (F.N ∖ {x₀})`. No chart contains both, no ball, no path is named: the
clopen argument manufactures a finite chain of chart balls. This is the lemma whose *reformulation*
along a chain of charts is both possible and useful (§4.6).

### 1.8 `Gather.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `sgnAt`, `sgnAt_of_mem`, `count_eq_sum`, `count_of_const_sign`, `frameSign_mem` | 32–58 | essential (they *are* the signed theory) | untouched; unused in the mod 2 route |
| `GInv` | 63 | the `sign` field carries the orientation; `card` and `agree` do not | for mod 2 use `card` only (`GInvFree`), or skip gathering altogether (§4.9) |
| `unmatched`, `mem_unmatched`, `ChainP`, `card_unmatched_pos_iff`, `badSet`, `mem_badSet` | 69–303 | none | reusable if gathering is wanted |
| `gather_move` | 81 | `hGs`, `hF.sign` used **only** to discharge `exists_reach`'s sign hypothesis (line 99) | states only; with a frame-free reach the hypotheses vanish. What it needs about the two points: `adjN N x z`, upgraded to `z ∈ compl' F.N x` by `closure_compl'_subset` plus `z ∉ F.N`. No chart, no ball |
| `gather_step`, `gather` | 147, 238 | only through `GInv.sign`/`hGs`; the chain combinatorics is orientation-free | states only |
| `exists_matched` | 307 | only to discharge `exists_reach`'s sign hypothesis | states only |

### 1.9 `CancelStep.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `count_of_remove_two`, `count_of_move` | 33, 77 | essential (about `count`) | unused for mod 2; the parity analogue is `Main.card_of_remove_two`, already orientation-free |
| `framedCobordant_of_frames` | 113 | `hsu`, `hsz` (equal signs at the two points), used only to feed `exists_reach` at `y = x` | states only. **Nothing geometric is needed of the two points beyond `u ≠ z`**: both frame changes happen at `mem_compl'_self`, with no motion |
| `cancel_step` | 173 | `hsign` (opposite signs); `exists_goodBall oM`; `exists_frame_of_sign hm oM u hs'`; `exists_reach … hvs`; and the bookkeeping `ε := orSign (oM.or z) (stdOr m) id` with the split `by_cases hsε : s = ε` deciding which of `u, z` sits at `c₀ + a • w` | states only, but the sign hypothesis is *the* content. In the chart-sign formulation, `ε` disappears and the split becomes `by_cases chartSign hM z u v = 1` — the same two cases, without `ε` |

*What the proof needs about the two points `x₀, z`.* (i) `z ∈ closure (compl' F.N x₀)`, so that a
point `u` of `x₀`'s component can be found inside a small chart ball at `z`; (ii) a good ball at `z`
(radius `R`, `closedBall ⊆ target`, closure missing `F.N ∖ {z}`); (iii) then the two points `u, z`
placed symmetrically about the midpoint of their chart images, with `8a ≤ R` automatic from
`u ∈ ballU hM z (R/4)`. So: a chart containing both *after* the move, a ball avoiding the rest, and a
path only in the weak sense of "same connected component of the complement of the rest".

### 1.10 `Main.lean`

| decl | line | orientation | verdict |
|---|---|---|---|
| `exists_opposite_neighbour` | 29 | `oM` only to *partition* `F.N` by sign before calling `exists_neighbour_M` | for mod 2, replace by `exists_neighbour_pair`: take `B := {x}` for any `x ∈ F.N`, `N ∖ B ≠ ∅` from `2 ≤ card`. ≈ 8 lines |
| `count_of_empty` | 49 | essential (about `count`) | unused |
| `card_of_remove_two` | 55 | **none** | reused verbatim: it is exactly the parity step |
| `framedCobordant_of_count_eq` | 86 | the signed induction; Case C (constant signs) is where the orientation does real work | the mod 2 analogue is shorter: no Case C, no gathering (§4.9) |

### 1.11 `AddPoint.lean`

`exists_lower_bound_basisCLM` (29): none. `exists_add_point` (49): `oM` only through
`exists_goodBall oM` and `exists_dualTuple oM (hpos …)`; states only; becomes orientation-free.
(It is used by the oriented `exists_framedSub_of_card` in `Hopf.lean`; that caller keeps its
orientation and gains nothing, but loses nothing either.)

---

## 2. The two ways to make the signs local, and which to use

### 2.1 Chart sign (recommended)

```lean
/-- The determinant sign of the frame `v` at `x`, read in the chart centred at `x_c`. -/
def chartSign (x_c x : M) (v : Fin m → EuclideanSpace ℝ (Fin (K+1))) : ℤ :=
  sgn (LinearMap.det ((chartFrameCLM hM x_c x v : _ →L[ℝ] _) : _ →ₗ[ℝ] _))

/-- The sign of the frame `v` at `x` read in the chart at `x` itself. -/
def selfSign (x : M) (v : Fin m → EuclideanSpace ℝ (Fin (K+1))) : ℤ := chartSign hM x x v

/-- The determinant sign of the derivative at `x` of the chart centred at `x_c`. -/
def jacSign (x_c x : M) : ℤ :=
  sgn (LinearMap.det (mfd 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) (extChartAt 𝓘(ℝ, Eᵐ) x_c) x : Eᵐ →ₗ[ℝ] Eᵐ))
```
Facts, all one- or two-liners from `orSign_self_eq_sgn_det` (`Chapter6/LevelMap.lean` line 63),
`LinearMap.det_comp`, `sgn_mul`, `mfd_extChartAt_self` (`OrientTransport.lean` line 85):

* `chartSign hM x_c x v = orSign (stdOr m) (stdOr m) (chartFrameCLM hM x_c x v)` — so every existing
  `orSign`-computation transfers verbatim with the hub orientation taken to be `stdOr m`;
* `chartSign hM x_c x v = jacSign hM x_c x * selfSign hM x v`, `jacSign hM x x = 1`;
* `chartSign ≠ 0` and `∈ {1, -1}` for tangent, independent `v` with `x` in the chart source;
* **bridge:** `frameSign hM oM v x = orEps oM x * selfSign hM x v`, and under the old `hpos`,
  `orEps oM y = orEps oM x_c * jacSign hM x_c y`; hence `hsign` in the old form is equivalent to
  `chartSign`-equality on a ball where `hpos` holds.

Cost: one new file of ≈ 300 lines (§4.1), no new concepts, and several existing proofs get shorter.

### 2.2 A local orientation at the hub (the variant, and why not)

One could keep orientations and pass a single `o : Orientation ℝ (EuclideanSpace ℝ (Fin m)) (Fin m)`
at the ball's centre, defining the orientation at the other points of the ball by
`Milnor.transport 𝓘(ℝ,Eᵐ) x_c z o`. Then the old hypothesis `hpos` becomes a *theorem*
(`orSign_transport`, `OrientTransport.lean` line 144) rather than a hypothesis — an attractive
option. But (i) since `orSign (stdOr m) o T = orSign (stdOr m) o id * sgn (det T)`, this differs from
the chart sign by one global factor and proves nothing extra; (ii) it drags an orientation object
through every statement of the local theory; (iii) at the seams between balls one still has to
compare orientations at different hubs, i.e. multiply two `jacSign`s. So the orientation buys
nothing that `±1` does not. **Use the chart sign, and keep `transport` for the loop combinatorics
only, where the dictionary of §2.4 converts it to `±1` anyway.**

### 2.3 What "local" cannot do

A local orientation cannot make `exists_reach` (`Reach.lean` line 245) local: its hypothesis is that
`y` lies in the *connected component* of `x₀` in `M ∖ (F.N ∖ {x₀})`, and the sign `s` in its
invariant is compared across the whole component. There are exactly two honest local replacements:

* **forget the sign:** reach `y` with *some* frame (`exists_reach_any`); or
* **carry the chain:** reach `y` along an explicit chain of balls and record that the sign has been
  multiplied by the chain's sign (`exists_slide`).

The second implies the first and also implies the oriented original (an orientation forces the chain
sign to be `orEps x₀ * orEps y`, §4.4), so it is the right statement to prove once.

### 2.4 Dictionary: transport = product of determinant signs

For `h : ChartHop 𝓘(ℝ,Eᵐ) x y` (`OrientTransport.lean` line 262) put
`hopSign h := jacSign hM h.hub x * jacSign hM h.hub y`, and for a chain the product `chainSign`.
Then, from `transport` (line 128) and `orSign_self_eq_sgn_det`:

* `Milnor.transport I c z o = o ↔ jacSign hM c z = 1`;
* `h.transport o = o` if `hopSign h = 1`, and `= -o` if `hopSign h = -1`;
* `c.transport o = o ↔ chainSign c = 1`, and `ChartChain.Reverses c m ↔ chainSign c = -1`;
* **slide bookkeeping:** moving a framed point from `x` to `y` inside the ball at hub `c` preserves
  `chartSign hM c · ·` (that is exactly the restated `exists_move`), hence
  `selfSign hM y v_y = hopSign h * selfSign hM x v_x`.

So the whole orientation bookkeeping of the endgame is the multiplicative group `{±1}` and the
cocycle `jacSign`. This dictionary is ≈ 80 lines and is the hinge of the plan.

---

## 3. The design question

### 3.1 Why option (a) alone does not work

"Slide a point around a reversing loop, then cancel with the existing `cancel_step` using a local
orientation" cannot be stated: there is no orientation, not even a local one, shared by the loop and
the cancelling ball. `cancel_step`'s sign hypothesis compares the two frames through *one* chart;
after a slide, what is known about the moved frame is its chart sign in the *last* ball of the loop.
Converting between the two requires precisely the `jacSign` cocycle. So option (a) has to be
performed in the language of option (b).

### 3.2 Why option (b) alone does not work

An orientation-free cancellation hypothesis of the form "the two frames are joined along an arc by a
path in `GL⁻`" is *false as a sufficient condition on an orientable manifold*: on `Sᵐ` two maps of
degrees `0` and `2` have Pontryagin manifolds of the same parity and are not homotopic. Any
orientation-free restatement must therefore keep an honest hypothesis, and that hypothesis is what
non-orientability supplies. Concretely: the condition "there is a chain from `x₀` to a neighbourhood
of `z`, avoiding the other points, whose chain sign makes the two chart signs opposite" is the
correct orientation-free hypothesis, and it is satisfiable for *both* values of the sign exactly when
a reversing loop avoiding the other points exists.

### 3.3 New idea 1: the loops of `Orientable.lean` are the wrong kind

`Orientable.lean` produces, from `¬ IsOrientable`, a reversing `ChartChain`
(`exists_reverses_of_not_isOrientable`, line 290). Its hops are "one chart whose source contains both
endpoints". Two problems:

* **Not slidable.** A framed point is moved by `exists_move`, which needs both endpoints inside
  `ballU hM x_c (R/4)` for a radius with `closedBall (φ x_c x_c) R ⊆ target`. A chart source can be
  disconnected or too thin for any such ball to join the endpoints.
* **Not an obstruction.** The module docstring of `Orientable.lean` gives an explicit counterexample
  (`ℝ` with a flipped chart on `(1,2)`) where a reversing `ChartChain` exists although `ℝ` is
  orientable; it says that passing from `Milnor.Orient` to a chart-coherent orientation needs the
  chart sources to be connected and is "not attempted here".

Both are cured by the same move: redo the dichotomy for **ball-hops**,

```lean
structure BallHop (I) (P : Set M) (x y : M) where
  hub : M
  rad : ℝ
  rad_pos : 0 < rad
  target : closedBall (extChartAt I hub hub) rad ⊆ (extChartAt I hub).target
  avoid : ∀ z ∈ closure (ballU hub rad), z ∉ P
  mem_left  : x ∈ ballU hub (rad / 4)
  mem_right : y ∈ ballU hub (rad / 4)
```
with the coercion to `ChartHop` (so all of `OrientTransport.lean`'s transport algebra is reused) and
`ChartChain.IsBall` an inductive predicate, closed under `comp`, `reverse`, `hop`, `snoc`. Since a
chart ball is connected and `jacSign hM c ·` restricted to it is constant *only after the transition
cocycle is taken into account*, a `Milnor.Orient` does forbid reversing ball-loops (§4.4), so for
ball-hops the dichotomy is an exact equivalence with no hypothesis on chart sources. **This stage
therefore also closes the gap the `Orientable.lean` docstring flags.**

### 3.4 New idea 2: the loop must avoid the other points — and that needs `2 ≤ m`

`exists_move` insists that every other point of `F.N` lie outside the closure of the ball in which
the move happens. So a reversing loop whose balls contain other points of `F.N` is useless. I
examined four ways round this and rejected them:

1. *Move the obstacles aside and back.* Works on paper, but the flip's bookkeeping tracks the class
   of one frame, and each obstacle that is moved and returned must come back with its **original
   frame**, which needs the frame-prescribing move, which needs the flip. Retracing the parking
   chain repairs the class, but the retracing chain must avoid the *current* positions of all the
   other points; the induction that keeps this straight is the configuration-space bookkeeping of an
   isotopy extension, which I estimate at 400–600 lines with high risk — worse than the alternative.
2. *Convoy.* Sliding all the points round the loop flips all their signs at once, which is no
   progress (`(+,+) ↦ (-,-)`).
3. *Arrange the induction so that the flip is only needed for a single point.* The flip with no other
   point present is free (the component is all of `M`), but cancelling two points of a
   framed `0`-manifold with `n ≥ 2` points inevitably needs a flip with `n-1 ≥ 1` obstacles.
   Creating and cancelling auxiliary pairs is local and cannot change a class.
4. *Choose the loop first, then park the obstacles off its trajectory.* Needs "the trajectory has
   empty interior", i.e. a measure/Hausdorff-dimension argument and `2 ≤ m` anyway, plus frame-free
   gathering; ≈ the same cost as the route I recommend but with a fiddlier core.

**Recommended:** prove the statement the situation actually calls for —

> a connected non-orientable manifold of dimension `≥ 2` is still connected and still
> non-orientable after finitely many points are removed,

and read off a reversing ball-loop whose balls avoid the given finite set. Ingredients: a punctured
chart ball of dimension `≥ 2` is connected (Mathlib: `OpenPartialHomeomorph.univBall` plus
`isPathConnected_compl_singleton_of_one_lt_rank`); hence `M ∖ P` is connected (a disconnection of
`M ∖ P` extends over each puncture because the punctured ball around it is connected); hence
`compl' F.N x = M ∖ (F.N ∖ {x})`; and a ball-coherent family of orientations on `M ∖ P` extends
across each puncture, because `y ↦ transport I p y (or y)` is locally constant on the punctured ball
(§4.5).

**The dimension hypothesis.** A connected non-orientable manifold has `m ≥ 2`, because every
connected `1`-manifold is orientable — but that needs the classification of `1`-manifolds, which this
project does not have (`Milnor/Appendix/OneManifold.lean` proves only the even-boundary corollary;
`Leftovers.md` item 7 estimates the classification at 2,000 lines and "not started"). **So the final
theorem must carry `hm2 : 2 ≤ m`, and this must be flagged in the docstring, in
`Exposition/Comparison.md` (as "narrower"), and in `Verification.md`.** To keep the defect isolated,
state the parity theorem from a named hypothesis (§4.5, `HasReversingBallLoop`) and derive that
hypothesis from `¬ IsOrientable ∧ 2 ≤ m` in one place; a future classification of `1`-manifolds then
upgrades the theorem by deleting one hypothesis.

### 3.5 Option (c) — what else the code offers

Three opportunities visible in the sources, all folded into the plan:

* `Milnor.bijective_mfd_extChartAt` makes `hpos` redundant everywhere (§1.4). This was not available
  when `MoveH`/`CancelH` were written.
* `card_of_remove_two` (`Main.lean` line 55) is already the parity step, orientation-free.
* With `compl' F.N x = M ∖ (F.N ∖ {x})` (available once `2 ≤ m` gives punctured connectedness) and
  the fact that a finite set has empty interior in a manifold, *any* two distinct points of `F.N`
  satisfy `z ∈ closure (compl' F.N x)`. So `exists_neighbour_M` and the whole chain combinatorics of
  `Chain.lean` become optional for the mod 2 endgame. Keep the neighbour lemma anyway (it is cheap
  and it needs no dimension hypothesis), but no gathering is needed at all.

---

## 4. The staged plan, one file per stage

Each stage is buildable and testable on its own. Estimates are Lean lines including docstrings, in
the style of the existing chapter (≈ 25–40 lines per nontrivial lemma).

### Stage 1 — `Milnor/Chapter7/ChartSign.lean` (new, ≈ 300)

*Proves.* `chartSign`, `selfSign`, `jacSign` and their algebra (§2.1); `chartSign_mem` (`±1`) and
`chartSign_ne_zero`; the bridge `frameSign_eq_orEps_mul_selfSign` and
`orEps_eq_of_orSign_chart_eq_one` (the `hpos` dictionary); `exists_frame_of_selfSign` (at every point
frames of both intrinsic signs — a shortened `exists_frame_of_sign`); and

```lean
/-- A frame at `y` with the same chart sign as a given frame at `x`, both in the chart at `c`. -/
theorem exists_frame_transport {c x y : M} (hx : x ∈ (extChartAt 𝓘(ℝ,Eᵐ) c).source)
    (hy : y ∈ (extChartAt 𝓘(ℝ,Eᵐ) c).source) {v : Fin m → EuclideanSpace ℝ (Fin (K+1))}
    (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    ∃ w, (∀ i, w i ∈ tangentM hM y) ∧ LinearIndependent ℝ w ∧
      chartFrameCLM hM c y w = chartFrameCLM hM c x v
```
built from the inverse of `dφ_y` supplied by `isInvertible_mfd_extChartAt` and `basisCLM_comp_eq`.

*Depends on.* `Hopf0.lean`, `MoveAux.lean` (for `chartFrameCLM`), `OrientTransport.lean`,
`Chapter6/LevelMap.lean` (`orSign_self_eq_sgn_det`), `CancelMap.lean` (`Tcan`, `det_Tcan`).
*Risk.* Low. *Watch.* `finrank_E` must be threaded into every `orSign` lemma, as elsewhere.

### Stage 2 — edits to `MoveAux.lean`, `MoveH.lean`, `CancelH.lean` (≈ 60 lines deleted, 40 changed)

Delete `mfd_extChartAt_bijective`; drop `oM`/`hpos` from `chartFrameCLM_bijective`,
`bijective_mfd_moveH_slice_of_mem`, `isRegularValue_moveH_slice`, `isRegularValue_moveH`,
`bijective_mfd_cancelH_slice_of_mem`, `isRegularValue_cancelH_slice`, `isRegularValue_cancelH`;
restate `exists_dualTuple`'s last conjunct with `chartSign`; keep `orSign_chartFrameCLM` as the
bridge. *Risk.* Low; the only churn is deleting `(hpos := hpos)` at the call sites.

### Stage 3 — edits to `Move.lean`, `Cancel.lean`, `AddPoint.lean`, `Reach.lean` (≈ 150 changed, net −60)

`exists_move` and `exists_cancel` restated with `chartSign` (§1.5, §1.6); `frameSign_cancelH_slice`
becomes `chartSign_cancelH_slice` and loses `hmul3`/`hpos`; `exists_add_point` loses `oM`;
`exists_goodBall` loses `oM` and the `hpos` conjunct; `move_in_ball` restated with `chartSign`; the
oriented `exists_reach` is **kept** and its proof adjusted through the Stage 1 bridge (≈ 20 lines
changed) so that `Gather.lean`, `CancelStep.lean`, `Main.lean`, `Hopf.lean` and the oriented
`hopf_homotopic` are unaffected. *Risk.* Low–moderate: this is the only stage that touches proofs the
oriented theorem depends on. *Mitigation.* Do Stage 3 in one commit and rebuild `Chapter7` fully;
`Milnor/Test.lean` already pins `hopf_homotopic`.

### Stage 4 — `Milnor/Chapter7/BallChain.lean` (new, ≈ 450)

*Proves.*

* `BallHop` (§3.3), its coercion to `ChartHop`, `symm`, and `ChartChain.IsBall` with closure under
  `comp`, `reverse`, `hop`, `snoc`;
* `hopSign`, `chainSign` and the dictionary of §2.4 (`chainSign_comp`, `chainSign_reverse`,
  `transport_eq_iff_chainSign`, `Reverses_iff_chainSign_eq_neg_one`);
* the **transition cocycle lemma**, the technical key used twice later:
  `∀ᶠ z in 𝓝 y, jacSign hM p z * jacSign hM q z = jacSign hM p y * jacSign hM q y`
  for `y ∈ source p ∩ source q`. Proof: the chart at `z` cancels between the two factors, leaving the
  determinant sign of the *fixed* transition `extChartAt p ∘ (extChartAt q).symm` at `extChartAt q z`
  (`contDiffOn_ext_coord_change`, `ContDiffOn.continuousOn_fderivWithin`, `LinearMap.det_comp`);
* **ball reachability**: for an open `C ⊆ M` with `IsPreconnected C` and `P` closed with `C ∩ P = ∅`,
  any two points of `C` are joined by a `P`-avoiding ball-chain inside `C` (clopen argument in `C`
  with `isPreconnected_connectedComponentIn`-style `subset_left_of_subset_union`, as in
  `exists_reach`, and small balls from a generalized `exists_ballU_subset`);
* **the ball dichotomy**, `P = ∅` case: `¬ IsOrientable → ∃ reversing ball-loop at every point`,
  a faithful copy of `Orientable.lean`'s construction (`someChain`, `transportFrom`,
  `isChartCoherent_transportFrom`) with `IsBall` added — the coherence obtained is ball-coherence,
  which suffices for `Orient.ofTransportSection`;
* the converse `Orient → chainSign = orEps x * orEps y` (clopen argument inside a ball, using the
  cocycle lemma), giving the **exact equivalence** `IsOrientable ↔ no reversing ball-loop` for
  connected `M`.

*Depends on.* `OrientTransport.lean`, `Orientable.lean`, `Glue.lean` (`ballU`,
`closure_ballU_subset`), Stage 1. *Risk.* Moderate: the cocycle lemma is `mfderiv`/`fderiv` plumbing;
the rest is boilerplate. *Note.* Generalize `exists_ballU_subset` (`Segment.lean` line 32) to an
abstract manifold, or duplicate it here.

### Stage 5 — `Milnor/Chapter7/Puncture.lean` (new, ≈ 650) — **the risky stage**

*Proves.*

* `isConnected_ballU_diff_singleton (hm2 : 2 ≤ m)`: a punctured chart ball is connected
  (`OpenPartialHomeomorph.univBall` + `isPathConnected_compl_singleton_of_one_lt_rank`, transported
  by the chart);
* `isConnected_diff_finite (hm2 : 2 ≤ m) (hP : P.Finite)`: `M ∖ P` is connected — extend a
  disconnection over each puncture using the previous item;
* `compl'_eq_diff`: `compl' F.N x = M ∖ (F.N ∖ {x})`, and `exists_mem_open_notMem_finite` (a
  generalization of `exists_notMem_finite`, `Hopf.lean` line 71, from `M` to any nonempty open set);
* `extend_ballCoherent`: a ball-coherent family on `M ∖ P` extends to a transport section on `M`
  (set `or p := transport I p y (or y)`; well defined because `y ↦ transport I p y (or y)` is locally
  constant on the punctured ball — this is where the Stage 4 cocycle lemma is used — and the
  punctured ball is connected);
* **the punctured dichotomy**, the interface the rest of the plan consumes:

```lean
/-- A reversing loop of chart balls at `x₀`, all of them missing `P`. -/
def HasReversingBallLoop (P : Set M) (x₀ : M) : Prop :=
  ∃ c : ChartChain 𝓘(ℝ,Eᵐ) x₀ x₀, c.IsBall P ∧ chainSign c = -1

theorem hasReversingBallLoop_of_not_isOrientable (hm2 : 2 ≤ m)
    (hconn : ConnectedSpace M) (hnor : ¬ IsOrientable 𝓘(ℝ,Eᵐ) M m)
    {P : Set M} (hP : P.Finite) {x₀ : M} (hx₀ : x₀ ∉ P) : HasReversingBallLoop hM P x₀
```
*Depends on.* Stage 4; Mathlib `Mathlib/Analysis/Normed/Module/Connected.lean` and
`Mathlib/Analysis/Normed/Module/Ball/Homeomorph.lean`. *Risk.* **High** — this is the stage with new
mathematics. *Fallbacks, in order of preference.* (i) Prove the two connectivity statements and the
extension lemma as above. (ii) If the extension lemma resists, replace it by the *detour*
construction: refine each hop of a plain reversing ball-loop into a chain of balls following a path
in the punctured ball, using the cocycle lemma for the invariance of the sign (≈ the same size, more
fiddly: uniform continuity and a partition of the path). (iii) If the whole stage stalls, keep
`HasReversingBallLoop` as a hypothesis of the theorems downstream: everything from Stage 6 on is
independent of how it is obtained.

### Stage 6 — `Milnor/Chapter7/Slide.lean` (new, ≈ 350)

*Proves.*

```lean
/-- Sliding a framed point along a chain of balls multiplies its sign by the chain's sign. -/
theorem exists_slide (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ y : M} (hx₀ : x₀ ∈ F.N)
    (c : ChartChain 𝓘(ℝ,Eᵐ) x₀ y) (hc : c.IsBall (F.N \ {x₀})) :
    ∃ (F' : FramedSub hM 0 m), F'.N = (F.N \ {x₀}) ∪ {y} ∧ AgreesOff F F' x₀ ∧
      FramedCobordant hM F F' ∧
      ∀ hy : y ∈ F'.N, selfSign hM y (fun i => F'.v i ⟨y, hy⟩) =
        chainSign c * selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩)
```
by induction on the chain: each step is the restated `exists_move` with the arriving frame supplied
by `exists_frame_transport`, and the sign bookkeeping is §2.4. Then

* `exists_reach_any` (reach any point of the component with *some* frame) — from `exists_slide` plus
  Stage 4's ball reachability inside `compl' F.N x₀`;
* **the flip** `exists_flip`: with `HasReversingBallLoop (F.N \ {x₀}) x₀`, there is `F'` with
  `F'.N = F.N`, `AgreesOff F F' x₀`, `FramedCobordant hM F F'` and the sign at `x₀` reversed. (The
  loop returns `x₀` to itself and never moves the other points, so the point set and all other
  frames are literally unchanged.)
* `exists_frame_free`: change the frame at a point of `F.N` to **any** tangent independent frame
  (compare `selfSign`; flip if needed, then an in-class change at the point, which is
  `move_in_ball` with `y₁ = y₂`);
* `exists_reach_free`: `exists_reach_any` followed by `exists_frame_free` at the target — the
  drop-in, sign-free replacement for `exists_reach`.

*Depends on.* Stages 1, 3, 4, 5. *Risk.* Moderate: the avoidance data must be threaded through the
induction (the set `F.N ∖ {x₀}` is invariant, which is what makes it work).

### Stage 7 — `Milnor/Chapter7/CancelFree.lean` (new, ≈ 260)

*Proves.* `framedCobordant_of_frames_free` (change the frames at two distinct points to anything),
and

```lean
theorem cancel_step_free (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ z : M}
    (hx₀ : x₀ ∈ F.N) (hz : z ∈ F.N) (hxz : x₀ ≠ z) (hnb : z ∈ closure (compl' F.N x₀))
    (hflip : ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop hM P x) :
    ∃ F'' : FramedSub hM 0 m, F''.N = F.N \ {x₀, z} ∧
      (∀ i x (hx : x ∈ F.N), x ≠ x₀ → x ≠ z → ∀ hx' : x ∈ F''.N, F''.v i ⟨x,hx'⟩ = F.v i ⟨x,hx⟩) ∧
      FramedCobordant hM F F''
```
a copy of `cancel_step` (`CancelStep.lean` line 173) with `hsign` deleted: move `x₀` to `u` near `z`
with `exists_reach_free`, choosing at `u` a frame whose chart sign in the chart at `z` is the
negative of `z`'s (which `exists_frame_of_selfSign` provides), then the same `exists_cancel`
call, with the `by_cases s = ε` split replaced by `by_cases chartSign hM z u v = 1`.
Also `exists_neighbour_pair` (`Main.lean`'s `exists_opposite_neighbour` with the signs deleted).
*Depends on.* Stages 3, 6. *Risk.* Low–moderate (mostly transcription).

### Stage 8 — `Milnor/Chapter7/CountMod2.lean` (new, ≈ 260)

*Proves.*

```lean
def countMod2 (F : FramedSub hM 0 m) : ZMod 2 := (F.finite_N.toFinset.card : ZMod 2)

theorem framedCobordant_of_countMod2_eq (hm : 0 < m) (hconn : ConnectedSpace M)
    (hflip : ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop hM P x)
    (F G : FramedSub hM 0 m) (h : countMod2 F = countMod2 G) : FramedCobordant hM F G
```
by strong induction on `F.finite_N.toFinset.card + G.finite_N.toFinset.card`: if `F` has `≥ 2`
points, `exists_neighbour_pair` and `cancel_step_free` remove two (`card_of_remove_two`,
`Main.lean` line 55, does the arithmetic) and recurse; symmetrically for `G`; otherwise both have
`≤ 1` point and equal parity, hence equal cardinality — both empty (`FramedSub.ext'`) or one point
each, where `exists_reach_free` moves `F`'s point onto `G`'s with `G`'s frame and `FramedSub.ext'`
finishes. Also the degree bridge

```lean
theorem countMod2_pontryagin (hm : 0 < m) (hf : ContMDiff … ∞ f) (hy : IsRegularValue … f y)
    (e : Fin m → EuclideanSpace ℝ (Fin m)) (he : LinearIndependent ℝ e) :
    countMod2 (pontryagin hM hMc hne hf hy (zero_add m) e he) = degMod2 𝓘(ℝ,Eᵐ) 𝓘(ℝ,Eᵐ) f
```
from `pontryagin … |>.N = f ⁻¹' {y}`, `Set.ncard_eq_toFinset_card` and `degMod2_eq`
(`Chapter4/Degree.lean` line 113); instances needed: `CompactSpace M` from `hMc`, `T2Space`,
`SecondCountableTopology`, and `PreconnectedSpace (Sph m)` from `Sphere.preconnectedSpace hm`.
*Risk.* Low.

### Stage 9 — `Milnor/Chapter7/HopfMod2.lean` (new, ≈ 150)

The final theorems (§6), plus registration in `Milnor.lean` and `Milnor/Test.lean`.
*Risk.* Low.

### Optional Stage 10 — the framed converse (≈ 120)

`FramedCobordant hM F G → countMod2 F = countMod2 G`, via `exists_map_of_framedSub_subset`
(realize `F`, `G` as Pontryagin manifolds), `smoothHomotopic_of_framedCobordant` and
`degMod2_eq_of_homotopy`; this upgrades Stage 8 to an "if and only if" on the framed side.

---

## 5. Every existing declaration to be generalized, with the exact generalization

| declaration | file · line | exact change |
|---|---|---|
| `mfd_extChartAt_bijective` | MoveAux 42 | **delete**; replace uses by `Milnor.bijective_mfd_extChartAt (mem_ballU.1 hx).1` |
| `chartFrameCLM_bijective` | MoveAux 54 | hypothesis `orSign (oM.or x) (oM.or x_c) (dφ|_x) = 1` → `x ∈ (extChartAt 𝓘(ℝ,Eᵐ) x_c).source`; drop `oM` |
| `exists_dualTuple` | MoveAux 77 | drop `oM`; hypothesis as above; last conjunct `orSign (stdOr m) (oM.or x_c) (basisCLM τ) = frameSign hM oM v x` → `sgn (det (basisCLM τ)) = chartSign hM x_c x v` |
| `orSign_chartFrameCLM` | MoveAux 64 | keep; add `chartSign_eq_orSign` (hub orientation `stdOr m`) and the bridge `frameSign_eq_orEps_mul_selfSign` |
| `bijective_mfd_moveH_slice_of_mem` | MoveH 117 | drop `oM`, `hpos` |
| `isRegularValue_moveH_slice` | MoveH 138 | drop `oM`, `hpos` |
| `isRegularValue_moveH` | MoveH 160 | drop `oM`, `hpos` |
| `bijective_mfd_cancelH_slice_of_mem` | CancelH 113 | drop `oM`, `hpos` |
| `isRegularValue_cancelH_slice` | CancelH 135 | drop `oM`, `hpos` |
| `isRegularValue_cancelH` | CancelH 164 | drop `oM`, `hpos` |
| `exists_move` | Move 130 | drop `oM`, `hpos`; `hsign : frameSign v₁ x₁ = frameSign (F.v x₀) x₀` → `chartSign hM x_c x₁ v₁ = chartSign hM x_c x₀ (F.v ⟨x₀,_⟩)` |
| `frameSign_cancelH_slice` | Cancel 136 | rename `chartSign_cancelH_slice`; drop `oM`, `hpos`; conclusion `sgn l * orSign (oM.or x_c) (stdOr m) id` → `sgn l` (delete `hmul3`) |
| `exists_cancel` | Cancel 209 | drop `oM`, `hpos`; the two `frameSign … = ± orSign (oM.or x_c) (stdOr m) id` conclusions → `chartSign hM x_c x₁ … = 1`, `chartSign hM x_c x₂ … = -1` |
| `exists_add_point` | AddPoint 49 | drop `oM` (only `exists_goodBall`/`exists_dualTuple` used it) |
| `exists_frame_of_sign` | Reach 84 | rename `exists_frame_of_selfSign`; drop `oM`; conclusion `frameSign hM oM v x = s` → `selfSign hM x v = s`; delete the `by_cases s = ε` split |
| `exists_goodBall` | Reach 153 | drop `oM` and the `hpos` conjunct from the conclusion |
| `move_in_ball` | Reach 196 | drop `oM`; the frame hypothesis and conclusion in terms of `chartSign hM y · ·` |
| `exists_reach` | Reach 245 | **keep** the oriented statement (used by `Gather`, `CancelStep`, `Main`, `Hopf`); adjust the proof to the new `move_in_ball`/`exists_frame_of_selfSign` through the Stage 1 bridge. Add `exists_reach_any`, `exists_reach_free` in Stage 6 |
| `exists_ballU_subset` | Segment 32 | generalize from the slice-submanifold setting to an abstract `[ChartedSpace]`/`[IsManifold]`, for use in Stage 4 (or duplicate) |
| `exists_notMem_finite` | Hopf 71 | generalize: a nonempty **open** subset of `M` contains a point outside any finite set (needed for parking-free arguments and for "finite sets have empty interior") |
| `GInv` | Gather 63 | if gathering is wanted for mod 2, add `GInvFree` with the `sign` field removed; otherwise untouched |
| `exists_opposite_neighbour` | Main 29 | add the sign-free `exists_neighbour_pair` (`B := {x}`, hypothesis `2 ≤ F.finite_N.toFinset.card`) |

Nothing in `Gather.lean`, `CancelStep.lean`, `Main.lean` or `Hopf.lean` needs to change: the oriented
theorem keeps its own `exists_reach`, `cancel_step`, `gather`, `framedCobordant_of_count_eq`,
`hopf_homotopic`.

---

## 6. The final theorems, in the project's vocabulary

In `Milnor/Chapter7/HopfMod2.lean`, with
`M : Set (EuclideanSpace ℝ (Fin (K+1)))`,
`hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K+1))) (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin w)) M`,
`hMc : IsCompact M`, `hne : M.Nonempty`, and `Eᵐ := EuclideanSpace ℝ (Fin m)`:

```lean
/-- **Framed `0`-manifolds of a connected non-orientable manifold are classified by the parity of
the number of points.** -/
theorem framedCobordant_of_card_parity (hm2 : 2 ≤ m)
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; haveI := hM.isManifold;
      ¬ IsOrientable 𝓘(ℝ, Eᵐ) M m)
    (F G : FramedSub hM 0 m)
    (h : (F.finite_N.toFinset.card : ZMod 2) = (G.finite_N.toFinset.card : ZMod 2)) :
    FramedCobordant hM F G

/-- **Milnor's remark at the end of §7 (p. 50): the degree modulo `2` classifies the maps of a
connected non-orientable manifold to the sphere.** -/
theorem hopf_homotopic_mod2 (hm2 : 2 ≤ m)
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; haveI := hM.isManifold;
      ¬ IsOrientable 𝓘(ℝ, Eᵐ) M m)
    {f g : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) ∞ g) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) f g ↔
      degMod2 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) f = degMod2 𝓘(ℝ, Eᵐ) 𝓘(ℝ, Eᵐ) g
```
The forward direction is `degMod2_eq_of_homotopy` (`Chapter4/Degree.lean` line 141) applied to the
homotopy, and needs neither orientability nor `2 ≤ m` (only `0 < m`, for
`PreconnectedSpace (Sph m)`). The reverse direction runs: regular values `y` for `f` and `y'` for `g`
(`dense_regularValues`), positive bases at them, `countMod2_pontryagin` twice,
`framedCobordant_of_card_parity`, then `smoothHomotopic_of_framedCobordant` (`ThmAconv.lean` line
109) — exactly the skeleton of `hopf_homotopic`, with `count`/`deg` replaced by
`countMod2`/`degMod2` and with no orientation of `M` anywhere.

Docstring must record: `2 ≤ m` is an artefact — a connected `1`-manifold is orientable, so
`hnor` forces `2 ≤ m` in mathematics, but the classification of `1`-manifolds is not formalized
here (`Leftovers.md` item 7).

---

## 7. What is new mathematics, what is reworking, and the risks

**Reworking only** (no new idea; mechanical once the chart sign is in place): Stages 1, 2, 3, 6, 7,
8, 9. These are ≈ 1,500 lines and I would expect them to go through without surprises. Stage 3 is
the only one that touches the oriented theorem's dependencies.

**Genuinely new:**

1. **Loops of balls.** `Orientable.lean`'s chart-hops are not slidable, and (by its own
   counterexample) not an obstruction to orientability. Stage 4 re-proves the dichotomy for round
   chart balls, where the equivalence is exact. The technical key is the transition cocycle lemma:
   `jacSign p z * jacSign q z` is locally constant in `z`, because the chart at `z` cancels and what
   is left is the determinant sign of a *fixed* transition map. Risk: moderate (`mfderiv`/`fderiv`
   plumbing).
2. **The loop must avoid the other points.** Stage 5: a connected non-orientable manifold of
   dimension `≥ 2` minus a finite set is connected and non-orientable. Risk: high; three fallbacks
   listed in Stage 5. This is also where `2 ≤ m` enters, and the only real gap between the formal
   statement and Milnor's.

**Two smaller things to watch.** (i) The mod 2 endgame needs no gathering at all; do not port
`gather`/`exists_matched` unless the Stage 5 fallback (iv) of §3.4 is taken, which needs a frame-free
gathering lemma. (ii) A framed `0`-manifold cannot be modified "by hand" anywhere in the current
development — every framed manifold is a Pontryagin manifold — so keep all new statements
existential, as `exists_move`/`exists_reach` are; a "replace the frame at one point" constructor
would need `ContMDiff` of an arbitrary field on a `0`-dimensional manifold, which nothing supplies.

**Estimate.** ≈ 2,420 new lines plus ≈ 200 lines of edits, against `Leftovers.md`'s 1,200 for item
6b. The difference is Stages 4 and 5, neither of which was foreseen there: 6b assumed the loops of
6a could be used as they are.

---

## 8. Registration checklist

* `Milnor.lean`: add `Chapter7.ChartSign`, `Chapter7.BallChain`, `Chapter7.Puncture`,
  `Chapter7.Slide`, `Chapter7.CancelFree`, `Chapter7.CountMod2`, `Chapter7.HopfMod2` after
  `Chapter7.Orientable`.
* `Milnor/Test.lean`: add `#print axioms` for `Milnor.Framed.framedCobordant_of_card_parity`,
  `Milnor.Framed.hopf_homotopic_mod2`, `Milnor.Framed.countMod2_pontryagin`,
  `Milnor.hasReversingBallLoop_of_not_isOrientable`, `Milnor.isConnected_diff_finite`.
* `README.md` status table: one row for §7 p. 50.
* `Leftovers.md`: rewrite item 6b (new stage list, revised estimate, the `2 ≤ m` caveat); note in
  item 7 that the classification of `1`-manifolds would remove that caveat.
* `Exposition/Chapter7.md`: the closing "Checked by machine" paragraph currently says the mod 2
  remark is *not* verified — update it, and turn the "two remarks without proof" block into a
  statement with the parity argument spelled out.
* `Exposition/Comparison.md` / `Comparison.json` / `Verification.md`: a new row for the mod 2
  theorem, labelled "narrower" because of `2 ≤ m`, plus one for the sharpened orientability
  dichotomy (loops of balls).
