import Mathlib

/-!
Milnor, *Morse Theory*, §3, pp. 20–22: Lemmas 3.6 and 3.7.

# Attaching a cell along homotopic maps, or to homotopy equivalent spaces

For a space `X` and a continuous `φ : S^{n-1} → X`, `X ∪_φ e^n` is obtained from the disjoint union
of `X` and the closed disk `D^n` by identifying each `u ∈ S^{n-1}` with `φ(u)`. Here it is the
pushout of `X ← S^{n-1} → D^n` in `TopCat` (`Morse.AttachCell φ`), built from Mathlib's `∂𝔻 n`,
`𝔻 n` and `diskBoundaryInclusion n` (the basic cells of Mathlib's CW complexes), as in
`Morse/Chapter2/CellAdjunction.lean` and `Morse/Chapter2/CellPatch.lean`.

**Lemma 3.6** (p. 20, after J. H. C. Whitehead), paraphrased: if `φ₀, φ₁ : S^{n-1} → X` are
homotopic, the identity of `X` extends to a homotopy equivalence `X ∪_{φ₀} e^n → X ∪_{φ₁} e^n`.

**Lemma 3.7** (p. 21, after an unpublished paper of P. Hilton), paraphrased: a homotopy equivalence
`f : X → Y` extends to a homotopy equivalence `X ∪_φ e^n → Y ∪_{fφ} e^n`.

Both are proved with Milnor's explicit formulas. A point of the cell is written `tu`, with
`t = ‖z‖ ∈ [0, 1]` and `u = z/‖z‖ ∈ S^{n-1}`. All of Milnor's maps and homotopies are, on the cell,
`tu ↦ (t/a)u` (a point of the cell) for `t ≤ a` and `tu ↦ Ψ(t, u)` (a point of `X`) for `t ≥ a`, for
a radius `a ∈ (0, 1]` and a map `Ψ` with `Ψ(a, u) = φ(u)` (`Morse.radial`). His `k` (Lemma 3.6) has
`a = 1/2` and `Ψ(t, u) = φ_{2-2t}(u)`; his `q_τ` (Lemma 3.7) has `a = (1+τ)/2` and
`Ψ(t, u) = h_{2-2t+τ}(φ(u))`.

## What Milnor's text leaves implicit

* **Maps and homotopies out of `X ∪_φ e^n`.** A map given by compatible formulas on `X` and on the
  cell is continuous: the universal property of the pushout (`Morse.cellDesc`). For a *homotopy*
  `I × (X ∪_φ e^n) → Z` given on `I × X` and `I × D^n` one needs more, because a product of a
  quotient map with the identity of `I` must again be a quotient map; this holds since `I` is
  locally compact (J. H. C. Whitehead's lemma). Here it is the exponential law
  `C(I × P, Z) = C(P, C(I, Z))` for locally compact `I` (`Morse.cellHomotopy`). Milnor uses both
  facts silently.
* **Continuity of the formulas** on the cell: pasting along the sphere `t = a`, where the two
  formulas agree because `Ψ(a, u) = φ(u)` is identified with `u` (`Morse.continuous_radial`). The
  case `n = 0` (`S^{-1} = ∅`, `D^0` a point) needs no separate treatment.
* **`kℓ ≃ id` and `ℓk ≃ id`**, which Milnor says it "is now not difficult to verify" (p. 21), with
  `ℓ` "defined by similar formulas". Here `ℓ` is `k` for the reversed homotopy, so that `ℓk(tu)`
  is `4tu` for `t ≤ 1/4`, `φ_{4t-1}(u)` for `1/4 ≤ t ≤ 1/2` and `φ_{2-2t}(u)` for `t ≥ 1/2`
  (`Morse.lemma36_zero`): along each radius the outer three quarters run out along the homotopy to
  `φ₁` and back. The homotopy to the identity
  shrinks this excursion: with `a = (1 + 3τ)/4`, it is `tu ↦ (t/a)u` for `t ≤ a` and
  `tu ↦ φ_{min(4(t-a), 2-2t)}(u)` for `t ≥ a` (`Morse.lemma36Homotopy`; the homotopy `H_τ` of the
  exposition, as one formula). `kℓ ≃ id` is the same statement for the reversed homotopy.
* **Lemma 3.7 uses the proof of Lemma 3.6, not its statement**: Milnor's homotopy `q_τ` from `kGF`
  to the identity ("using the specific definitions of `k`, `G`, and `F`", p. 22) needs the formula
  of `k`, and Step 1 needs that `k` has a left homotopy inverse. Here `k` is `Morse.lemma36Map` for
  the homotopy `h_t φ` from `gfφ` to `φ` (`Morse.homotopyAttach`).
* **"A similar proof shows that `G` has a left homotopy inverse"** (p. 22): it is the same statement
  for `(Y, fφ, g, f)` in place of `(X, φ, f, g)`, with a homotopy from `fg` to the identity
  (`Morse.lemma37Homotopy`, applied twice in `Morse.lemma_3_7`).
* **The Assertion** (p. 22): if `F` has a left homotopy inverse `L` and a right homotopy inverse
  `R`, then `RF ≃ id` (`Morse.homotopic_of_leftInv_rightInv`), used in each of Milnor's Steps 1–3.

## Main definitions and results

* `Morse.AttachCell φ` (`X ∪_φ e^n`), `Morse.cellInl`, `Morse.cellInr`.
* `Morse.cellDesc`, `Morse.cellHomotopy`: maps and homotopies out of `X ∪_φ e^n`.
* `Morse.radial`, `Morse.continuous_radial`: Milnor's formulas on the cell.
* `Morse.lemma36Map` (Milnor's `k`), `Morse.lemma36Homotopy` (`ℓk ≃ id`), `Morse.lemma_3_6`.
* `Morse.attachMap` (Milnor's `F`: `f` on `X`, the identity on the cell), `Morse.lemma37Homotopy`
  (`kGF ≃ id`), `Morse.homotopic_of_leftInv_rightInv`, `Morse.lemma_3_7`.
-/

open Set CategoryTheory Limits TopCat ContinuousMap
open scoped unitInterval

universe u

noncomputable section

namespace Morse

variable {n : ℕ}

/-! ### Adjunction spaces -/

/-- `X ∪_φ e^n`. -/
abbrev AttachCell {X : TopCat.{u}} (φ : ∂𝔻 n ⟶ X) : TopCat.{u} :=
  pushout φ (diskBoundaryInclusion n)

/-- The inclusion `X → X ∪_φ e^n`. -/
abbrev cellInl {X : TopCat.{u}} (φ : ∂𝔻 n ⟶ X) : X ⟶ AttachCell φ :=
  pushout.inl φ (diskBoundaryInclusion n)

/-- The characteristic map `D^n → X ∪_φ e^n` of the cell. -/
abbrev cellInr {X : TopCat.{u}} (φ : ∂𝔻 n ⟶ X) : 𝔻 n ⟶ AttachCell φ :=
  pushout.inr φ (diskBoundaryInclusion n)

variable {X : TopCat.{u}} (φ : ∂𝔻 n ⟶ X)

theorem cellInl_apply_eq (s : ∂𝔻 n) :
    cellInl φ (φ s) = cellInr φ (diskBoundaryInclusion n s) :=
  ConcreteCategory.congr_hom pushout.condition s

theorem attachCell_hom_ext {Z : TopCat.{u}} {f g : AttachCell φ ⟶ Z}
    (h1 : ∀ x, f (cellInl φ x) = g (cellInl φ x)) (h2 : ∀ d, f (cellInr φ d) = g (cellInr φ d)) :
    f = g := by
  apply pushout.hom_ext
  · ext x
    exact h1 x
  · ext d
    exact h2 d

/-- A map out of `X ∪_φ e^n`, given on `X` and on the cell. -/
def cellDesc {Z : TopCat.{u}} (g : C(X, Z)) (h : C(𝔻 n, Z))
    (w : ∀ s, g (φ s) = h (diskBoundaryInclusion n s)) : AttachCell φ ⟶ Z :=
  pushout.desc (TopCat.ofHom g) (TopCat.ofHom h) (by ext s; exact w s)

@[simp]
theorem cellDesc_inl {Z : TopCat.{u}} (g : C(X, Z)) (h : C(𝔻 n, Z))
    (w : ∀ s, g (φ s) = h (diskBoundaryInclusion n s)) (x : X) :
    cellDesc φ g h w (cellInl φ x) = g x :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) x

@[simp]
theorem cellDesc_inr {Z : TopCat.{u}} (g : C(X, Z)) (h : C(𝔻 n, Z))
    (w : ∀ s, g (φ s) = h (diskBoundaryInclusion n s)) (d : 𝔻 n) :
    cellDesc φ g h w (cellInr φ d) = h d :=
  ConcreteCategory.congr_hom (pushout.inr_desc _ _ _) d

/-- **Homotopies out of `X ∪_φ e^n`** (the fact (Q2) of the exposition): a homotopy of maps out of
the adjunction space may be given on `X` and on the cell, compatibly on `S^{n-1}`. The proof
passes through the exponential law `C(I × P, Z) = C(P, C(I, Z))`, valid since `I` is locally
compact; this is J. H. C. Whitehead's lemma that `I × (quotient map)` is a quotient map. -/
def cellHomotopy {Z : TopCat.{u}} {f₀ f₁ : AttachCell φ ⟶ Z} (HX : C(I × X, Z))
    (HD : C(I × 𝔻 n, Z)) (hc : ∀ t s, HX (t, φ s) = HD (t, diskBoundaryInclusion n s))
    (h0X : ∀ x, HX (0, x) = f₀ (cellInl φ x)) (h1X : ∀ x, HX (1, x) = f₁ (cellInl φ x))
    (h0D : ∀ d, HD (0, d) = f₀ (cellInr φ d)) (h1D : ∀ d, HD (1, d) = f₁ (cellInr φ d)) :
    Homotopy f₀.hom f₁.hom := by
  let cX : X ⟶ TopCat.of C(I, Z) :=
    TopCat.ofHom (ContinuousMap.curry (HX.comp ContinuousMap.prodSwap))
  let cD : 𝔻 n ⟶ TopCat.of C(I, Z) :=
    TopCat.ofHom (ContinuousMap.curry (HD.comp ContinuousMap.prodSwap))
  have w : φ ≫ cX = diskBoundaryInclusion n ≫ cD := by
    ext s t
    exact hc t s
  let P := pushout.desc cX cD w
  have hPl : ∀ x t, P (cellInl φ x) t = HX (t, x) := fun x t =>
    congrArg (fun g : C(I, Z) => g t) (ConcreteCategory.congr_hom (pushout.inl_desc cX cD w) x)
  have hPr : ∀ d t, P (cellInr φ d) t = HD (t, d) := fun d t =>
    congrArg (fun g : C(I, Z) => g t) (ConcreteCategory.congr_hom (pushout.inr_desc cX cD w) d)
  let H : C(I × AttachCell φ, Z) := (ContinuousMap.uncurry P.hom).comp ContinuousMap.prodSwap
  have hH : ∀ t y, H (t, y) = P y t := fun _ _ => rfl
  have hend : ∀ (t : I) (f : AttachCell φ ⟶ Z), (∀ x, HX (t, x) = f (cellInl φ x)) →
      (∀ d, HD (t, d) = f (cellInr φ d)) → ∀ y, H (t, y) = f y := by
    intro t f hX hD y
    let e : AttachCell φ ⟶ Z :=
      TopCat.ofHom (H.comp ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _)))
    have he : e = f := attachCell_hom_ext φ (fun x => by
        change H (t, cellInl φ x) = _
        rw [hH, hPl, hX]) (fun d => by
        change H (t, cellInr φ d) = _
        rw [hH, hPr, hD])
    exact ConcreteCategory.congr_hom he y
  exact
    { toContinuousMap := H
      map_zero_left := hend 0 f₀ h0X h0D
      map_one_left := hend 1 f₁ h1X h1D }

/-! ### Points of the disk and of the sphere -/

/-- The point `v` of `D^n`, for `‖v‖ ≤ 1`. -/
def diskPt (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) : 𝔻 n :=
  ULift.up ⟨v, mem_closedBall_zero_iff.2 hv⟩

/-- The point `v` of `S^{n-1}`, for `‖v‖ = 1`. -/
def spherePt (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) : ∂𝔻 n :=
  ULift.up ⟨v, mem_sphere_zero_iff_norm.2 hv⟩

/-- The vector `z ∈ ℝⁿ` of a point of `D^n`. -/
abbrev dvec (d : 𝔻 n) : EuclideanSpace ℝ (Fin n) :=
  (d.down : EuclideanSpace ℝ (Fin n))

/-- The vector `u ∈ ℝⁿ` of a point of `S^{n-1}`. -/
abbrev svec (s : ∂𝔻 n) : EuclideanSpace ℝ (Fin n) :=
  (s.down : EuclideanSpace ℝ (Fin n))

theorem norm_dvec_le (d : 𝔻 n) : ‖dvec d‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 d.down.2

theorem norm_svec (s : ∂𝔻 n) : ‖svec s‖ = 1 :=
  mem_sphere_zero_iff_norm.1 s.down.2

theorem continuous_dvec : Continuous (dvec : 𝔻 n → EuclideanSpace ℝ (Fin n)) :=
  continuous_subtype_val.comp continuous_uliftDown

@[simp]
theorem dvec_diskPt (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) : dvec (diskPt v hv) = v :=
  rfl

@[simp]
theorem svec_spherePt (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) : svec (spherePt v hv) = v :=
  rfl

@[simp]
theorem dvec_inclusion (s : ∂𝔻 n) : dvec (diskBoundaryInclusion n s) = svec s :=
  rfl

theorem diskPt_dvec (d : 𝔻 n) : diskPt (dvec d) (norm_dvec_le d) = d :=
  rfl

theorem disk_ext {d d' : 𝔻 n} (h : dvec d = dvec d') : d = d' :=
  ULift.ext _ _ (Subtype.ext h)

theorem sphere_ext {s s' : ∂𝔻 n} (h : svec s = svec s') : s = s' :=
  ULift.ext _ _ (Subtype.ext h)

theorem inclusion_spherePt (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    diskBoundaryInclusion n (spherePt v hv) = diskPt v hv.le :=
  rfl

theorem norm_inv_smul_le {v : EuclideanSpace ℝ (Fin n)} {a : ℝ} (ha : 0 < a) (h : ‖v‖ ≤ a) :
    ‖a⁻¹ • v‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, inv_mul_le_iff₀ ha, mul_one]
  exact h

theorem norm_inv_norm_smul {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

theorem ne_zero_of_lt_norm {v : EuclideanSpace ℝ (Fin n)} {a : ℝ} (ha : 0 < a) (h : a ≤ ‖v‖) :
    v ≠ 0 := by
  rintro rfl
  rw [norm_zero] at h
  linarith

/-! ### A pasting lemma -/

/-- **Pasting along `α = β`** for a function defined by cases `α ≤ β` and `β ≤ α`, each piece
being continuous on its (closed) domain. -/
theorem continuous_dite_le {T Z : Type*} [TopologicalSpace T] [TopologicalSpace Z]
    {α β : T → ℝ} (hα : Continuous α) (hβ : Continuous β) (G₁ : {t // α t ≤ β t} → Z)
    (hG₁ : Continuous G₁) (G₂ : {t // β t ≤ α t} → Z) (hG₂ : Continuous G₂)
    (heq : ∀ t (h : α t = β t), G₁ ⟨t, h.le⟩ = G₂ ⟨t, h.ge⟩) :
    Continuous fun t => if h : α t ≤ β t then G₁ ⟨t, h⟩ else G₂ ⟨t, (not_le.1 h).le⟩ := by
  rw [← continuousOn_univ]
  have hU : {t | α t ≤ β t} ∪ {t | β t ≤ α t} = univ :=
    eq_univ_of_forall fun t => (le_total (α t) (β t)).elim Or.inl Or.inr
  rw [← hU]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_le hα hβ) (isClosed_le hβ hα)
  · rw [continuousOn_iff_continuous_domRestrict]
    refine hG₁.congr fun t => ?_
    simp only [domRestrict_apply]
    rw [dif_pos t.2]
  · rw [continuousOn_iff_continuous_domRestrict]
    refine hG₂.congr fun t => ?_
    simp only [domRestrict_apply]
    by_cases h : α t ≤ β t
    · rw [dif_pos h]
      exact (heq t (le_antisymm h t.2)).symm
    · rw [dif_neg h]

/-! ### Milnor's formulas on the cell -/

/-- **Milnor's formulas on the cell** (pp. 21–22). Writing a point of `D^n` as `z = tu` with
`t = ‖z‖` and `u = z/‖z‖`, `radial φ a Ψ τ z` is the point `(t/a(τ)) u` of the cell if
`t ≤ a(τ)`, and the point `Ψ(τ, t, u)` of `X` if `t > a(τ)`. -/
def radial {T : Type*} (a : T → ℝ) (ha : ∀ τ, 0 < a τ) (Ψ : T → ℝ → ∂𝔻 n → X) (τ : T)
    (d : TopCat.disk.{u} n) : AttachCell φ :=
  if h : ‖dvec d‖ ≤ a τ then cellInr φ (diskPt ((a τ)⁻¹ • dvec d) (norm_inv_smul_le (ha τ) h))
  else cellInl φ (Ψ τ ‖dvec d‖ (spherePt (‖dvec d‖⁻¹ • dvec d)
    (norm_inv_norm_smul (ne_zero_of_lt_norm (ha τ) (not_le.1 h).le))))

variable {T : Type*} {a : T → ℝ} {ha : ∀ τ, 0 < a τ} {Ψ : T → ℝ → ∂𝔻 n → X}

theorem radial_of_le {τ : T} {d : TopCat.disk.{u} n} (h : ‖dvec d‖ ≤ a τ) :
    radial φ a ha Ψ τ d = cellInr φ (diskPt ((a τ)⁻¹ • dvec d) (norm_inv_smul_le (ha τ) h)) :=
  dif_pos h

/-- On `t ≥ a(τ)` the formula is `Ψ(τ, t, u)`, also at `t = a(τ)` when `Ψ(τ, a(τ), u) = φ(u)`. -/
theorem radial_of_ge (hcompat : ∀ τ u, Ψ τ (a τ) u = φ u) {τ : T} {d : TopCat.disk.{u} n}
    (h : a τ ≤ ‖dvec d‖) :
    radial φ a ha Ψ τ d = cellInl φ (Ψ τ ‖dvec d‖ (spherePt (‖dvec d‖⁻¹ • dvec d)
      (norm_inv_norm_smul (ne_zero_of_lt_norm (ha τ) h)))) := by
  unfold radial
  split_ifs with h'
  · have key : ∀ (t : ℝ) (ht : t = a τ) (hu : ‖t⁻¹ • dvec d‖ = 1),
        cellInl φ (Ψ τ t (spherePt (t⁻¹ • dvec d) hu)) =
          cellInr φ (diskPt ((a τ)⁻¹ • dvec d) (norm_inv_smul_le (ha τ) h')) := by
      rintro t rfl hu
      rw [hcompat, cellInl_apply_eq, inclusion_spherePt]
    exact (key _ (le_antisymm h' h) _).symm
  · rfl

/-- On the boundary sphere (`a(τ) ≤ 1`), the formula is `Ψ(τ, 1, u)`. -/
theorem radial_inclusion (hcompat : ∀ τ u, Ψ τ (a τ) u = φ u) {τ : T} (ha1 : a τ ≤ 1)
    (s : ∂𝔻 n) : radial φ a ha Ψ τ (diskBoundaryInclusion n s) = cellInl φ (Ψ τ 1 s) := by
  have h1 : ‖dvec (diskBoundaryInclusion n s)‖ = 1 := norm_svec s
  rw [radial_of_ge φ hcompat (h1 ▸ ha1)]
  have hs : spherePt (‖dvec (diskBoundaryInclusion n s)‖⁻¹ • dvec (diskBoundaryInclusion n s))
      (norm_inv_norm_smul (ne_zero_of_lt_norm (ha τ) (h1 ▸ ha1))) = s :=
    sphere_ext (by simp)
  rw [hs, h1]

/-- **The continuity of Milnor's formulas**, jointly in the parameter and the point. -/
theorem continuous_radial [TopologicalSpace T] (hac : Continuous a)
    (hΨ : Continuous fun q : T × ℝ × ∂𝔻 n => Ψ q.1 q.2.1 q.2.2)
    (hcompat : ∀ τ u, Ψ τ (a τ) u = φ u) :
    Continuous fun q : T × TopCat.disk.{u} n => radial φ a ha Ψ q.1 q.2 := by
  have hn : Continuous fun q : T × TopCat.disk.{u} n => ‖dvec q.2‖ :=
    continuous_norm.comp (continuous_dvec.comp continuous_snd)
  have ha' : Continuous fun q : T × TopCat.disk.{u} n => a q.1 := hac.comp continuous_fst
  refine continuous_dite_le hn ha'
    (fun q => cellInr φ (diskPt ((a q.1.1)⁻¹ • dvec q.1.2) (norm_inv_smul_le (ha _) q.2))) ?_
    (fun q => cellInl φ (Ψ q.1.1 ‖dvec q.1.2‖ (spherePt (‖dvec q.1.2‖⁻¹ • dvec q.1.2)
      (norm_inv_norm_smul (ne_zero_of_lt_norm (ha _) q.2))))) ?_ ?_
  · refine (cellInr φ).hom.continuous.comp (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _))
    exact ((ha'.comp continuous_subtype_val).inv₀ fun q => (ha _).ne').smul
      (continuous_dvec.comp (continuous_snd.comp continuous_subtype_val))
  · have hg : Continuous fun q : {q : T × TopCat.disk.{u} n // a q.1 ≤ ‖dvec q.2‖} =>
        ((q.1.1, ‖dvec q.1.2‖, spherePt (‖dvec q.1.2‖⁻¹ • dvec q.1.2)
          (norm_inv_norm_smul (ne_zero_of_lt_norm (ha _) q.2))) : T × ℝ × ∂𝔻 n) := by
      refine (continuous_fst.comp continuous_subtype_val).prodMk
        ((hn.comp continuous_subtype_val).prodMk
          (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)))
      exact ((hn.comp continuous_subtype_val).inv₀ fun q =>
          norm_ne_zero_iff.2 (ne_zero_of_lt_norm (ha _) q.2)).smul
        (continuous_dvec.comp (continuous_snd.comp continuous_subtype_val))
    exact (cellInl φ).hom.continuous.comp (hΨ.comp hg)
  · intro q h
    have h' : ‖dvec q.2‖ ≤ a q.1 := h.le
    have := radial_of_ge φ (ha := ha) hcompat (τ := q.1) (d := q.2) h.ge
    rw [radial_of_le φ h'] at this
    exact this

/-- Two instances of Milnor's formulas with the same `a` and `Ψ` agree. -/
theorem radial_congr {T' : Type*} {a' : T' → ℝ} {ha' : ∀ τ, 0 < a' τ} {Ψ' : T' → ℝ → ∂𝔻 n → X}
    {τ : T} {τ' : T'} (h1 : a τ = a' τ') (h2 : ∀ t u, Ψ τ t u = Ψ' τ' t u)
    (d : TopCat.disk.{u} n) :
    radial φ a ha Ψ τ d = radial φ a' ha' Ψ' τ' d := by
  by_cases h : ‖dvec d‖ ≤ a τ
  · rw [radial_of_le φ h, radial_of_le φ (h1 ▸ h)]
    exact congrArg (cellInr φ) (disk_ext (by simp [h1]))
  · rw [radial, dif_neg h, radial, dif_neg (h1 ▸ h), h2]

/-- With `a = 1`, Milnor's formula is the identity of the cell. -/
theorem radial_of_eq_one {τ : T} (h1 : a τ = 1) (d : TopCat.disk.{u} n) :
    radial φ a ha Ψ τ d = cellInr φ d := by
  rw [radial_of_le φ (h1 ▸ norm_dvec_le d)]
  exact congrArg (cellInr φ) (disk_ext (by simp [h1]))

/-- `u = z/‖z‖` does not change when `z` is scaled by `c > 0`. -/
theorem inv_norm_smul_smul {v : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hc : 0 < c) :
    ‖c • v‖⁻¹ • (c • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hc.ne', mul_one]

/-! ### Lemma 3.6 -/

/-- `t ↦ t` clamped to `[0, 1]`. -/
abbrev clampI (t : ℝ) : I :=
  Set.projIcc 0 1 zero_le_one t

theorem clampI_val {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : (clampI t : ℝ) = t := by
  unfold clampI
  rw [Set.projIcc_of_mem _ ⟨h0, h1⟩]

theorem continuous_clampI : Continuous clampI :=
  continuous_projIcc

section Lemma36

variable {φ₀ φ₁ : ∂𝔻 n ⟶ X}

/-- The outer part of Milnor's map `k`: `(t, u) ↦ φ_{2-2t}(u)`. -/
def kOuter (Φ : Homotopy φ₀.hom φ₁.hom) (t : ℝ) (u : ∂𝔻 n) : X :=
  Φ (clampI (2 - 2 * t), u)

theorem continuous_kOuter (Φ : Homotopy φ₀.hom φ₁.hom) {T : Type*} [TopologicalSpace T] :
    Continuous fun q : T × ℝ × ∂𝔻 n => kOuter Φ q.2.1 q.2.2 :=
  Φ.continuous.comp ((continuous_clampI.comp (continuous_const.sub
    (continuous_const.mul (continuous_fst.comp continuous_snd)))).prodMk
      (continuous_snd.comp continuous_snd))

theorem kOuter_half (Φ : Homotopy φ₀.hom φ₁.hom) (u : ∂𝔻 n) : kOuter Φ (1 / 2) u = φ₁ u := by
  have : clampI (2 - 2 * (1 / 2)) = 1 := Subtype.ext (by rw [clampI_val] <;> norm_num)
  rw [kOuter, this, Φ.apply_one]

theorem kOuter_one (Φ : Homotopy φ₀.hom φ₁.hom) (u : ∂𝔻 n) : kOuter Φ 1 u = φ₀ u := by
  have : clampI (2 - 2 * 1) = 0 := Subtype.ext (by rw [clampI_val] <;> norm_num)
  rw [kOuter, this, Φ.apply_zero]

/-- The cell part of Milnor's map `k`. -/
def kCell (Φ : Homotopy φ₀.hom φ₁.hom) : C(TopCat.disk.{u} n, AttachCell φ₁) where
  toFun d :=
    radial φ₁ (fun _ : Unit => (1 / 2 : ℝ)) (fun _ => one_half_pos) (fun _ => kOuter Φ) () d
  continuous_toFun := by
    have h := continuous_radial φ₁ (T := Unit) (a := fun _ => (1 / 2 : ℝ))
      (ha := fun _ => one_half_pos) (Ψ := fun _ => kOuter Φ) continuous_const
      (continuous_kOuter Φ) (fun _ u => kOuter_half Φ u)
    have h2 : Continuous fun d : TopCat.disk.{u} n => (((), d) : Unit × TopCat.disk.{u} n) :=
      continuous_const.prodMk continuous_id
    have h3 := h.comp h2
    simp only [Function.comp_def] at h3
    exact h3

/-- **Milnor's map `k`** (Lemma 3.6, p. 21): `k(x) = x` on `X`, `k(tu) = 2tu` for `t ≤ 1/2` and
`k(tu) = φ_{2-2t}(u)` for `t ≥ 1/2`. -/
def lemma36Map (Φ : Homotopy φ₀.hom φ₁.hom) : AttachCell φ₀ ⟶ AttachCell φ₁ :=
  cellDesc φ₀ (cellInl φ₁).hom (kCell Φ) fun s => by
    change cellInl φ₁ (φ₀ s) = radial φ₁ (fun _ : Unit => (1 / 2 : ℝ)) (fun _ => one_half_pos)
      (fun _ => kOuter Φ) () (diskBoundaryInclusion n s)
    rw [radial_inclusion φ₁ (fun _ u => kOuter_half Φ u) (by norm_num), kOuter_one]

@[simp]
theorem lemma36Map_inl (Φ : Homotopy φ₀.hom φ₁.hom) (x : X) :
    lemma36Map Φ (cellInl φ₀ x) = cellInl φ₁ x :=
  cellDesc_inl _ _ _ _ x

theorem lemma36Map_inr (Φ : Homotopy φ₀.hom φ₁.hom) (d : TopCat.disk.{u} n) :
    lemma36Map Φ (cellInr φ₀ d) =
      radial φ₁ (fun _ : Unit => (1 / 2 : ℝ)) (fun _ => one_half_pos) (fun _ => kOuter Φ) () d :=
  cellDesc_inr _ _ _ _ d

/-- The parameter `a = (1 + 3τ)/4` of the homotopy `H_τ`. -/
def aH (τ : I) : ℝ :=
  (1 + 3 * (τ : ℝ)) / 4

theorem aH_pos (τ : I) : 0 < aH τ := by
  unfold aH
  linarith [τ.2.1]

theorem aH_le_one (τ : I) : aH τ ≤ 1 := by
  unfold aH
  linarith [τ.2.2]

/-- The outer part of the homotopy `H_τ`: `(t, u) ↦ φ_{min(4(t - a), 2 - 2t)}(u)`, which runs
out along the homotopy to `φ_{1-τ}` and back. -/
def hOuter (Φ : Homotopy φ₀.hom φ₁.hom) (τ : I) (t : ℝ) (u : ∂𝔻 n) : X :=
  Φ (clampI (min (4 * (t - aH τ)) (2 - 2 * t)), u)

theorem hOuter_aH (Φ : Homotopy φ₀.hom φ₁.hom) (τ : I) (u : ∂𝔻 n) :
    hOuter Φ τ (aH τ) u = φ₀ u := by
  have h : clampI (min (4 * (aH τ - aH τ)) (2 - 2 * aH τ)) = 0 := by
    refine Subtype.ext ?_
    rw [sub_self, mul_zero, min_eq_left (by linarith [aH_le_one τ])]
    rw [clampI_val le_rfl zero_le_one]
    rfl
  rw [hOuter, h, Φ.apply_zero]

theorem hOuter_one (Φ : Homotopy φ₀.hom φ₁.hom) (τ : I) (u : ∂𝔻 n) :
    hOuter Φ τ 1 u = φ₀ u := by
  have h : clampI (min (4 * (1 - aH τ)) (2 - 2 * 1)) = 0 := by
    refine Subtype.ext ?_
    rw [min_eq_right (by linarith [aH_le_one τ]), clampI_val (by norm_num) (by norm_num)]
    norm_num
  rw [hOuter, h, Φ.apply_zero]

theorem continuous_hOuter (Φ : Homotopy φ₀.hom φ₁.hom) :
    Continuous fun q : I × ℝ × ∂𝔻 n => hOuter Φ q.1 q.2.1 q.2.2 := by
  have ha : Continuous fun q : I × ℝ × ∂𝔻 n => aH q.1 :=
    ((continuous_const.add (continuous_const.mul continuous_subtype_val)).div_const _).comp
      continuous_fst
  exact Φ.continuous.comp ((continuous_clampI.comp ((continuous_const.mul
    ((continuous_fst.comp continuous_snd).sub ha)).min (continuous_const.sub
      (continuous_const.mul (continuous_fst.comp continuous_snd))))).prodMk
        (continuous_snd.comp continuous_snd))

theorem aH_zero : aH 0 = 1 / 4 := by
  norm_num [aH]

theorem unitInterval_symm_clampI {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    σ (clampI t) = clampI (1 - t) := by
  refine Subtype.ext ?_
  rw [unitInterval.coe_symm_eq, clampI_val h0 h1, clampI_val (by linarith) (by linarith)]

/-- The computation behind `H_0 = ℓ k` on the cell: `ℓ k(tu) = 4tu` for `t ≤ 1/4`,
`φ_{4t-1}(u)` for `1/4 ≤ t ≤ 1/2`, `φ_{2-2t}(u)` for `t ≥ 1/2`. -/
theorem lemma36_zero (Φ : Homotopy φ₀.hom φ₁.hom) (d : TopCat.disk.{u} n) :
    radial φ₀ aH aH_pos (hOuter Φ) 0 d = lemma36Map Φ.symm (lemma36Map Φ (cellInr φ₀ d)) := by
  rw [lemma36Map_inr]
  have hn := norm_nonneg (dvec d)
  rcases le_total ‖dvec d‖ (1 / 2) with h12 | h12
  · rw [radial_of_le φ₁ (a := fun _ : Unit => (1 / 2 : ℝ)) (τ := ()) h12, lemma36Map_inr]
    have h2z : ‖dvec (diskPt ((1 / 2 : ℝ)⁻¹ • dvec d)
        (norm_inv_smul_le one_half_pos h12))‖ = 2 * ‖dvec d‖ := by
      rw [dvec_diskPt, norm_smul]
      norm_num
    rcases le_total ‖dvec d‖ (1 / 4) with h14 | h14
    · rw [radial_of_le φ₀ (a := aH) (τ := 0) (by rw [aH_zero]; exact h14),
        radial_of_le φ₀ (a := fun _ : Unit => (1 / 2 : ℝ)) (τ := ())
          (by rw [h2z]; linarith)]
      refine congrArg (cellInr φ₀) (disk_ext ?_)
      simp only [dvec_diskPt, aH_zero, smul_smul]
      norm_num
    · rw [radial_of_ge φ₀ (hOuter_aH Φ) (τ := 0) (by rw [aH_zero]; exact h14),
        radial_of_ge φ₀ (a := fun _ : Unit => (1 / 2 : ℝ)) (τ := ())
          (fun _ u => kOuter_half Φ.symm u) (by rw [h2z]; linarith)]
      refine congrArg (cellInl φ₀) ?_
      rw [hOuter, kOuter, Homotopy.symm_apply]
      refine congrArg Φ (Prod.ext ?_ (sphere_ext ?_))
      · dsimp only
        rw [h2z, unitInterval_symm_clampI (by linarith) (by linarith), aH_zero,
          min_eq_left (by linarith)]
        congr 1
        ring
      · simp only [svec_spherePt, dvec_diskPt]
        rw [inv_norm_smul_smul (by norm_num)]
  · rw [radial_of_ge φ₁ (a := fun _ : Unit => (1 / 2 : ℝ)) (τ := ())
      (fun _ u => kOuter_half Φ u) h12, lemma36Map_inl,
      radial_of_ge φ₀ (hOuter_aH Φ) (τ := 0) (by rw [aH_zero]; linarith)]
    refine congrArg (cellInl φ₀) ?_
    have h : clampI (min (4 * (‖dvec d‖ - aH 0)) (2 - 2 * ‖dvec d‖)) =
        clampI (2 - 2 * ‖dvec d‖) := by
      rw [aH_zero, min_eq_right (by linarith)]
    rw [hOuter, kOuter, h]

/-- **`ℓ k ≃ id`** (Lemma 3.6, "it is now not difficult to verify", p. 21): Milnor's `ℓ` is `k`
for the reversed homotopy, and `H_τ` (`τ ∈ [0, 1]`) is `x ↦ x` on `X` and, on the cell,
`tu ↦ (t/a) u` for `t ≤ a = (1 + 3τ)/4`, `tu ↦ φ_{min(4(t - a), 2 - 2t)}(u)` for `t ≥ a`. -/
def lemma36Homotopy (Φ : Homotopy φ₀.hom φ₁.hom) :
    Homotopy ((lemma36Map Φ.symm).hom.comp (lemma36Map Φ).hom) (ContinuousMap.id _) :=
  cellHomotopy φ₀ (f₀ := lemma36Map Φ ≫ lemma36Map Φ.symm) (f₁ := 𝟙 _)
    ((cellInl φ₀).hom.comp ContinuousMap.snd)
    ⟨fun q => radial φ₀ aH aH_pos (hOuter Φ) q.1 q.2,
      continuous_radial φ₀ (((continuous_const.add (continuous_const.mul
        continuous_subtype_val)).div_const _)) (continuous_hOuter Φ) (hOuter_aH Φ)⟩
    (fun t s => by
      change cellInl φ₀ (φ₀ s) = radial φ₀ aH aH_pos (hOuter Φ) t _
      rw [radial_inclusion φ₀ (hOuter_aH Φ) (aH_le_one t), hOuter_one])
    (fun x => by
      change cellInl φ₀ x = lemma36Map Φ.symm (lemma36Map Φ (cellInl φ₀ x))
      simp)
    (fun x => rfl)
    (fun d => by
      change radial φ₀ aH aH_pos (hOuter Φ) 0 d = lemma36Map Φ.symm (lemma36Map Φ (cellInr φ₀ d))
      exact lemma36_zero Φ d)
    (fun d => by
      change radial φ₀ aH aH_pos (hOuter Φ) 1 d = cellInr φ₀ d
      exact radial_of_eq_one φ₀ (by norm_num [aH]) d)

/-- **Lemma 3.6** (J. H. C. Whitehead; Milnor, p. 20). If `φ₀, φ₁ : S^{n-1} → X` are homotopic,
the identity of `X` extends to a homotopy equivalence `k : X ∪_{φ₀} e^n → X ∪_{φ₁} e^n`. -/
theorem lemma_3_6 (h : φ₀.hom.Homotopic φ₁.hom) :
    ∃ k : ContinuousMap.HomotopyEquiv (AttachCell φ₀) (AttachCell φ₁),
      ∀ x, k (cellInl φ₀ x) = cellInl φ₁ x := by
  obtain ⟨Φ⟩ := h
  have h2 := lemma36Homotopy Φ.symm
  rw [Homotopy.symm_symm] at h2
  exact ⟨⟨(lemma36Map Φ).hom, (lemma36Map Φ.symm).hom, ⟨lemma36Homotopy Φ⟩, ⟨h2⟩⟩,
    fun x => lemma36Map_inl Φ x⟩

end Lemma36

/-! ### Lemma 3.7 -/

section Lemma37

variable {Y : TopCat.{u}}

/-- **Milnor's `F`** (p. 21): the map `X ∪_φ e^n → Y ∪_{fφ} e^n` which is `f` on `X` and the
identity on the cell. -/
def attachMap (f : X ⟶ Y) : AttachCell φ ⟶ AttachCell (φ ≫ f) :=
  cellDesc φ (f ≫ cellInl (φ ≫ f)).hom (cellInr (φ ≫ f)).hom fun s => cellInl_apply_eq (φ ≫ f) s

@[simp]
theorem attachMap_inl (f : X ⟶ Y) (x : X) : attachMap φ f (cellInl φ x) = cellInl (φ ≫ f) (f x) :=
  cellDesc_inl _ _ _ _ x

@[simp]
theorem attachMap_inr (f : X ⟶ Y) (d : TopCat.disk.{u} n) :
    attachMap φ f (cellInr φ d) = cellInr (φ ≫ f) d :=
  cellDesc_inr _ _ _ _ d

/-- The homotopy `h_t φ` from `g f φ` to `φ`, for a homotopy `h_t` from `g f` to the identity. -/
def homotopyAttach (f : X ⟶ Y) (g : Y ⟶ X) (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X)) :
    Homotopy ((φ ≫ f) ≫ g).hom φ.hom :=
  (h.compContinuousMap φ.hom).cast rfl rfl

/-- The parameter `a = (1 + τ)/2` of Milnor's homotopy `q_τ`. -/
def aQ (τ : I) : ℝ :=
  (1 + (τ : ℝ)) / 2

theorem aQ_pos (τ : I) : 0 < aQ τ := by
  unfold aQ
  linarith [τ.2.1]

theorem aQ_le_one (τ : I) : aQ τ ≤ 1 := by
  unfold aQ
  linarith [τ.2.2]

/-- The outer part of Milnor's homotopy `q_τ` (p. 22): `(t, u) ↦ h_{2-2t+τ}(φ(u))`. -/
def qOuter {f : X ⟶ Y} {g : Y ⟶ X} (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X)) (τ : I)
    (t : ℝ) (u : ∂𝔻 n) : X :=
  h (clampI (2 - 2 * t + τ), φ u)

theorem qOuter_aQ {f : X ⟶ Y} {g : Y ⟶ X} (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X))
    (τ : I) (u : ∂𝔻 n) : qOuter φ h τ (aQ τ) u = φ u := by
  have : clampI (2 - 2 * aQ τ + τ) = 1 :=
    Subtype.ext (by rw [clampI_val] <;> simp [aQ] <;> linarith)
  rw [qOuter, this, h.apply_one]
  rfl

theorem qOuter_one {f : X ⟶ Y} {g : Y ⟶ X} (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X))
    (τ : I) (u : ∂𝔻 n) : qOuter φ h τ 1 u = h (τ, φ u) := by
  have : clampI (2 - 2 * 1 + τ) = τ :=
    Subtype.ext (by rw [clampI_val] <;> linarith [τ.2.1, τ.2.2])
  rw [qOuter, this]

theorem continuous_qOuter {f : X ⟶ Y} {g : Y ⟶ X}
    (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X)) :
    Continuous fun q : I × ℝ × ∂𝔻 n => qOuter φ h q.1 q.2.1 q.2.2 :=
  h.continuous.comp ((continuous_clampI.comp ((continuous_const.sub
    (continuous_const.mul (continuous_fst.comp continuous_snd))).add
      (continuous_subtype_val.comp continuous_fst))).prodMk
        (φ.hom.continuous.comp (continuous_snd.comp continuous_snd)))

/-- **`k G F ≃ id`** (Milnor, p. 22): the homotopy `q_τ`, which is `h_τ` on `X` and, on the cell,
`tu ↦ (2/(1+τ)) tu` for `t ≤ (1+τ)/2` and `tu ↦ h_{2-2t+τ}(φ(u))` for `t ≥ (1+τ)/2`. -/
def lemma37Homotopy (f : X ⟶ Y) (g : Y ⟶ X)
    (h : Homotopy (g.hom.comp f.hom) (ContinuousMap.id X)) :
    Homotopy ((lemma36Map (homotopyAttach φ f g h)).hom.comp
      ((attachMap (φ ≫ f) g).hom.comp (attachMap φ f).hom)) (ContinuousMap.id _) :=
  cellHomotopy φ (f₀ := attachMap φ f ≫ attachMap (φ ≫ f) g ≫ lemma36Map (homotopyAttach φ f g h))
    (f₁ := 𝟙 _) ((cellInl φ).hom.comp h.toContinuousMap)
    ⟨fun q => radial φ aQ aQ_pos (qOuter φ h) q.1 q.2,
      continuous_radial φ ((continuous_const.add continuous_subtype_val).div_const _)
        (continuous_qOuter φ h) (qOuter_aQ φ h)⟩
    (fun t s => by
      change cellInl φ (h (t, φ s)) = radial φ aQ aQ_pos (qOuter φ h) t _
      rw [radial_inclusion φ (qOuter_aQ φ h) (aQ_le_one t), qOuter_one])
    (fun x => by
      change cellInl φ (h (0, x)) = lemma36Map (homotopyAttach φ f g h)
        (attachMap (φ ≫ f) g (attachMap φ f (cellInl φ x)))
      rw [h.apply_zero, attachMap_inl, attachMap_inl, lemma36Map_inl]
      rfl)
    (fun x => by
      change cellInl φ (h (1, x)) = cellInl φ x
      rw [h.apply_one]
      rfl)
    (fun d => by
      change radial φ aQ aQ_pos (qOuter φ h) 0 d = lemma36Map (homotopyAttach φ f g h)
        (attachMap (φ ≫ f) g (attachMap φ f (cellInr φ d)))
      rw [attachMap_inr, attachMap_inr, lemma36Map_inr]
      refine radial_congr φ (by norm_num [aQ]) (fun t u => ?_) d
      simp only [qOuter, kOuter, homotopyAttach, Homotopy.cast, Homotopy.compContinuousMap]
      norm_num
      rfl)
    (fun d => by
      change radial φ aQ aQ_pos (qOuter φ h) 1 d = cellInr φ d
      exact radial_of_eq_one φ (by norm_num [aQ]) d)

end Lemma37

/-- **Milnor's Assertion** (p. 22): if `L F ≃ id` and `F R ≃ id`, then `R F ≃ id` (so that `F` is a
homotopy equivalence with homotopy inverse `R`, and also `L`). The relations give
`L ≃ L (F R) = (L F) R ≃ R`, hence `R F ≃ L F ≃ id`. -/
theorem homotopic_of_leftInv_rightInv {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {F : C(A, B)} {L R : C(B, A)} (hL : (L.comp F).Homotopic (ContinuousMap.id A))
    (hR : (F.comp R).Homotopic (ContinuousMap.id B)) :
    (R.comp F).Homotopic (ContinuousMap.id A) := by
  have hLR : L.Homotopic R := by
    have h1 : (L.comp (F.comp R)).Homotopic (L.comp (ContinuousMap.id B)) :=
      (ContinuousMap.Homotopic.refl L).comp hR
    have h2 : ((L.comp F).comp R).Homotopic ((ContinuousMap.id A).comp R) :=
      hL.comp (ContinuousMap.Homotopic.refl R)
    rw [ContinuousMap.comp_id] at h1
    rw [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h2
    exact h1.symm.trans h2
  exact (hLR.symm.comp (ContinuousMap.Homotopic.refl F)).trans hL

section Lemma37Statement

variable {Y : TopCat.{u}}

/-- **Lemma 3.7** (Milnor, p. 21, following P. Hilton). A homotopy equivalence `f : X → Y` extends
to a homotopy equivalence `F : X ∪_φ e^n → Y ∪_{fφ} e^n`, namely the map which is `f` on `X` and
the identity on the cell. -/
theorem lemma_3_7 (e : ContinuousMap.HomotopyEquiv X Y) :
    ∃ F : ContinuousMap.HomotopyEquiv (AttachCell φ) (AttachCell (φ ≫ TopCat.ofHom e.toFun)),
      (∀ x, F (cellInl φ x) = cellInl (φ ≫ TopCat.ofHom e.toFun) (e x)) ∧
      ∀ d, F (cellInr φ d) = cellInr (φ ≫ TopCat.ofHom e.toFun) d := by
  set f : X ⟶ Y := TopCat.ofHom e.toFun with hf
  set g : Y ⟶ X := TopCat.ofHom e.invFun with hg
  obtain ⟨h⟩ : (g.hom.comp f.hom).Homotopic (ContinuousMap.id X) := e.left_inv
  obtain ⟨h'⟩ : (f.hom.comp g.hom).Homotopic (ContinuousMap.id Y) := e.right_inv
  set F := attachMap φ f
  set G := attachMap (φ ≫ f) g
  set k := lemma36Map (homotopyAttach φ f g h)
  -- `k` has a left homotopy inverse (Lemma 3.6), and `k G F ≃ id`
  have hk : ((lemma36Map (homotopyAttach φ f g h).symm).hom.comp k.hom).Homotopic
      (ContinuousMap.id _) := ⟨lemma36Homotopy _⟩
  have h0 : (k.hom.comp (G.hom.comp F.hom)).Homotopic (ContinuousMap.id _) :=
    ⟨lemma37Homotopy φ f g h⟩
  -- `G` has a left homotopy inverse (the same argument with `g` in the role of `f`)
  have hG : (((lemma36Map (homotopyAttach (φ ≫ f) g f h')).hom.comp
      (attachMap ((φ ≫ f) ≫ g) f).hom).comp G.hom).Homotopic (ContinuousMap.id _) :=
    ⟨lemma37Homotopy (φ ≫ f) g f h'⟩
  -- Step 1: `(G F) k ≃ id`
  have s1 : ((G.hom.comp F.hom).comp k.hom).Homotopic (ContinuousMap.id _) :=
    homotopic_of_leftInv_rightInv hk h0
  -- Step 2: `(F k) G ≃ id`
  have s2 : ((F.hom.comp k.hom).comp G.hom).Homotopic (ContinuousMap.id _) :=
    homotopic_of_leftInv_rightInv hG s1
  -- Step 3: `F` is a homotopy equivalence with inverse `k G`
  exact ⟨⟨F.hom, k.hom.comp G.hom, h0, s2⟩, fun x => attachMap_inl φ f x,
    fun d => attachMap_inr φ f d⟩

end Lemma37Statement

end Morse
