import CubeChains.Concurrency.Grading.Coarser
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/CutPresentation — `Ch Zbp` presented by its bead cuts

Generators the codimension-one refinements, relations the codimension-two ones, read in the
opposite category — the form `Concurrency/Presentation/LiftPresentation` transports to `Ch K`.

Everything rests on **unique factorisation through an intermediate shape** (`exists_factor`,
`factor_ext`): the second factor enumerates each bead of the middle shape in the order the
composite imposes on it, and the first is what is left.  A shape *is* its boundary set
(`boundaries_injective`), so a one-cut step is pinned by the boundary it removes
(`mid_eq_of_cuts_eq`), and `Cut.exists_min_first` sorts a generating path by that boundary.
-/

open CategoryTheory Equiv Opposite BPSet CubeChain CubeChains

namespace ChainCat

open CubeChains

variable {a m b : Ch Zbp}

/-! ## Uniqueness

Inside a bead of `m` the second factor preserves the event order, so the order the first factor
imposes on the source is read off the composite; across beads it is the bead order.  Two first
factors therefore differ by a monotone bijection of `beadEvent m.dims`, which is the identity. -/

/-- **The relative order inside a bead of `m` is read off the composite.** -/
private theorem pos_lt_of_factor {f : a ⟶ b} (u : a ⟶ m) (v : m ⟶ b) (huv : u ≫ v = f)
    {p q : beadEvent a.dims} (hb : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1)
    (hlt : pos (coordMap (Hom.φ u) p) < pos (coordMap (Hom.φ u) q)) :
    pos (coordMap (Hom.φ f) p) < pos (coordMap (Hom.φ f) q) := by
  have hcomp : ∀ w, coordMap (Hom.φ f) w = coordMap (Hom.φ v) (coordMap (Hom.φ u) w) := fun w => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  rw [hcomp, hcomp]
  exact coordMap_pos_lt_of_fst_eq (Hom.φ v) hb hlt

/-- **Two factorisations impose the same order on the source.** -/
private theorem lt_of_factor_of_factor {f : a ⟶ b} {u u' : a ⟶ m} {v v' : m ⟶ b}
    (huv : u ≫ v = f) (hu'v' : u' ≫ v' = f) {p q : beadEvent a.dims}
    (hlt : coordMap (Hom.φ u) p < coordMap (Hom.φ u) q) :
    coordMap (Hom.φ u') p < coordMap (Hom.φ u') q := by
  have hp := coordMap_fst_congr (Hom.φ u') (Hom.φ u) p
  have hq := coordMap_fst_congr (Hom.φ u') (Hom.φ u) q
  by_cases hbead : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1
  · have hf := pos_lt_of_factor u v huv hbead hlt
    rcases lt_trichotomy (coordMap (Hom.φ u') p) (coordMap (Hom.φ u') q) with h | h | h
    · exact h
    · exact absurd (congrArg (coordMap (Hom.φ u)) ((coordMapEquiv (Hom.φ u')).injective h))
        (ne_of_lt hlt)
    · exact absurd (pos_lt_of_factor u' v' hu'v' (by rw [hp, hq, hbead]) h) (asymm hf)
  · refine pos_lt_of_fst_lt ?_
    rw [hp, hq]
    exact lt_of_le_of_ne (fst_le_of_pos_lt hlt) fun hc => hbead (Fin.ext hc)

/-- **The two factors are determined.**  A bijection of events monotone for the event order
preserves the flattening (`pos_eq_of_monotone`), hence is the identity. -/
theorem factor_ext {f : a ⟶ b} {g g' : a ⟶ m} {e e' : m ⟶ b}
    (h : g ≫ e = f) (h' : g' ≫ e' = f) : g = g' ∧ e = e' := by
  have hmono : Monotone ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))) := by
    intro x y hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · have hx : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm x) = x :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply x
      have hy : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm y) = y :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply y
      exact le_of_lt (lt_of_factor_of_factor h h' (by rw [hx, hy]; exact hlt))
  have hGG : coordMapEquiv (Hom.φ g) = coordMapEquiv (Hom.φ g') := by
    refine Equiv.ext fun p => ?_
    have hp := pos_eq_of_monotone hmono
      ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))).bijective
      (coordMapEquiv (Hom.φ g) p)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hp
    exact (pos.injective (Fin.ext hp)).symm
  have hgg : ∀ p, coordMap (Hom.φ g) p = coordMap (Hom.φ g') p := Equiv.ext_iff.mp hGG
  have hv : ∀ (u : a ⟶ m) (v : m ⟶ b), u ≫ v = f → ∀ p,
      coordMap (Hom.φ v) (coordMap (Hom.φ u) p) = coordMap (Hom.φ f) p := fun u v huv p => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  refine ⟨hom_ext' (wedgeHom_ext hGG), hom_ext' (wedgeHom_ext (Equiv.ext fun y => ?_))⟩
  obtain ⟨p, rfl⟩ := (coordMapEquiv (Hom.φ g)).surjective y
  change coordMap (Hom.φ e) (coordMap (Hom.φ g) p) = coordMap (Hom.φ e') (coordMap (Hom.φ g) p)
  rw [hv g e h, hgg p, hv g' e' h']

/-! ## Existence

The second factor sends the `k`-th event of the bead `j` of `m` to the `k`-th smallest event of
`b` in the image, under the composite, of the events sitting in that bead. -/

/-- **Factorisation through an intermediate shape.**  Once `a ⟶ m ⟶ b` is possible at all, every
refinement `a ⟶ b` factors through `m` — in exactly one way, by `factor_ext`. -/
theorem exists_factor (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b)) (f : a ⟶ b) :
    ∃ (g : a ⟶ m) (e : m ⟶ b), g ≫ e = f := by
  obtain ⟨h₁, hb₁⟩ := nonempty_wedgeHom_iff_coarser.mp (ham.map Hom.φ)
  obtain ⟨h₂, hb₂⟩ := nonempty_wedgeHom_iff_coarser.mp (hmb.map Hom.φ)
  obtain ⟨u, v, hu, hv, huv⟩ :=
    exists_isShuffle_factor hb₁ hb₂ (isShuffle_coordMapEquiv (Hom.φ f))
  obtain ⟨γ, hγ⟩ := exists_coordMapEquiv_eq hu
  obtain ⟨ε, hε⟩ := exists_coordMapEquiv_eq hv
  refine ⟨Hom.mk γ (Subsingleton.elim _ _), Hom.mk ε (Subsingleton.elim _ _), ?_⟩
  refine hom_ext' (wedgeHom_ext (Equiv.ext fun p => ?_))
  change coordMap (γ ≫ ε) p = coordMap (Hom.φ f) p
  rw [coordMap_comp, Function.comp_apply,
    show coordMap γ p = u p from Equiv.ext_iff.mp hγ p,
    show coordMap ε (u p) = v (u p) from Equiv.ext_iff.mp hε (u p)]
  exact huv p

/-! ## The cuts of a refinement -/

/-- The boundaries a refinement of serial wedges removes. -/
def cutsOf {a b : Ch Zbp} (_f : a ⟶ b) : Finset ℕ := boundaries a.dims \ boundaries b.dims

theorem card_cutsOf {a b : Ch Zbp} (f : a ⟶ b) : (cutsOf f).card = codim f := by
  rw [cutsOf, Finset.card_sdiff_of_subset (boundaries_subset_of_hom f),
    card_boundaries, card_boundaries, codim_eq_length_sub]
  omega

theorem cutsOf_comp {a b c : Ch Zbp} (f : a ⟶ b) (g : b ⟶ c) :
    cutsOf (f ≫ g) = cutsOf f ∪ cutsOf g := by
  rw [cutsOf, cutsOf, cutsOf, ← Finset.sup_eq_union]
  exact (sdiff_sup_sdiff_cancel (boundaries_subset_of_hom f) (boundaries_subset_of_hom g)).symm

/-- Where a one-cut refinement's cut sits. -/
theorem mem_cutsOf {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) :
    t ∈ boundaries a.dims ∧ t ∉ boundaries b.dims := by
  have ht : t ∈ cutsOf f := h ▸ Finset.mem_singleton_self t
  exact Finset.mem_sdiff.mp ht

theorem exists_cutsOf_eq_singleton {f : a ⟶ b} (h : codim f = 1) : ∃ t, cutsOf f = {t} :=
  Finset.card_eq_one.mp ((card_cutsOf f).trans h)

theorem codim_eq_one_of_cutsOf {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) : codim f = 1 := by
  rw [← card_cutsOf, h, Finset.card_singleton]

/-- **A one-cut refinement erases exactly its cut from the boundary set.** -/
theorem boundaries_eq_erase {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) :
    boundaries b.dims = (boundaries a.dims).erase t := by
  rw [Finset.erase_eq, ← h, cutsOf, Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom f)]

theorem cutsOf_eq_singleton {f : a ⟶ b} {t : ℕ} (ht : t ∈ boundaries a.dims)
    (h : boundaries b.dims = (boundaries a.dims).erase t) : cutsOf f = {t} := by
  rw [cutsOf, h, Finset.sdiff_erase_self ht]

/-- **A step is pinned by the boundary it removes** — an equation of shapes, not an iso, since a
shape is its boundary set. -/
theorem mid_eq_of_cuts_eq {c c' : Ch Zbp} {e : a ⟶ c} {e' : a ⟶ c'} {t : ℕ}
    (h : cutsOf e = {t}) (h' : cutsOf e' = {t}) : c = c' :=
  Obj.eq_of_dims
    (boundaries_injective ((boundaries_eq_erase h).trans (boundaries_eq_erase h').symm))

/-! ## Factoring off a single cut -/

/-- The fine end, with the two beads meeting at a removed boundary merged. -/
private theorem exists_mid_merge (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ m : Ch Zbp, boundaries m.dims = (boundaries a.dims).erase t
      ∧ dimSum m.dims = dimSum a.dims := by
  rw [cutsOf, Finset.mem_sdiff] at ht
  have h0 : t ≠ 0 := fun h => ht.2 (h ▸ zero_mem_boundaries _)
  have hlast : t ≠ dimSum a.dims := fun h =>
    ht.2 (by rw [h, strandsEq f]; exact dimSum_mem_boundaries b.dims)
  obtain ⟨l, r, p, q, ha, hl⟩ := exists_split_of_mem_boundaries a.dims ht.1 h0 hlast
  refine ⟨zObj (l ++ (p + q) :: r), ?_, by rw [zObj_dims, ha]; exact (dimSum_cut l r p q).symm⟩
  rw [zObj_dims, ha, boundaries_cut, hl,
    Finset.erase_insert (hl ▸ notMem_boundaries_cut l r p q)]

/-- **A refinement splits off its first cut at any boundary it removes.**  Uniqueness is
`mid_eq_of_cuts_eq` and `factor_ext`. -/
theorem exists_factor_first (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ (c : Ch Zbp) (e : a ⟶ c) (g : c ⟶ b), cutsOf e = {t} ∧ e ≫ g = f := by
  obtain ⟨c, hc, hcd⟩ := exists_mid_merge f ht
  have ht' := Finset.mem_sdiff.mp ht
  have hd := strandsEq f
  obtain ⟨e, g, heg⟩ := exists_factor
    (nonempty_hom_iff.mpr ⟨hcd.symm, hc ▸ Finset.erase_subset _ _⟩)
    (nonempty_hom_iff.mpr ⟨by omega,
      hc ▸ Finset.subset_erase.mpr ⟨boundaries_subset_of_hom f, ht'.2⟩⟩) f
  exact ⟨c, e, g, cutsOf_eq_singleton ht'.1 hc, heg⟩

/-- **A refinement of positive codimension splits off a generator at the front.** -/
theorem exists_first (f : a ⟶ b) (hf : codim f ≠ 0) :
    ∃ (c : Ch Zbp) (e : a ⟶ c) (g : c ⟶ b), codim e = 1 ∧ e ≫ g = f := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ cutsOf f := Finset.card_pos.mp (by rw [card_cutsOf]; omega)
  obtain ⟨c, e, g, hcut, heg⟩ := exists_factor_first f ht
  exact ⟨c, e, g, codim_eq_one_of_cutsOf hcut, heg⟩

/-- **Two consecutive one-cut steps re-factor with their cuts exchanged** — split the *second*
cut off the front of the composite; erasing commutes, so what is left removes the first. -/
theorem exists_swap {c : Ch Zbp} {e₀ : a ⟶ c} {e₁ : c ⟶ b} {t₀ t₁ : ℕ}
    (h₀ : cutsOf e₀ = {t₀}) (h₁ : cutsOf e₁ = {t₁}) :
    ∃ (c' : Ch Zbp) (u : a ⟶ c') (v : c' ⟶ b),
      cutsOf u = {t₁} ∧ cutsOf v = {t₀} ∧ u ≫ v = e₀ ≫ e₁ := by
  have hne : t₀ ≠ t₁ := fun hc => (mem_cutsOf h₀).2 (hc ▸ (mem_cutsOf h₁).1)
  obtain ⟨c', u, v, hu, huv⟩ := exists_factor_first (e₀ ≫ e₁) (by
    rw [cutsOf_comp, h₁]; exact Finset.mem_union_right _ (Finset.mem_singleton_self t₁))
  refine ⟨c', u, v, hu, cutsOf_eq_singleton
    (boundaries_eq_erase hu ▸ Finset.mem_erase.mpr ⟨hne, (mem_cutsOf h₀).1⟩) ?_, huv⟩
  rw [boundaries_eq_erase hu, boundaries_eq_erase h₁, boundaries_eq_erase h₀,
    Finset.erase_right_comm]

/-! ## The generating quiver

An edge runs the way a *path* does — from the coarse shape to the fine one — so that
`eval` lands in `(Ch Zbp)ᵒᵖ`, the form the transport to `Ch K` consumes. -/

namespace Cut

/-- The shapes, as the vertices of the generating quiver. -/
def Vert : Type := Ch Zbp

/-- The shape a vertex names. -/
def Vert.as (x : Vert) : Ch Zbp := x

/-- The vertex a shape names. -/
def Vert.mk (x : Ch Zbp) : Vert := x

theorem Vert.as_injective : Function.Injective Vert.as := fun _ _ h => h

/-- A generating edge — a refinement removing a single boundary, pointing at its fine end. -/
def Gen (x y : Vert) := {f : y.as ⟶ x.as // codim f = 1}

instance : Quiver Vert := ⟨Gen⟩

/-- The generator named by a one-cut refinement.  `show … from` is what crosses the type synonym:
the quiver instance does not unfold at anonymous-constructor transparency. -/
def gen {x y : Vert} (f : y.as ⟶ x.as) (hf : codim f = 1) : x ⟶ y :=
  show Gen x y from ⟨f, hf⟩

/-- The refinement a generator names. -/
def genHom {x y : Vert} (e : x ⟶ y) : y.as ⟶ x.as := (show Gen x y from e).1

theorem codim_genHom {x y : Vert} (e : x ⟶ y) : codim (genHom e) = 1 :=
  (show Gen x y from e).2

/-- Every generator is named, with its codimension split off. -/
theorem exists_gen {x y : Vert} (e : x ⟶ y) :
    ∃ (f : y.as ⟶ x.as) (hf : codim f = 1), e = gen f hf := ⟨genHom e, codim_genHom e, rfl⟩

/-- The generating quiver's inclusion. -/
def evalPre : Vert ⥤q (Ch Zbp)ᵒᵖ where
  obj x := op x.as
  map {_ _} e := (genHom e).op

/-- Evaluation of a generating path — identity on objects. -/
def eval : CategoryTheory.Paths Vert ⥤ (Ch Zbp)ᵒᵖ := Paths.lift evalPre

/-- The refinement a generating path performs: consing an edge *pre*composes. -/
def ev {x y : Vert} (P : Quiver.Path x y) : y.as ⟶ x.as := (eval.map P).unop

@[simp] theorem ev_nil {x : Vert} : ev (Quiver.Path.nil : Quiver.Path x x) = 𝟙 x.as := rfl

@[simp] theorem ev_cons {x y z : Vert} (P : Quiver.Path x y) (e : y ⟶ z) :
    ev (P.cons e) = genHom e ≫ ev P := rfl

theorem eval_map_eq_iff {x y : Vert} {P Q : Quiver.Path x y} :
    eval.map P = eval.map Q ↔ ev P = ev Q :=
  ⟨congrArg Quiver.Hom.unop, fun h => Quiver.Hom.unop_inj h⟩

theorem codim_ev {x y : Vert} (P : Quiver.Path x y) : codim (ev P) = P.length := by
  induction P with
  | nil => exact codim_id _
  | cons P e ih =>
      rw [ev_cons, codim_comp, codim_genHom, ih]
      exact Nat.add_comm _ _

theorem length_eq_of_ev_eq {x y : Vert} {P Q : Quiver.Path x y} (h : ev P = ev Q) :
    P.length = Q.length := by rw [← codim_ev, ← codim_ev, h]

/-- **The one-cut refinements generate.**  Peel a generator off the front and induct on the
codimension; a codimension-zero refinement is an identity. -/
theorem exists_path : ∀ (n : ℕ) {a b : Ch Zbp} (f : a ⟶ b), codim f ≤ n →
    ∃ P : Quiver.Path (Vert.mk b) (Vert.mk a), ev P = f := by
  intro n
  induction n with
  | zero =>
      intro a b f hf
      obtain rfl : a = b := (codim_eq_zero_iff f).mp (Nat.le_zero.mp hf)
      exact ⟨Quiver.Path.nil, (endo_eq_id f).symm⟩
  | succ n ih =>
      intro a b f hf
      rcases Nat.eq_zero_or_pos (codim f) with h0 | hpos
      · exact ih f (by omega)
      · obtain ⟨c, e, g, he, heg⟩ := exists_first f (by omega)
        have hc : codim g ≤ n := by
          have := codim_comp e g
          rw [heg, he] at this
          omega
        obtain ⟨P, hP⟩ := ih g hc
        exact ⟨P.cons (gen (x := Vert.mk c) (y := Vert.mk a) e he), by rw [ev_cons, hP]; exact heg⟩

/-! ### The relation -/

/-- **The codimension-two relation**: two two-step factorisations of one refinement.  A path of
length two *is* a two-step factorisation, so nothing more need be said. -/
def rel : HomRel (CategoryTheory.Paths Vert) := fun _ _ P Q =>
  P.length = 2 ∧ Q.length = 2 ∧ ev P = ev Q

/-- The passage to the quotient. -/
noncomputable abbrev quotF : CategoryTheory.Paths Vert ⥤ CategoryTheory.Quotient rel :=
  Quotient.functor rel

theorem quot_cons {x y z : Vert} (P : Quiver.Path x y) (e : y ⟶ z) :
    quotF.map (P.cons e) = quotF.map P ≫ quotF.map e.toPath :=
  quotF.map_comp P e.toPath

/-- The relation, as an identity between two-step composites in the quotient. -/
theorem quot_swap {x y : Vert} {c c' : Ch Zbp} {e₀ : c ⟶ x.as} {e₁ : y.as ⟶ c}
    {u : c' ⟶ x.as} {v : y.as ⟶ c'} (h₀ : codim e₀ = 1) (h₁ : codim e₁ = 1)
    (hu : codim u = 1) (hv : codim v = 1) (h : e₁ ≫ e₀ = v ≫ u) :
    quotF.map (gen (x := x) (y := Vert.mk c) e₀ h₀).toPath
        ≫ quotF.map (gen (x := Vert.mk c) (y := y) e₁ h₁).toPath
      = quotF.map (gen (x := x) (y := Vert.mk c') u hu).toPath
        ≫ quotF.map (gen (x := Vert.mk c') (y := y) v hv).toPath := by
  rw [← quotF.map_comp, ← quotF.map_comp]
  refine CategoryTheory.Quotient.sound _ ⟨rfl, rfl, ?_⟩
  change e₁ ≫ e₀ ≫ 𝟙 x.as = v ≫ u ≫ 𝟙 x.as
  rw [Category.comp_id, Category.comp_id, h]

/-! ## Sorting a generating path -/

/-- **The lowest cut can be split off first** — sorting a generating path so that its first step
cuts at a position no other cut of the path is below. -/
theorem exists_min_first : ∀ (n : ℕ) {x y : Vert} (P : Quiver.Path x y), P.length = n + 1 →
    ∃ (z : Vert) (R : Quiver.Path x z) (e : y.as ⟶ z.as) (he : codim e = 1) (t : ℕ),
      cutsOf e = {t} ∧ (∀ s ∈ cutsOf (ev P), t ≤ s) ∧ R.length + 1 = P.length ∧
        e ≫ ev R = ev P ∧ quotF.map P = quotF.map (R.cons (gen e he)) := by
  intro n
  induction n with
  | zero =>
      intro x y P hP
      cases P with
      | nil => simp at hP
      | cons P' e =>
          cases P' with
          | cons P'' d => simp at hP
          | nil =>
              obtain ⟨e₁, he₁, rfl⟩ := exists_gen e
              obtain ⟨t, ht⟩ := exists_cutsOf_eq_singleton he₁
              have hev : ev (Quiver.Path.nil.cons (gen e₁ he₁)) = e₁ := Category.comp_id e₁
              refine ⟨x, Quiver.Path.nil, e₁, he₁, t, ht, fun s hs => ?_, rfl, hev, rfl⟩
              rw [hev, ht] at hs
              exact (Finset.mem_singleton.mp hs).ge
  | succ n ih =>
      intro x y P hP
      cases P with
      | nil => simp at hP
      | cons P' e =>
          obtain ⟨e₁, he₁, rfl⟩ := exists_gen e
          have hP' : P'.length = n + 1 := by simpa using hP
          obtain ⟨z₀, R', e₀, he₀, t₀, hcut₀, hmin₀, hlen₀, hcomp₀, hquot₀⟩ := ih P' hP'
          obtain ⟨t₁, ht₁⟩ := exists_cutsOf_eq_singleton he₁
          have hcuts : cutsOf (ev (P'.cons (gen e₁ he₁))) = cutsOf e₁ ∪ cutsOf (ev P') :=
            cutsOf_comp e₁ (ev P')
          have hbound : ∀ t : ℕ, (∀ u ∈ cutsOf (ev P'), t ≤ u) → t ≤ t₁ →
              ∀ s ∈ cutsOf (ev (P'.cons (gen e₁ he₁))), t ≤ s := by
            intro t hP₀ ht₁' s hs
            rw [hcuts, Finset.mem_union, ht₁, Finset.mem_singleton] at hs
            rcases hs with rfl | hs
            · exact ht₁'
            · exact hP₀ s hs
          rcases le_total t₁ t₀ with hle | hle
          · exact ⟨_, P', e₁, he₁, t₁, ht₁,
              hbound t₁ (fun u hu => hle.trans (hmin₀ u hu)) le_rfl, rfl, rfl, rfl⟩
          obtain ⟨c', u, v, hu, hv, huv⟩ := exists_swap ht₁ hcut₀
          have hu' := codim_eq_one_of_cutsOf hu
          have hv' := codim_eq_one_of_cutsOf hv
          refine ⟨Vert.mk c', R'.cons (gen v hv'), u, hu', t₀, hu,
            hbound t₀ hmin₀ hle, by simpa using hlen₀, ?_, ?_⟩
          · calc u ≫ ev (R'.cons (gen v hv'))
                = (u ≫ v) ≫ ev R' := (Category.assoc _ _ _).symm
              _ = (e₁ ≫ e₀) ≫ ev R' := congrArg (fun n => n ≫ ev R') huv
              _ = e₁ ≫ e₀ ≫ ev R' := Category.assoc _ _ _
              _ = ev (P'.cons (gen e₁ he₁)) := congrArg (fun n => e₁ ≫ n) hcomp₀
          · calc quotF.map (P'.cons (gen e₁ he₁))
                = quotF.map (R'.cons (gen e₀ he₀)) ≫ quotF.map (gen e₁ he₁).toPath := by
                  rw [quot_cons, hquot₀]
              _ = quotF.map R' ≫ (quotF.map (gen e₀ he₀).toPath
                    ≫ quotF.map (gen e₁ he₁).toPath) := by rw [quot_cons, Category.assoc]
              -- `congrArg`, not `rw`: the middle vertex is spelled `Vert.mk c'` in `quot_swap`
              -- and `c'` here, which are defeq but not syntactically equal
              _ = quotF.map R' ≫ (quotF.map (gen v hv').toPath
                    ≫ quotF.map (gen u hu').toPath) :=
                  congrArg (fun n => quotF.map R' ≫ n) (quot_swap he₀ he₁ hv' hu' huv.symm)
              _ = quotF.map ((R'.cons (gen v hv')).cons (gen u hu')) := by
                  rw [quot_cons (R'.cons (gen v hv')) (gen u hu'), quot_cons R' (gen v hv'),
                    Category.assoc]

/-- **Two generating paths with the same value agree in the quotient.**  Sort both; the two first
steps then cut at the same boundary, so they — and everything after them — coincide. -/
theorem quot_eq_of_ev_eq : ∀ (n : ℕ) {x y : Vert} (P Q : Quiver.Path x y),
    P.length = n → ev P = ev Q → quotF.map P = quotF.map Q := by
  intro n
  induction n with
  | zero =>
      intro x y P Q hP h
      have hQ : Q.length = 0 := (length_eq_of_ev_eq h).symm.trans hP
      cases P with
      | cons P' e => simp at hP
      | nil =>
          cases Q with
          | cons Q' d => simp at hQ
          | nil => rfl
  | succ n ih =>
      intro x y P Q hP h
      have hQ : Q.length = n + 1 := (length_eq_of_ev_eq h).symm.trans hP
      obtain ⟨z, R, e, he, t, hcut, hmin, hlenR, hcompR, hquotP⟩ := exists_min_first n P hP
      obtain ⟨z', S, d, hd, t', hcut', hmin', -, hcompS, hquotQ⟩ := exists_min_first n Q hQ
      have hcompS' : d ≫ ev S = ev P := hcompS.trans h.symm
      have htmem : t ∈ cutsOf (ev P) := by
        rw [← hcompR, cutsOf_comp, hcut]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self t)
      have ht'mem : t' ∈ cutsOf (ev Q) := by
        rw [← hcompS, cutsOf_comp, hcut']
        exact Finset.mem_union_left _ (Finset.mem_singleton_self t')
      obtain rfl : t = t' :=
        Nat.le_antisymm (hmin t' (by rw [h]; exact ht'mem)) (hmin' t (by rw [← h]; exact htmem))
      obtain rfl : z = z' := Vert.as_injective (mid_eq_of_cuts_eq hcut hcut')
      obtain ⟨rfl, hRS⟩ := factor_ext hcompR hcompS'
      rw [hquotP, hquotQ, quot_cons, quot_cons, ih R S (by omega) hRS]

/-! ## The presentation -/

/-- **The presentation functor**: evaluate a generating path, on the quotient. -/
noncomputable def presentationFunctor : CategoryTheory.Quotient rel ⥤ (Ch Zbp)ᵒᵖ :=
  CategoryTheory.Quotient.lift rel eval fun _ _ _ _ h => eval_map_eq_iff.mpr h.2.2

instance : presentationFunctor.Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨P, hP⟩ := exists_path (codim f.unop) f.unop le_rfl
    exact ⟨quotF.map P, Quiver.Hom.unop_inj hP⟩

instance : presentationFunctor.Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ f g hfg
    obtain ⟨P, rfl⟩ := quotF.map_surjective f
    obtain ⟨Q, rfl⟩ := quotF.map_surjective g
    exact quot_eq_of_ev_eq _ P Q rfl (eval_map_eq_iff.mp hfg)

instance : presentationFunctor.EssSurj where
  mem_essImage X := ⟨{ as := Vert.mk X.unop }, ⟨Iso.refl X⟩⟩

instance : presentationFunctor.IsEquivalence where

end Cut

/-- **`Ch Zbp` is presented by its bead cuts** — generators the codimension-one refinements,
relations the codimension-two ones, identity on objects.  It is the *opposite* that a path
presents: a path spells its steps in refinement order only there. -/
noncomputable def zPresentationOp : CategoryTheory.Quotient Cut.rel ≌ (Ch Zbp)ᵒᵖ :=
  Cut.presentationFunctor.asEquivalence

@[simp] theorem zPresentationOp_obj (a : Ch Zbp) :
    zPresentationOp.functor.obj { as := Cut.Vert.mk a } = op a := rfl

end ChainCat
