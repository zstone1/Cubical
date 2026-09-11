import CubeChains.Concurrency.Presentation.RunReduce
import CubeChains.Concurrency.Presentation.ArtinDegreeZero

/-!
# Concurrency/Presentation/ArtinCells — the degree-zero cells suffice

`Spans`' dimension-two half at `T₂` = the codimension-two cuts out of a run.  Out of a run a
codimension-one step is the merge or the atom, so one codimension-two cut has factorisations of
both kinds:

    run ──merge i──▸ atomComp i ──w──▸ d        run ──atom j──▸ atomComp j ──w'──▸ d

The merge contracts to the empty word, so such a cell reads the *second* cut's atom word as the
atoms themselves; the two-atom cell above them is then Artin's relation, with no reduced-word
uniqueness anywhere.  `posGradeLoc` and Matsumoto then derive every other 2-cell.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

/-! ## The sub-polygraph at degree zero -/

/-- **The 2-cells to keep**: the codimension-two cuts out of a run. -/
def OutOfRunCell {X Y : GenObj zCutContraction.poly.Gen} (α : zCutContraction.poly.Rel X Y) :
    Prop :=
  zCutContraction.rep α.cod.as = α.cod.as

/-- **The `N−1` atoms at each run, with the degree-zero codimension-two cells.** -/
noncomputable def zAtomPoly : Polygraph :=
  Polygraph.sub (P := zCutContraction.poly) OutOfRun OutOfRunCell runWord all_runWord

/-- Reading a word of the contracted polygraph in the sub-polygraph. -/
noncomputable def subF : zCutContraction.poly.Word ⥤ zAtomPoly.presented :=
  Paths.lift (subPre (P := zCutContraction.poly) OutOfRun runWord all_runWord) ⋙ zAtomPoly.quot

/-- **A codimension-two cut out of a run holds in the sub-polygraph** — that is what its 2-cells
are. -/
theorem subF_cell {u v : GenObj (chCutLocFunctor.obj Zbp).Gen}
    (α : (chCutLocFunctor.obj Zbp).Rel u v) (hv : zCutContraction.rep v.as = v.as) :
    subF.map (zCutContraction.words.map ((chCutLocFunctor.obj Zbp).src α))
      = subF.map (zCutContraction.words.map ((chCutLocFunctor.obj Zbp).tgt α)) :=
  zAtomPoly.quot_src_tgt (x := ⟨(zCutContraction.repObj u).as⟩)
    (y := ⟨(zCutContraction.repObj v).as⟩) ⟨⟨u, v, α, rfl, rfl⟩, hv⟩

/-! ## Reading the bead cuts there

A letter of the lifted cut polygraph contracts to the empty word when it is a merge and to its own
1-cell otherwise; `cutArrow` is what it names either way. -/

/-- Consing a letter is composing with it. -/
private theorem map_cons {V : Type*} [Quiver V] {D : Type*} [Category D] (F : Paths V ⥤ D)
    {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    F.map (p.cons e) = F.map p ≫ F.map e.toPath := F.map_comp p e.toPath

/-- Reading a word of the lifted cut polygraph in the sub-polygraph. -/
noncomputable def cutF : (chCutPoly Zbp).Word ⥤ zAtomPoly.presented :=
  (Polygraph.fwdPre (chCutPoly Zbp) zEltPicked).pathsFunctor ⋙ zCutContraction.words ⋙ subF

/-- The arrow a bead cut names there. -/
noncomputable def cutArrow {z z' : (chCutPoly Zbp).V} (e : (chCutPoly Zbp).Gen z z') :
    cutF.obj ((chCutPoly Zbp).pt z) ⟶ cutF.obj ((chCutPoly Zbp).pt z') :=
  cutF.map (Polygraph.cell e).toPath

/-- **A 2-cell of the lifted cut polygraph out of a run holds in the sub-polygraph.** -/
theorem cutF_cell {u v : (chCutPoly Zbp).V} (α : (chCutPoly Zbp).Rel ⟨u⟩ ⟨v⟩)
    (hv : zCutContraction.rep v = v) :
    cutF.map ((chCutPoly Zbp).src α) = cutF.map ((chCutPoly Zbp).tgt α) :=
  subF_cell (Polygraph.InvRel.keep (P := chCutPoly Zbp) (S := zEltPicked) α) hv

/-- A two-letter word is the two arrows. -/
private theorem cutF_two {a b c : (chCutPoly Zbp).V} (f : (chCutPoly Zbp).Gen a b)
    (g : (chCutPoly Zbp).Gen b c) :
    cutF.map ((Quiver.Path.nil.cons (Polygraph.cell f)).cons (Polygraph.cell g))
      = cutArrow f ≫ cutArrow g := by
  have hnil : cutF.map (Quiver.Path.nil : Quiver.Path ((chCutPoly Zbp).pt a)
      ((chCutPoly Zbp).pt a)) = 𝟙 _ := cutF.map_id _
  rw [map_cons, map_cons, hnil, Category.id_comp]
  rfl

/-- Two two-step factorisations of one codimension-two refinement, as a 2-cell. -/
noncomputable def pairCell {z zm zm' zd : (chCutPoly Zbp).V}
    (e₁ : (chCutPoly Zbp).Gen zd zm) (e₂ : (chCutPoly Zbp).Gen zm z)
    (e₁' : (chCutPoly Zbp).Gen zd zm') (e₂' : (chCutPoly Zbp).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1) :
    (chCutPoly Zbp).Rel ⟨zd⟩ ⟨z⟩ where
  src := (Quiver.Path.nil.cons (Polygraph.cell e₁)).cons (Polygraph.cell e₂)
  tgt := (Quiver.Path.nil.cons (Polygraph.cell e₁')).cons (Polygraph.cell e₂')
  cell :=
    { src := (Quiver.Path.nil.cons e₁.1).cons e₂.1
      tgt := (Quiver.Path.nil.cons e₁'.1).cons e₂'.1
      src_length := rfl
      tgt_length := rfl
      ev_eq := by simpa using hev }
  src_eq := rfl
  tgt_eq := rfl

/-- **Two two-step factorisations of one codimension-two cut out of a run spell one word.** -/
theorem cutArrow_pair {z zm zm' zd : (chCutPoly Zbp).V} (hz : zCutContraction.rep z = z)
    (e₁ : (chCutPoly Zbp).Gen zd zm) (e₂ : (chCutPoly Zbp).Gen zm z)
    (e₁' : (chCutPoly Zbp).Gen zd zm') (e₂' : (chCutPoly Zbp).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1) :
    cutArrow e₁ ≫ cutArrow e₂ = cutArrow e₁' ≫ cutArrow e₂' := by
  refine (cutF_two e₁ e₂).symm.trans (Eq.trans ?_ (cutF_two e₁' e₂'))
  exact cutF_cell (pairCell e₁ e₂ e₁' e₂' hev) hz

/-! ## A letter, contracted

A merge contracts to the empty word; any other letter contracts to its own 1-cell, and that 1-cell
is pinned by its cell data, the two representative equations being propositions. -/

/-- The letter a codimension-one cut between two 0-cells is. -/
noncomputable def cutOf {z z' : (chCutPoly Zbp).V} (f : zSh z' ⟶ zSh z) (hf : codim f = 1) :
    (chCutPoly Zbp).Gen z z' := zEltGen ⟨f, hf⟩

@[simp] theorem genHom_cutOf {z z' : (chCutPoly Zbp).V} (f : zSh z' ⟶ zSh z) (hf : codim f = 1) :
    Cut.genHom (cutOf f hf).1 = f := rfl

theorem cutArrow_eq {z z' : (chCutPoly Zbp).V} (e : (chCutPoly Zbp).Gen z z') :
    cutArrow e
      = subF.map (zCutContraction.cell (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e)) := by
  change subF.map (zCutContraction.words.map
    ((Polygraph.fwdPre (chCutPoly Zbp) zEltPicked).mapPath (Polygraph.cell e).toPath)) = _
  rw [Prefunctor.mapPath_toPath]
  exact congrArg subF.map
    (Paths.lift_toPath zCutContraction.pre (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e))

/-- The arrow a 1-cell of the contraction names in the sub-polygraph. -/
noncomputable def subArrow {u v : zCutContraction.V} (g : zCutContraction.Gen u v) :
    subF.obj (zCutContraction.poly.pt u) ⟶ subF.obj (zCutContraction.poly.pt v) :=
  subF.map (Polygraph.cell (P := zCutContraction.poly) g).toPath

/-- A renaming on either side of an identity. -/
private theorem eqToHom_sandwich_id {C : Type*} [Category C] {A B X : C} (h₁ : A = X) (h₂ : X = B)
    {f : X ⟶ X} (hf : f = 𝟙 X) (h : A = B) : eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom h := by
  subst h₁; subst h₂; rw [hf]; simp

/-- **A merge names a renaming.** -/
theorem cutArrow_merge {z z' : (chCutPoly Zbp).V} (e : (chCutPoly Zbp).Gen z z')
    (he : zEltPicked e) (h : cutF.obj ((chCutPoly Zbp).pt z) = cutF.obj ((chCutPoly Zbp).pt z')) :
    cutArrow e = eqToHom h := by
  rw [cutArrow_eq,
    zCutContraction.cell_of_S (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e) he]
  refine Eq.trans (Paths.map_cellCongr₂ subF _ _ _) ?_
  exact eqToHom_sandwich_id _ _ (subF.map_id _) h

/-- **…and any other letter is its own 1-cell of the contraction.** -/
theorem cutArrow_gen {z z' : (chCutPoly Zbp).V} (e : (chCutPoly Zbp).Gen z z')
    (he : ¬ zEltPicked e) :
    cutArrow e = subArrow (zCutContraction.genCell
      (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e) he) := by
  rw [cutArrow_eq,
    zCutContraction.cell_of_not_S (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e) he]
  rfl

/-- **A 1-cell of the contraction is pinned by its cell data.** -/
theorem gen_eq {X Y X' Y' : zCutContraction.V} (g : zCutContraction.Gen X Y)
    (g' : zCutContraction.Gen X' Y') (hd : g.dom = g'.dom) (hc : g.cod = g'.cod)
    (hg : g.gen ≍ g'.gen) : X = X' ∧ Y = Y' ∧ g ≍ g' := by
  obtain ⟨d, c, gen, hnm, r1, r2⟩ := g
  obtain ⟨d', c', gen', hnm', r1', r2'⟩ := g'
  simp only at hd hc
  subst hd; subst hc
  obtain rfl := eq_of_heq hg
  obtain rfl : X = X' := Subtype.ext (r1.symm.trans r1')
  obtain rfl : Y = Y' := Subtype.ext (r2.symm.trans r2')
  exact ⟨rfl, rfl, HEq.rfl⟩

/-- …so two such 1-cells name one arrow, up to the renaming of their 0-cells. -/
theorem subArrow_heq {X Y X' Y' : zCutContraction.V} {g : zCutContraction.Gen X Y}
    {g' : zCutContraction.Gen X' Y'} (hX : X = X') (hY : Y = Y') (hg : g ≍ g')
    (h1 : subF.obj (zCutContraction.poly.pt X) = subF.obj (zCutContraction.poly.pt X'))
    (h2 : subF.obj (zCutContraction.poly.pt Y') = subF.obj (zCutContraction.poly.pt Y)) :
    subArrow g = eqToHom h1 ≫ subArrow g' ≫ eqToHom h2 := by
  subst hX; subst hY
  obtain rfl := eq_of_heq hg
  simp

/-! ## Everything at one run

Every 0-cell in sight represents the run on its own events, so a word of cuts is read there. -/

/-- **A 0-cell of the lifted polygraph represents the run on its own events.** -/
theorem repObj_as_eq (x : zCutContraction.V) {z : (chCutPoly Zbp).V}
    (hz : dimSum (zSh z).dims = vStrands x) :
    (zCutContraction.repObj (⟨z⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x :=
  Subtype.ext (zEltV_ext (by
    change zObj (𝟙^(dimSum (zSh z).dims)) = zSh x.1
    rw [hz, zSh_eq_ones x]))

/-- The object a 0-cell names in the sub-polygraph. -/
noncomputable abbrev aObj (u : zCutContraction.V) : zAtomPoly.presented :=
  subF.obj (zCutContraction.poly.pt u)

/-- Conjugating a composite by renamings. -/
private theorem eqToHom_conj_comp {C : Type*} [Category C] {A B D E : C} (h₁ : A = E) (h₂ : B = E)
    (h₃ : D = E) (f : A ⟶ B) (g : B ⟶ D) :
    eqToHom h₁.symm ≫ (f ≫ g) ≫ eqToHom h₃
      = (eqToHom h₁.symm ≫ f ≫ eqToHom h₂) ≫ (eqToHom h₂.symm ≫ g ≫ eqToHom h₃) := by
  subst h₁; subst h₂; subst h₃; simp

/-- …and a renaming by renamings. -/
private theorem eqToHom_conj_id {C : Type*} [Category C] {A B E : C} (h₁ : A = E) (h₂ : B = E)
    (h : A = B) : eqToHom h₁.symm ≫ eqToHom h ≫ eqToHom h₂ = 𝟙 E := by
  subst h₁; subst h; simp

/-- An arrow of cuts, read at the run its two ends represent. -/
noncomputable def atX (x : zCutContraction.V) {z z' : (chCutPoly Zbp).V}
    (hz : (zCutContraction.repObj (⟨z⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (hz' : (zCutContraction.repObj (⟨z'⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (f : cutF.obj ((chCutPoly Zbp).pt z) ⟶ cutF.obj ((chCutPoly Zbp).pt z')) :
    aObj x ⟶ aObj x :=
  eqToHom (congrArg aObj hz).symm ≫ f ≫ eqToHom (congrArg aObj hz')

theorem atX_comp (x : zCutContraction.V) {z z' z'' : (chCutPoly Zbp).V}
    (hz : (zCutContraction.repObj (⟨z⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (hz' : (zCutContraction.repObj (⟨z'⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (hz'' : (zCutContraction.repObj (⟨z''⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (f : cutF.obj ((chCutPoly Zbp).pt z) ⟶ cutF.obj ((chCutPoly Zbp).pt z'))
    (g : cutF.obj ((chCutPoly Zbp).pt z') ⟶ cutF.obj ((chCutPoly Zbp).pt z'')) :
    atX x hz hz'' (f ≫ g) = atX x hz hz' f ≫ atX x hz' hz'' g :=
  eqToHom_conj_comp (congrArg aObj hz) (congrArg aObj hz') (congrArg aObj hz'') f g

theorem atX_eqToHom (x : zCutContraction.V) {z z' : (chCutPoly Zbp).V}
    (hz : (zCutContraction.repObj (⟨z⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (hz' : (zCutContraction.repObj (⟨z'⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (h : cutF.obj ((chCutPoly Zbp).pt z) = cutF.obj ((chCutPoly Zbp).pt z')) :
    atX x hz hz' (eqToHom h) = 𝟙 (aObj x) :=
  eqToHom_conj_id (congrArg aObj hz) (congrArg aObj hz') h

/-- Undoing a conjugation by renamings. -/
private theorem eqToHom_unconj {C : Type*} [Category C] {A B E : C} (h₁ : A = E) (h₂ : B = E)
    (f : E ⟶ E) : eqToHom h₁.symm ≫ (eqToHom h₁ ≫ f ≫ eqToHom h₂.symm) ≫ eqToHom h₂ = f := by
  subst h₁; subst h₂; simp

theorem repObj_x (x : zCutContraction.V) :
    (zCutContraction.repObj (⟨x.1⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x :=
  repObj_as_eq x rfl

/-- **A non-merge letter names the 1-cell it is, read at the run.** -/
theorem atX_cutArrow_gen (x : zCutContraction.V) {z z' : (chCutPoly Zbp).V}
    (e : (chCutPoly Zbp).Gen z z') (he : ¬ zEltPicked e)
    (hz : (zCutContraction.repObj (⟨z⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (hz' : (zCutContraction.repObj (⟨z'⟩ : GenObj (chCutLocFunctor.obj Zbp).Gen)).as = x)
    (g : zCutContraction.Gen x x) (hd : g.dom = z) (hc : g.cod = z')
    (hg : g.gen ≍ Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e) :
    atX x hz hz' (cutArrow e) = subArrow g := by
  obtain ⟨hX, hY, hgg⟩ :=
    gen_eq (zCutContraction.genCell (Polygraph.fwdCell (chCutPoly Zbp) zEltPicked e) he) g
      hd.symm hc.symm hg.symm
  rw [cutArrow_gen e he, subArrow_heq hX hY hgg (congrArg aObj hX) (congrArg aObj hY).symm]
  exact eqToHom_unconj (congrArg aObj hX) (congrArg aObj hY) (subArrow g)

/-! ## The word a cut spells at the run

A 1-cell names the atom word of its crossing permutation; at an atom that word is one letter, by
injectivity of `adjT`. -/

theorem subArrow_eq_quot {u v : zCutContraction.V} (g : zCutContraction.Gen u v) :
    subArrow g = zAtomPoly.quot.map (keptWord (P := zCutContraction.poly) OutOfRun
      (runWord g) (all_runWord g)) :=
  congrArg zAtomPoly.quot.map
    (Paths.lift_toPath (subPre (P := zCutContraction.poly) OutOfRun runWord all_runWord)
      (Polygraph.cell (P := zCutContraction.poly) g))

/-- The arrow the chosen atom word of a permutation names at a run. -/
noncomputable def permArrow (x : zCutContraction.V) (τ : Equiv.Perm (Fin (vStrands x))) :
    aObj x ⟶ aObj x :=
  zAtomPoly.quot.map (keptWord (P := zCutContraction.poly) OutOfRun
    (atomPath x (exists_atomWord (vStrands x) τ).choose Quiver.Path.nil)
    (all_atomPath x _ _ (Quiver.Path.all_nil _)))

/-- **An atom's chosen word is that atom** — a one-letter word names its own index. -/
theorem choose_atomWord_adjT (N : ℕ) (k : Fin (N - 1)) :
    (exists_atomWord N (adjT k)).choose = [k] := by
  obtain ⟨hlen, hfold, -⟩ := (exists_atomWord N (adjT k)).choose_spec
  obtain ⟨k', hk'⟩ := List.length_eq_one_iff.mp (hlen.trans (permLen_adjT k))
  rw [hk'] at hfold ⊢
  simp only [List.foldl_cons, List.foldl_nil, one_mul] at hfold
  rw [adjT_injective hfold]

/-- Which word `keptWord` reads matters, which proof does not. -/
private theorem keptWord_eq {X Y : GenObj zCutContraction.poly.Gen} {u v : Quiver.Path X Y}
    (h : u = v) (hu : Quiver.Path.All (fun ⦃_ _⦄ e => OutOfRun e) u)
    (hv : Quiver.Path.All (fun ⦃_ _⦄ e => OutOfRun e) v) :
    keptWord (P := zCutContraction.poly) OutOfRun u hu
      = keptWord (P := zCutContraction.poly) OutOfRun v hv := by
  subst h; rfl

theorem permArrow_adjT (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    permArrow x (adjT k) = subArrow (atomCell x k) := by
  have hpath : atomPath x (exists_atomWord (vStrands x) (adjT k)).choose Quiver.Path.nil
      = runWord (atomCell x k) := by
    rw [choose_atomWord_adjT]
    exact (runWord_self (atomCell x k) (outOfRun_atomCell x k)).symm
  rw [subArrow_eq_quot, permArrow]
  exact congrArg zAtomPoly.quot.map (keptWord_eq hpath _ _)

/-- **Every 1-cell at a run names the word its crossing permutation spells.** -/
theorem subArrow_eq_permArrow {x : zCutContraction.V} (g : zCutContraction.Gen x x) :
    subArrow g = permArrow x (genPerm g) := by
  by_cases hg : OutOfRun g
  · obtain ⟨k, rfl⟩ := exists_atomCell g hg
    rw [show genPerm (atomCell x k) = adjT k from crossPerm_atomCell x k, permArrow_adjT]
  · have hw : runWord g
        = atomPath x (exists_atomWord (vStrands x) (genPerm g)).choose Quiver.Path.nil := by
      have h0 : runWord g = cellCongr Quiver.Path rfl
          (congrArg zCutContraction.poly.pt (eq_of_gen g))
          (atomPath x (exists_atomWord (vStrands x) (genPerm g)).choose Quiver.Path.nil) :=
        dif_neg hg
      rw [h0, cellCongr_self]
    rw [subArrow_eq_quot, permArrow]
    exact congrArg zAtomPoly.quot.map (keptWord_eq hw _ _)

/-! ## The cuts above one run

A cut out of the run names an atom or nothing; a cut between two chains above it names the word its
crossing permutation spells. -/

/-- The letter a codimension-one cut out of a 0-cell's run is. -/
noncomputable def runCut (x : zCutContraction.V) {c : Ch Zbp}
    (f : zObj (𝟙^(vStrands x)) ⟶ c) (hf : codim f = 1) :
    (chCutPoly Zbp).Gen (zEltV c) x.1 :=
  cutOf (eqToHom (zSh_eq_ones x) ≫ f) ((codim_eqToHom_comp _ _).trans hf)

/-- The arrow it names at the run. -/
noncomputable def outArrow (x : zCutContraction.V) {c : Ch Zbp}
    (f : zObj (𝟙^(vStrands x)) ⟶ c) (hf : codim f = 1) (hc : dimSum c.dims = vStrands x) :
    aObj x ⟶ aObj x :=
  atX x (repObj_as_eq x hc) (repObj_x x) (cutArrow (runCut x f hf))

/-- …and the arrow a cut between two chains above the run names. -/
noncomputable def midArrow (x : zCutContraction.V) {p q : Ch Zbp} (f : p ⟶ q) (hf : codim f = 1)
    (hp : dimSum p.dims = vStrands x) (hq : dimSum q.dims = vStrands x) :
    aObj x ⟶ aObj x :=
  atX x (repObj_as_eq x hq) (repObj_as_eq x hp)
    (cutArrow (cutOf (z := zEltV q) (z' := zEltV p) f hf))

/-- **Two two-step factorisations of one codimension-two cut out of a run spell one word.** -/
theorem arrow_pair (x : zCutContraction.V) {d m m' : Ch Zbp}
    {a : zObj (𝟙^(vStrands x)) ⟶ m} (ha : codim a = 1) {b : m ⟶ d} (hb : codim b = 1)
    {a' : zObj (𝟙^(vStrands x)) ⟶ m'} (ha' : codim a' = 1) {b' : m' ⟶ d} (hb' : codim b' = 1)
    (hm : dimSum m.dims = vStrands x) (hm' : dimSum m'.dims = vStrands x)
    (hd : dimSum d.dims = vStrands x) (heq : a ≫ b = a' ≫ b') :
    midArrow x b hb hm hd ≫ outArrow x a ha hm
      = midArrow x b' hb' hm' hd ≫ outArrow x a' ha' hm' := by
  rw [midArrow, outArrow, midArrow, outArrow,
    ← atX_comp x (repObj_as_eq x hd) (repObj_as_eq x hm) (repObj_x x),
    ← atX_comp x (repObj_as_eq x hd) (repObj_as_eq x hm') (repObj_x x)]
  refine congrArg (atX x (repObj_as_eq x hd) (repObj_x x)) (cutArrow_pair x.2 _ _ _ _ ?_)
  simp only [runCut, genHom_cutOf, Category.assoc]
  exact congrArg (fun t => eqToHom (zSh_eq_ones x) ≫ t) heq

/-- **A merge out of the run names nothing.** -/
theorem outArrow_merge (x : zCutContraction.V) {c : Ch Zbp}
    (f : zObj (𝟙^(vStrands x)) ⟶ c) (hf : codim f = 1) (hc : dimSum c.dims = vStrands x)
    (hW : W Zbp f) : outArrow x f hf hc = 𝟙 (aObj x) := by
  rw [outArrow, cutArrow_merge (runCut x f hf)
      ((merge_iff _).mpr ⟨(W Zbp).comp_mem _ _ (W_eqToHom _) hW,
        (codim_eqToHom_comp _ _).trans hf⟩)
      (congrArg aObj ((repObj_as_eq x hc).trans (repObj_x x).symm)),
    atX_eqToHom]

/-- **…and the `k`-th atom's cut names the `k`-th atom.** -/
theorem outArrow_atomOnes (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    outArrow x (atomOnes (vStrands x) k) (codim_atomOnes _ _) (dimSum_atomComp _ _)
      = subArrow (atomCell x k) :=
  atX_cutArrow_gen x (runCut x (atomOnes (vStrands x) k) (codim_atomOnes _ _))
    (atomCell x k).not_mem _ _ (atomCell x k) rfl rfl HEq.rfl

/-- The 1-cell a non-merge cut above a run is, at that run. -/
noncomputable def midGen (x : zCutContraction.V) {p q : Ch Zbp} (f : p ⟶ q) (hf : codim f = 1)
    (hne : ¬ merge Zbp f) (hp : dimSum p.dims = vStrands x) (hq : dimSum q.dims = vStrands x) :
    zCutContraction.Gen x x where
  dom := zEltV q
  cod := zEltV p
  gen := Polygraph.fwdCell (chCutPoly Zbp) zEltPicked (cutOf (z := zEltV q) (z' := zEltV p) f hf)
  not_mem := hne
  rep_dom := congrArg Subtype.val (repObj_as_eq x hq)
  rep_cod := congrArg Subtype.val (repObj_as_eq x hp)

/-- **A cut above the run names the word its crossing permutation spells.** -/
theorem midArrow_eq (x : zCutContraction.V) {p q : Ch Zbp} (f : p ⟶ q) (hf : codim f = 1)
    (hne : ¬ merge Zbp f) (hp : dimSum p.dims = vStrands x) (hq : dimSum q.dims = vStrands x) :
    midArrow x f hf hp hq = permArrow x (crossPerm hp f) := by
  rw [midArrow, atX_cutArrow_gen x (cutOf (z := zEltV q) (z' := zEltV p) f hf) hne _ _
      (midGen x f hf hne hp hq) rfl rfl HEq.rfl,
    subArrow_eq_permArrow]
  rfl

/-! ## Artin's two families hold among the atoms

At the degree-two shape a pair of atoms share, the two-step factorisations through the *merge* read
the second cut's word as the two atoms, and the one through both *atoms* is then Artin's relation.
-/

private theorem not_merge_of_crossPerm {p q : Ch Zbp} {N : ℕ} (hp : dimSum p.dims = N)
    (f : p ⟶ q) (h : crossPerm hp f ≠ 1) : ¬ merge Zbp f := fun hm =>
  h ((W_iff_crossPerm_eq_one hp f).mp ((merge_iff f).mp hm).1)

private theorem codim_leg {d : Ch Zbp} (hdeg : degree d = 2) {N : ℕ} {k : Fin (N - 1)}
    (w : zObj (atomComp N k) ⟶ d) : codim w = 1 := by
  rw [codim, hdeg, degree_atomComp]

private theorem adjT_mul_ne_one {n : ℕ} {i j : Fin (n - 1)} (hij : i ≠ j) :
    adjT i * adjT j ≠ 1 := by
  intro h
  refine hij (adjT_injective ?_)
  have h' := congrArg (· * adjT j) h
  simpa [mul_adjT_adjT] using h'

/-- **Two far-apart atoms commute** — the square of the cell their cuts share. -/
theorem subArrow_atomCell_comm (x : zCutContraction.V) {i j : Fin (vStrands x - 1)}
    (hij : (i : ℕ) + 1 < (j : ℕ)) :
    subArrow (atomCell x i) ≫ subArrow (atomCell x j)
      = subArrow (atomCell x j) ≫ subArrow (atomCell x i) := by
  obtain ⟨d, hd, hdeg, hni, hnj⟩ := exists_pairCell i j (by omega)
  obtain ⟨mi, -, hui⟩ := exists_merge_leg i hni
  obtain ⟨mj, -, huj⟩ := exists_merge_leg j hnj
  obtain ⟨wj, hwj⟩ := exists_leg j hd hnj (σ := adjT i)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi, hwi⟩ := exists_leg i hd hni (σ := adjT j)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  have h := arrow_pair x (codim_atomOnes _ i) (codim_leg hdeg wi) (codim_atomOnes _ j)
    (codim_leg hdeg wj) (dimSum_atomComp _ i) (dimSum_atomComp _ j) hd
    (atom_pair_eq (by rw [hwi, hwj]; exact (adjT_comm i j hij).symm))
  rw [midArrow_eq x wi _ (not_merge_of_crossPerm _ wi (by rw [hwi]; exact adjT_ne_one j)),
    midArrow_eq x wj _ (not_merge_of_crossPerm _ wj (by rw [hwj]; exact adjT_ne_one i)),
    outArrow_atomOnes, outArrow_atomOnes, hwi, hwj, permArrow_adjT, permArrow_adjT] at h
  exact h.symm

/-- **Two adjacent atoms braid** — the hexagon of the cell their cuts share, with the two merge
factorisations reading the second cut as a two-letter word. -/
theorem subArrow_atomCell_braid (x : zCutContraction.V) {i j : Fin (vStrands x - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    (subArrow (atomCell x i) ≫ subArrow (atomCell x j)) ≫ subArrow (atomCell x i)
      = (subArrow (atomCell x j) ≫ subArrow (atomCell x i)) ≫ subArrow (atomCell x j) := by
  obtain ⟨d, hd, hdeg, hni, hnj⟩ := exists_pairCell i j (by omega)
  obtain ⟨mi, hWmi, hui⟩ := exists_merge_leg i hni
  obtain ⟨mj, hWmj, huj⟩ := exists_merge_leg j hnj
  obtain ⟨wj₁, hwj₁⟩ := exists_leg j hd hnj (σ := adjT i)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi₁, hwi₁⟩ := exists_leg i hd hni (σ := adjT j)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  obtain ⟨wi₂, hwi₂⟩ := exists_leg i hd hni (σ := adjT i * adjT j)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes _ j ≫ wj₁) (by rw [crossPerm_comp, hwj₁, crossPerm_atomOnes])
  obtain ⟨wj₂, hwj₂⟩ := exists_leg j hd hnj (σ := adjT j * adjT i)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes _ i ≫ wi₁) (by rw [crossPerm_comp, hwi₁, crossPerm_atomOnes])
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  -- the merge factorisation reads the second cut as two atoms
  have ha := arrow_pair x (codim_mergeOnes _ i) (codim_leg hdeg wi₂) (codim_atomOnes _ j)
    (codim_leg hdeg wj₁) (dimSum_atomComp _ i) (dimSum_atomComp _ j) hd
    (hom_ext_of_crossPerm (h := dimSum_replicate _) (by
      rw [crossPerm_comp, crossPerm_comp, hwi₂, hwj₁, crossPerm_atomOnes,
        crossPerm_eq_one_of_W _ (W_mergeOnes _ i), mul_one]))
  have hb := arrow_pair x (codim_mergeOnes _ j) (codim_leg hdeg wj₂) (codim_atomOnes _ i)
    (codim_leg hdeg wi₁) (dimSum_atomComp _ j) (dimSum_atomComp _ i) hd
    (hom_ext_of_crossPerm (h := dimSum_replicate _) (by
      rw [crossPerm_comp, crossPerm_comp, hwj₂, hwi₁, crossPerm_atomOnes,
        crossPerm_eq_one_of_W _ (W_mergeOnes _ j), mul_one]))
  rw [midArrow_eq x wi₂ _ (not_merge_of_crossPerm _ wi₂ (by rw [hwi₂]; exact adjT_mul_ne_one hne)),
    midArrow_eq x wj₁ _ (not_merge_of_crossPerm _ wj₁ (by rw [hwj₁]; exact adjT_ne_one i)),
    outArrow_merge _ _ _ _ (W_mergeOnes _ i), outArrow_atomOnes, hwi₂, hwj₁, permArrow_adjT,
    Category.comp_id] at ha
  rw [midArrow_eq x wj₂ _
      (not_merge_of_crossPerm _ wj₂ (by rw [hwj₂]; exact adjT_mul_ne_one hne.symm)),
    midArrow_eq x wi₁ _ (not_merge_of_crossPerm _ wi₁ (by rw [hwi₁]; exact adjT_ne_one j)),
    outArrow_merge _ _ _ _ (W_mergeOnes _ j), outArrow_atomOnes, hwj₂, hwi₁, permArrow_adjT,
    Category.comp_id] at hb
  -- and the two-atom factorisation is the hexagon
  have hc := arrow_pair x (codim_atomOnes _ i) (codim_leg hdeg wi₂) (codim_atomOnes _ j)
    (codim_leg hdeg wj₂) (dimSum_atomComp _ i) (dimSum_atomComp _ j) hd
    (atom_pair_eq (by rw [hwi₂, hwj₂]; exact adjT_braid i j hij))
  rw [midArrow_eq x wi₂ _ (not_merge_of_crossPerm _ wi₂ (by rw [hwi₂]; exact adjT_mul_ne_one hne)),
    midArrow_eq x wj₂ _
      (not_merge_of_crossPerm _ wj₂ (by rw [hwj₂]; exact adjT_mul_ne_one hne.symm)),
    outArrow_atomOnes, outArrow_atomOnes, hwi₂, hwj₂, ha, hb] at hc
  exact hc

/-! ## The Artin monoid acts

The atoms are an Artin family, so Matsumoto lifts every positive braid to a word in them; the
chosen word of a permutation is the value of that lift. -/

/-- A loop at a run, multiplied in composition order. -/
noncomputable def aOp (x : zCutContraction.V) (f : aObj x ⟶ aObj x) :
    (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ := MulOpposite.op f

private theorem aOp_mul (x : zCutContraction.V) (a b : aObj x ⟶ aObj x) :
    aOp x a * aOp x b = aOp x (a ≫ b) := rfl

/-- The atoms at a run, multiplied in composition order. -/
noncomputable def atomFam (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ :=
  aOp x (subArrow (atomCell x k))

theorem isArtinFamily_atomFam (x : zCutContraction.V) : IsArtinFamily (atomFam x) where
  comm i j h := by
    simp only [atomFam, aOp_mul]
    exact congrArg (aOp x) (subArrow_atomCell_comm x h)
  braid i j h := by
    simp only [atomFam, aOp_mul]
    exact congrArg (aOp x) (subArrow_atomCell_braid x h)

/-- **The positive braids act on the atoms at a run** — Matsumoto, read in the sub-polygraph. -/
noncomputable def atomBraid (x : zCutContraction.V) :
    PosBraid (vStrands x) →* (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ :=
  (ArtinPosBraid.lift (atomFam x) (isArtinFamily_atomFam x)).comp
    (posBraid_equiv_artinPos (vStrands x)).toMonoidHom

@[simp] theorem atomBraid_adjT (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    atomBraid x (posPerm (adjT k)) = atomFam x k := by
  rw [atomBraid, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, posBraid_equiv_artinPos_adjT]
  rfl

/-! ### A reduced word is the simple it spells -/

theorem posPermHom_foldl {n : ℕ} : ∀ (l : List (Fin (n - 1))) (b : PosBraid n),
    posPermHom n (l.foldl (fun c k => c * posPerm (adjT k)) b)
      = l.foldl (fun β k => β * adjT k) (posPermHom n b) := by
  intro l
  induction l with
  | nil => exact fun _ => rfl
  | cons k l ih =>
      intro b
      rw [List.foldl_cons, List.foldl_cons, ih, map_mul, posPermHom_posPerm]

theorem posLen_foldl {n : ℕ} : ∀ (l : List (Fin (n - 1))) (b : PosBraid n),
    Multiplicative.toAdd (posLen n (l.foldl (fun c k => c * posPerm (adjT k)) b))
      = Multiplicative.toAdd (posLen n b) + l.length := by
  intro l
  induction l with
  | nil => exact fun _ => (Nat.add_zero _).symm
  | cons k l ih =>
      intro b
      rw [List.foldl_cons, ih, map_mul, toAdd_mul, posLen_posPerm, permLen_adjT, toAdd_ofAdd,
        List.length_cons]
      omega

/-- **A reduced word spells the simple of the permutation it multiplies to.** -/
theorem posPerm_foldl {n : ℕ} (l : List (Fin (n - 1)))
    (hlen : l.length = permLen (l.foldl (fun β k => β * adjT k) 1)) :
    l.foldl (fun c k => c * posPerm (adjT k)) (1 : PosBraid n)
      = posPerm (l.foldl (fun β k => β * adjT k) 1) := by
  have hperm : posPermHom n (l.foldl (fun c k => c * posPerm (adjT k)) (1 : PosBraid n))
      = l.foldl (fun β k => β * adjT k) 1 := by
    rw [posPermHom_foldl, map_one]
  have hlen' : Multiplicative.toAdd
      (posLen n (l.foldl (fun c k => c * posPerm (adjT k)) (1 : PosBraid n)))
      = permLen (posPermHom n (l.foldl (fun c k => c * posPerm (adjT k)) (1 : PosBraid n))) := by
    rw [posLen_foldl, map_one, hperm, ← hlen]
    simp
  rw [eq_posPerm_of_posLen hlen', hperm]

theorem map_foldl {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N) {α : Type*} (g : α → M) :
    ∀ (l : List α) (b : M), φ (l.foldl (fun c k => c * g k) b)
      = l.foldl (fun c k => c * φ (g k)) (φ b) := by
  intro l
  induction l with
  | nil => exact fun _ => rfl
  | cons k l ih => intro b; rw [List.foldl_cons, ih, map_mul, List.foldl_cons]

theorem subArrow_atomCell_eq (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    subArrow (atomCell x k)
      = zAtomPoly.quot.map (keptCell (P := zCutContraction.poly) OutOfRun (atomCell x k)
        (outOfRun_atomCell x k)).toPath := by
  rw [subArrow_eq_quot]
  refine congrArg zAtomPoly.quot.map ?_
  rw [keptWord_eq (runWord_self (atomCell x k) (outOfRun_atomCell x k)) _
    (Quiver.Path.all_toPath.mpr (outOfRun_atomCell x k))]
  rfl

/-- **An atom word names the product of the atoms it spells.** -/
theorem aOp_atomPath (x : zCutContraction.V) : ∀ (l : List (Fin (vStrands x - 1)))
    (p : Quiver.Path (zCutContraction.poly.pt x) (zCutContraction.poly.pt x))
    (hp : Quiver.Path.All (fun ⦃_ _⦄ e => OutOfRun e) p)
    (b : (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ),
    aOp x (zAtomPoly.quot.map (keptWord (P := zCutContraction.poly) OutOfRun p hp)) = b →
      aOp x (zAtomPoly.quot.map (keptWord (P := zCutContraction.poly) OutOfRun
          (atomPath x l p) (all_atomPath x l p hp)))
        = l.foldl (fun c k => c * atomFam x k) b := by
  intro l
  induction l with
  | nil => exact fun _ _ _ h => h
  | cons k l ih =>
      intro p hp b h
      refine ih _ ((Quiver.Path.all_cons_iff p _).mpr ⟨hp, outOfRun_atomCell x k⟩) _ ?_
      refine Eq.trans (congrArg (aOp x) (Polygraph.quot_map_cons zAtomPoly _ _)) ?_
      refine Eq.trans (aOp_mul x _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t * aOp x (zAtomPoly.quot.map (Quiver.Hom.toPath
        (keptCell (P := zCutContraction.poly) OutOfRun (atomCell x k)
          (outOfRun_atomCell x k))))) h) ?_
      exact congrArg (fun t => b * aOp x t) (subArrow_atomCell_eq x k).symm

/-- **A positive braid acts by the chosen atom word of its permutation** — Matsumoto, since any
reduced word spells the same simple. -/
theorem atomBraid_posPerm (x : zCutContraction.V) (τ : Equiv.Perm (Fin (vStrands x))) :
    atomBraid x (posPerm τ) = aOp x (permArrow x τ) := by
  obtain ⟨hlen, hfold, -⟩ := (exists_atomWord (vStrands x) τ).choose_spec
  have h1 : posPerm τ
      = (exists_atomWord (vStrands x) τ).choose.foldl (fun c k => c * posPerm (adjT k)) 1 := by
    rw [posPerm_foldl _ (by rw [hfold, hlen]), hfold]
  rw [h1, map_foldl (atomBraid x) (fun k => posPerm (adjT k)), map_one]
  simp only [atomBraid_adjT]
  refine (aOp_atomPath x _ Quiver.Path.nil (Quiver.Path.all_nil _) 1 ?_).symm
  exact congrArg (aOp x) (Polygraph.quot_map_nil zAtomPoly _)

/-! ## The grading reads a 1-cell as its crossing permutation

`posGradeLoc` is the easy half of `Concurrency/Presentation/Retraction`: the merges it inverts carry
no element, so only the loop in the middle of a conjugate survives. -/

private theorem val_sandwich {M : ℕ → Type*} [∀ n, Monoid (M n)] {m n p q : ℕ}
    (a : @Quiver.Hom (Graded M) _ m n) (b : @Quiver.Hom (Graded M) _ n p)
    (c : @Quiver.Hom (Graded M) _ p q) (ha : a.val = 1) (hc : c.val = 1) :
    (a ≫ b ≫ c).val = Graded.congrDeg a.deg.symm b.val := by
  rw [Graded.val_comp, Graded.val_comp, ha, hc, map_one, one_mul, mul_one]

private theorem congrDeg_congrDeg {M : ℕ → Type*} [∀ n, Monoid (M n)] {m n : ℕ}
    (h : m = n) (h' : n = m) (a : M m) : Graded.congrDeg h' (Graded.congrDeg h a) = a := by
  subst h; rfl

private theorem val_eq_one_of_comp_id {M : ℕ → Type*} [∀ n, Monoid (M n)] {m n : ℕ}
    {f : @Quiver.Hom (Graded M) _ m n} {g : @Quiver.Hom (Graded M) _ n m}
    (hf : f.val = 1) (h : f ≫ g = @CategoryStruct.id (Graded M) _ m) : g.val = 1 := by
  have h1 := congrArg GradedHom.val h
  rw [Graded.val_comp, hf, mul_one] at h1
  have h2 := congrArg (Graded.congrDeg (M := M) f.deg.symm.symm) h1
  rw [Graded.congrDeg_symm_apply] at h2
  exact h2.trans (map_one _)

theorem val_posGradeLoc_vRunIso_hom (x : zCutContraction.V) :
    (posGradeLoc.map (vRunIso x).hom).unop.val = 1 := by
  change (posGradeLoc.map (((W Zbp).op).Q.map (eqToHom (zSh_eq_ones x)).op)).unop.val = 1
  rw [posGradeLoc_map_Q]
  change (posGrade.map (eqToHom (zSh_eq_ones x))).val = 1
  rw [posGrade_map_of_W (W_eqToHom (zSh_eq_ones x))]
  rfl

theorem val_posGradeLoc_vRunIso_inv (x : zCutContraction.V) :
    (posGradeLoc.map (vRunIso x).inv).unop.val = 1 := by
  refine val_eq_one_of_comp_id (val_posGradeLoc_vRunIso_hom x) ?_
  have h : posGradeLoc.map (vRunIso x).inv ≫ posGradeLoc.map (vRunIso x).hom = 𝟙 _ := by
    rw [← posGradeLoc.map_comp, (vRunIso x).inv_hom_id, posGradeLoc.map_id]
  exact congrArg Quiver.Hom.unop h

/-- **A loop at a 0-cell's own shape performs its crossing permutation.** -/
theorem posGradeLoc_middle (x : zCutContraction.V) (τ : Equiv.Perm (Fin (vStrands x))) :
    posGradeLoc.map ((vRunIso x).inv ≫ runLoop (vStrands x) τ ≫ (vRunIso x).hom)
      = Quiver.Hom.op (Graded.loop (posPerm τ)) := by
  have hmid : (posGradeLoc.map (runLoop (vStrands x) τ)).unop.val
      = Graded.congrDeg (dimSum_replicate (vStrands x)).symm (posPerm τ) :=
    Graded.congrDeg_eq_symm _ (runGrade_runLoop (vStrands x) τ)
  refine Quiver.Hom.unop_inj (GradedHom.ext ?_)
  rw [posGradeLoc.map_comp, posGradeLoc.map_comp, unop_comp, unop_comp, Category.assoc,
    val_sandwich _ _ _ (val_posGradeLoc_vRunIso_hom x) (val_posGradeLoc_vRunIso_inv x), hmid]
  exact congrDeg_congrDeg _ _ (posPerm τ)

/-! ## The run at a strand count

A 0-cell is the run on its own events, so the strand count names it. -/

/-- The 0-cell at a strand count. -/
noncomputable def runV (N : ℕ) : zCutContraction.V :=
  ⟨zEltV (zObj (𝟙^N)), zEltV_ext (by
    change zObj (𝟙^(dimSum (zObj (𝟙^N) : Ch Zbp).dims)) = zObj (𝟙^N)
    rw [zObj_dims, dimSum_replicate])⟩

@[simp] theorem vStrands_runV (N : ℕ) : vStrands (runV N) = N := by
  change dimSum (zObj (𝟙^N) : Ch Zbp).dims = N
  rw [zObj_dims, dimSum_replicate]

@[simp] theorem runV_vStrands (x : zCutContraction.V) : runV (vStrands x) = x :=
  Subtype.ext (zEltV_ext (zSh_eq_ones x).symm)

/-! ## The graded positive braid monoid acts on the sub-polygraph -/

/-- The atoms at a run, indexed by any naming of its strand count. -/
noncomputable def atomFamAt {N : ℕ} {x : zCutContraction.V} (h : vStrands x = N)
    (k : Fin (N - 1)) : (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ :=
  atomFam x (finCongr (by rw [h]) k)

theorem isArtinFamily_atomFamAt {N : ℕ} {x : zCutContraction.V} (h : vStrands x = N) :
    IsArtinFamily (atomFamAt h) := by
  subst h; exact isArtinFamily_atomFam x

/-- **The positive braids act on the atoms at a run** — Matsumoto, read in the sub-polygraph. -/
noncomputable def atomBraidAt {N : ℕ} {x : zCutContraction.V} (h : vStrands x = N) :
    PosBraid N →* (@End zAtomPoly.presented _ (aObj x))ᵐᵒᵖ :=
  (ArtinPosBraid.lift (atomFamAt h) (isArtinFamily_atomFamAt h)).comp
    (posBraid_equiv_artinPos N).toMonoidHom

theorem atomBraidAt_rfl (x : zCutContraction.V) (τ : Equiv.Perm (Fin (vStrands x))) :
    atomBraidAt (rfl : vStrands x = vStrands x) (posPerm τ) = aOp x (permArrow x τ) :=
  atomBraid_posPerm x τ

/-- **A 0-cell's action is the run's, renamed.** -/
theorem atomBraidAt_congr {N : ℕ} {x y : zCutContraction.V} (hy : y = x) (h : vStrands y = N)
    (h' : vStrands x = N) (β : PosBraid N) :
    ((atomBraidAt h β).unop : aObj y ⟶ aObj y)
      = eqToHom (congrArg aObj hy) ≫ ((atomBraidAt h' β).unop : aObj x ⟶ aObj x)
        ≫ eqToHom (congrArg aObj hy).symm := by
  subst hy; simp

/-- **The positive braids, acting on the sub-polygraph** — one copy per strand count. -/
noncomputable def artinFull : FullPosBraidᵒᵖ ⥤ zAtomPoly.presented :=
  Graded.descOp (fun N => aObj (runV N)) (fun N => atomBraidAt (vStrands_runV N))

/-! ## The degree-zero cells derive the rest

The grading sends a word of cuts to its braid and the action sends that braid back to the word the
atoms spell, so a 2-cell of the run presentation is already an equation in the sub-polygraph. -/

/-- The braid a 1-cell performs, at its own strand count. -/
noncomputable def posPre : GenObj zCutContraction.poly.Gen ⥤q FullPosBraidᵒᵖ where
  obj V := Opposite.op (vStrands V.as)
  map {X Y} e := Quiver.Hom.op
    (⟨(congrArg vStrands (eq_of_gen e)).symm,
      Graded.congrDeg (congrArg vStrands (eq_of_gen e)) (posPerm (genPerm e))⟩ :
      @Quiver.Hom FullPosBraid _ (vStrands Y.as) (vStrands X.as))

/-- The grading of a 0-cell: its own strand count. -/
noncomputable def gradeIso (V : GenObj zCutContraction.poly.Gen) :
    posGradeLoc.obj (zRunPresentation.at' V) ≅ posPre.obj V :=
  posGradeLoc.mapIso (zLocIso V.as.1)

/-- …and the 0-cell that strand count names. -/
noncomputable def fullIso (V : GenObj zCutContraction.poly.Gen) :
    artinFull.obj (posPre.obj V) ≅ subF.obj V :=
  eqToIso (congrArg aObj (runV_vStrands V.as))

private theorem reassoc₅ {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    (a ≫ b) ≫ c ≫ (d ≫ e) = a ≫ (b ≫ c ≫ d) ≫ e := by simp

private theorem eq_of_conj {C : Type*} [Category C] {A B A' B' : C} (i : A ≅ B) (j : A' ≅ B')
    {f g : B ⟶ B'} (h : i.hom ≫ f ≫ j.inv = i.hom ≫ g ≫ j.inv) : f = g := by
  have h' := congrArg (fun t => i.inv ≫ t ≫ j.hom) h
  simpa using h'

/-- **A 1-cell is graded by its crossing permutation.** -/
theorem posGradeLoc_arrow {X Y : GenObj zCutContraction.poly.Gen} (e : X ⟶ Y) :
    posGradeLoc.map (zRunPresentation.arrow e)
      = (gradeIso X).hom ≫ posPre.map e ≫ (gradeIso Y).inv := by
  obtain rfl : X = Y := GenObj.ext (eq_of_gen e)
  have harr : zRunPresentation.arrow e = (zLocIso X.as.1).hom
      ≫ ((vRunIso X.as).inv ≫ runLoop (vStrands X.as) (genPerm e) ≫ (vRunIso X.as).hom)
        ≫ (zLocIso X.as.1).inv := by
    rw [zRun_arrow_runLoop e]
    exact reassoc₅ _ _ _ _ _
  rw [harr]
  refine Eq.trans (posGradeLoc.map_comp _ _) (Eq.trans (congrArg
    (fun t => posGradeLoc.map (zLocIso X.as.1).hom ≫ t) (posGradeLoc.map_comp _ _)) ?_)
  exact congrArg (fun t => posGradeLoc.map (zLocIso X.as.1).hom ≫ t
    ≫ posGradeLoc.map (zLocIso X.as.1).inv) (posGradeLoc_middle X.as (genPerm e))

/-- **…and that braid acts by the word the atoms spell.** -/
theorem artinFull_posPre {X Y : GenObj zCutContraction.poly.Gen} (e : X ⟶ Y) :
    artinFull.map (posPre.map e) = (fullIso X).hom ≫ subArrow e ≫ (fullIso Y).inv := by
  obtain rfl : X = Y := GenObj.ext (eq_of_gen e)
  have h1 : artinFull.map (posPre.map e)
      = ((atomBraidAt (vStrands_runV (vStrands X.as)) (posPerm (genPerm e))).unop
          : aObj (runV (vStrands X.as)) ⟶ aObj (runV (vStrands X.as))) :=
    Category.id_comp _
  rw [h1, atomBraidAt_congr (runV_vStrands X.as) _ rfl, atomBraidAt_rfl,
    subArrow_eq_permArrow]
  rfl

theorem lift_posPre {X Y : GenObj zCutContraction.poly.Gen} (u : Quiver.Path X Y) :
    posGradeLoc.map (zRunPresentation.eval.map u)
      = (gradeIso X).hom ≫ (Paths.lift posPre).map u ≫ (gradeIso Y).inv := by
  rw [← Presents.lift_evalPre_comp zRunPresentation posGradeLoc u]
  exact Polygraph.lift_conj (ψ := zRunPresentation.evalPre ⋙q posGradeLoc.toPrefunctor)
    (ψ' := posPre) gradeIso (fun e => posGradeLoc_arrow e) u

theorem lift_subF {X Y : GenObj zCutContraction.poly.Gen} (u : Quiver.Path X Y) :
    artinFull.map ((Paths.lift posPre).map u)
      = (fullIso X).hom ≫ subF.map u ≫ (fullIso Y).inv := by
  rw [Paths.lift_comp_map posPre artinFull u,
    show subF.map u = (Paths.lift (subPre (P := zCutContraction.poly) OutOfRun runWord all_runWord
      ⋙q zAtomPoly.quot.toPrefunctor)).map u from
      Paths.lift_comp_map (subPre (P := zCutContraction.poly) OutOfRun runWord all_runWord)
        zAtomPoly.quot u]
  refine Polygraph.lift_conj (ψ := posPre ⋙q artinFull.toPrefunctor)
    (ψ' := subPre (P := zCutContraction.poly) OutOfRun runWord all_runWord
      ⋙q zAtomPoly.quot.toPrefunctor) fullIso (fun e => ?_) u
  exact (artinFull_posPre e).trans (by rw [subArrow_eq_quot]; rfl)

/-- **Every 2-cell of the run presentation holds in the sub-polygraph.** -/
theorem cell_derivable' {X Y : GenObj zCutContraction.poly.Gen}
    (α : zCutContraction.poly.Rel X Y) :
    subF.map (zCutContraction.poly.src α) = subF.map (zCutContraction.poly.tgt α) := by
  have h := zRunPresentation.sound α
  have hu := lift_posPre (zCutContraction.poly.src α)
  have hv := lift_posPre (zCutContraction.poly.tgt α)
  rw [h] at hu
  have h1 : (Paths.lift posPre).map (zCutContraction.poly.src α)
      = (Paths.lift posPre).map (zCutContraction.poly.tgt α) :=
    eq_of_conj (gradeIso X) (gradeIso Y) (hu.symm.trans hv)
  exact eq_of_conj (fullIso X) (fullIso Y)
    ((lift_subF _).symm.trans ((congrArg artinFull.map h1).trans (lift_subF _)))

/-! ## The presentation -/

/-- **Keeping the cuts out of a run and the codimension-two cells above them loses nothing.** -/
noncomputable def runSpans : Spans zCutContraction.poly OutOfRun OutOfRunCell where
  word := runWord
  word_all := all_runWord
  word_eq := quot_runWord
  word_self := runWord_self
  cell_derivable α := cell_derivable' α

/-- **`Ch(Z)[W⁻¹]` presented by the `N−1` atoms at each run, with the codimension-two cuts out of
that run as the only relations.** -/
noncomputable def zAtomPresentation :
    Presents runSpans.poly (((W Zbp).op).Localization) :=
  zRunPresentation.restrictCells runSpans

/-- **A kept 1-cell names the atom loop it always named.** -/
theorem zAtomPresentation_arrow (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    zAtomPresentation.arrow (atomGen x k)
      = (runIsoAt x).hom ≫ atomLoop (vStrands x) k ≫ (runIsoAt x).inv :=
  (zRunPresentation.restrictCells_arrow runSpans (atomGen x k)).trans (arrow_atomCell x k)

/-- Appending two loops to a conjugated one. -/
private theorem conj_step₃ {C : Type*} [Category C] {X Y : C} (I : X ≅ Y) (A B D : Y ⟶ Y) :
    (I.hom ≫ A ≫ I.inv) ≫ (I.hom ≫ B ≫ I.inv) ≫ (I.hom ≫ D ≫ I.inv)
      = I.hom ≫ (A ≫ B ≫ D) ≫ I.inv := by simp

private theorem conj_step₂ {C : Type*} [Category C] {X Y : C} (I : X ≅ Y) (A B : Y ⟶ Y) :
    (I.hom ≫ A ≫ I.inv) ≫ (I.hom ≫ B ≫ I.inv) = I.hom ≫ (A ≫ B) ≫ I.inv := by simp

/-- **Two adjacent atoms braid.** -/
theorem zAtomPresentation_braid (x : zCutContraction.V) {i j : Fin (vStrands x - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    zAtomPresentation.arrow (atomGen x i) ≫ zAtomPresentation.arrow (atomGen x j)
        ≫ zAtomPresentation.arrow (atomGen x i)
      = zAtomPresentation.arrow (atomGen x j) ≫ zAtomPresentation.arrow (atomGen x i)
        ≫ zAtomPresentation.arrow (atomGen x j) := by
  simp only [zAtomPresentation_arrow]
  refine Eq.trans (conj_step₃ (runIsoAt x) _ _ _)
    (Eq.trans ?_ (conj_step₃ (runIsoAt x) _ _ _).symm)
  exact congrArg (fun t => (runIsoAt x).hom ≫ t ≫ (runIsoAt x).inv) (atomLoop_braid hij)

/-- **…and two far-apart atoms commute.** -/
theorem zAtomPresentation_comm (x : zCutContraction.V) {i j : Fin (vStrands x - 1)}
    (hij : (i : ℕ) + 1 < (j : ℕ)) :
    zAtomPresentation.arrow (atomGen x i) ≫ zAtomPresentation.arrow (atomGen x j)
      = zAtomPresentation.arrow (atomGen x j) ≫ zAtomPresentation.arrow (atomGen x i) := by
  simp only [zAtomPresentation_arrow]
  refine Eq.trans (conj_step₂ (runIsoAt x) _ _) (Eq.trans ?_ (conj_step₂ (runIsoAt x) _ _).symm)
  exact congrArg (fun t => (runIsoAt x).hom ≫ t ≫ (runIsoAt x).inv) (atomLoop_comm hij)

/-! ## Against Artin's own polygraph

The 1-cells match atom for atom, so the comparison is a `Presents.Map`; the 2-cells do not match in
number — a `Cut.Cell` is an *ordered pair of two-step factorisations*, so a codimension-two cut out
of a run carries several, where `artinBP` carries one relation per pair of atoms. -/

/-- The atom index a 1-cell carries. -/
noncomputable def genIdx {X Y : GenObj runSpans.poly.Gen} (e : X ⟶ Y) :
    Fin (vStrands Y.as - 1) :=
  (keptEquiv Y.as).symm
    (cellCongr (keptGen (P := zCutContraction.poly) OutOfRun) (eq_of_gen e.1) rfl e)

@[simp] theorem genIdx_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    genIdx (atomGen x k) = k := (keptEquiv x).symm_apply_apply k

theorem exists_atomGen {X : GenObj runSpans.poly.Gen} (e : X ⟶ X) :
    ∃ k : Fin (vStrands X.as - 1), atomGen X.as k = e :=
  ⟨(keptEquiv X.as).symm e, (keptEquiv X.as).apply_symm_apply e⟩

/-- The Artin generator an atom names. -/
noncomputable def genRunBP {X Y : GenObj runSpans.poly.Gen} (e : X ⟶ Y) :
    runBP.pt (vStrands X.as) ⟶ runBP.pt (vStrands Y.as) :=
  Quiver.homOfEq (runBP.gen (runAtom (vStrands Y.as) (genIdx e)))
    (congrArg runBP.pt (congrArg vStrands (eq_of_gen e.1))).symm rfl

theorem genRunBP_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    genRunBP (atomGen x k) = runBP.gen (runAtom (vStrands x) k) := by
  rw [genRunBP, genIdx_atomGen]; rfl

/-- **The atom polygraph and Artin's present one category, atom by atom.** -/
noncomputable def runBPComparison : Polygraph.Presents.Map zAtomPresentation runBP.base :=
  Polygraph.Presents.Map.ofGenerators (fun V => runBP.pt (vStrands V.as))
    (fun {_ _} e => genRunBP e) (fun V => (runIsoAt V.as).symm)
    (fun {X Y} e => by
      obtain rfl : X = Y := GenObj.ext (eq_of_gen e.1)
      obtain ⟨k, rfl⟩ := exists_atomGen e
      have h1 : runBP.base.arrow (genRunBP (atomGen X.as k)) = atomLoop (vStrands X.as) k := by
        rw [genRunBP_atomGen, runBase_arrow_atomLoop, runAtomLoop_runAtom]
      refine Eq.trans h1 (Eq.trans ?_
        (congrArg (fun t => (runIsoAt X.as).inv ≫ t ≫ (runIsoAt X.as).hom)
          (zAtomPresentation_arrow X.as k)).symm)
      simp)

/-- **…and at each strand count that polygraph is Artin's**, cell for cell — `runRelabel`. -/
noncomputable def runBPArtin (N : ℕ) : runBP.P N ≅ artinBP.P N := runRelabel N

end ChainCat
