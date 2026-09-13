import CubeChains.Machinery.Presentation.Contract

/-!
# Machinery/Presentation/ContractMap — a contraction is functorial in the polygraph

A map of polygraphs *reflecting* the contracted family and taking each chosen merge to the chosen
merge carries one contraction to another.  The square below is `Map.pre_words`, and the two boundary
laws of `Map.poly` are it read at a 2-cell's source and target word.

                   c.words
    P.Word ─────────────────────▸ Paths (GenObj c.Gen)
      │ m.hom.words                   │ m.pre
      ▾                               ▾
    Q.Word ─────────────────────▸ Paths (GenObj c'.Gen)
                   c'.words

It commutes only up to `repObj_pre`, the two ways a representative is pushed forward; `cellCongr`
carries that, and nothing else here does.  Reading a 1-cell *back* needs no transport at all.
-/

universe w u' w₂ v u

namespace CategoryTheory

namespace Contraction

variable {P Q R : Polygraph.{w, u', w₂}} {S : ∀ {a b : P.V}, P.Gen a b → Prop}
  {T : ∀ {a b : Q.V}, Q.Gen a b → Prop} {U : ∀ {a b : R.V}, R.Gen a b → Prop}
  {c : Contraction P S} {c' : Contraction Q T} {c'' : Contraction R U}

/-- Renaming a 1-cell's endpoints is `Quiver.homOfEq` and nothing more — `Gen.ext`, the endpoints
entering only through proofs. -/
theorem gen_eq_homOfEq {x y x' y' : c.V} (h₁ : x = x') (h₂ : y = y')
    (e : (⟨x⟩ : GenObj c.Gen) ⟶ ⟨y⟩) (e' : (⟨x'⟩ : GenObj c.Gen) ⟶ ⟨y'⟩)
    (hd : e.dom = e'.dom) (hc : e.cod = e'.cod) (hg : e.gen ≍ e'.gen) :
    e' = Quiver.homOfEq e (congrArg GenObj.mk h₁) (congrArg GenObj.mk h₂) := by
  subst h₁; subst h₂
  change e' = e
  exact (Contraction.Gen.ext c e e' hd hc hg).symm

theorem words_nil (c : Contraction P S) (u : GenObj P.Gen) :
    c.words.map (Quiver.Path.nil : Quiver.Path u u) = Quiver.Path.nil :=
  Paths.lift_nil c.pre u

theorem words_cons (c : Contraction P S) {u v z : GenObj P.Gen} (R : Quiver.Path u v) (e : v ⟶ z) :
    c.words.map (R.cons e) = (c.words.map R).comp (c.cell e) :=
  Paths.lift_cons c.pre R e

/-- **Data carrying one contraction to another**: a map of polygraphs that reflects the contracted
family and takes each chosen merge onto a representative to the chosen merge. -/
structure Map (c : Contraction P S) (c' : Contraction Q T) where
  /-- the map of polygraphs -/
  hom : P ⟶ Q
  /-- …which reflects the contracted family -/
  mem_iff {a b : P.V} (g : P.Gen a b) : T (hom.pre.map (Polygraph.cell g)) ↔ S g
  /-- …and commutes with the representative -/
  rep_hom (x : P.V) : c'.rep (hom.pre.obj (P.pt x)).as = (hom.pre.obj (P.pt (c.rep x))).as
  /-- …carrying the merge onto the representative to the merge -/
  word_hom (x : P.V) : hom.pre.mapPath (c.word x)
    = cellCongr Quiver.Path rfl (congrArg Q.pt (rep_hom x))
        (c'.word (hom.pre.obj (P.pt x)).as)
  /-- …and its inverse to the inverse -/
  invWord_hom (x : P.V) : hom.pre.mapPath (c.invWord x)
    = cellCongr Quiver.Path (congrArg Q.pt (rep_hom x)) rfl
        (c'.invWord (hom.pre.obj (P.pt x)).as)

namespace Map

variable (m : Map c c')

/-- **A map is its map of polygraphs** — the other four fields are propositions. -/
theorem ext : ∀ {m m' : Map c c'}, m.hom = m'.hom → m = m'
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, h => by subst h; rfl

/-! ## The contracted polygraph, on a map -/

/-- The 0-cell a 0-cell is carried to. -/
def obj (x : P.V) : Q.V := (m.hom.pre.obj (P.pt x)).as

/-- **…a representative to a representative.** -/
def vtx (x : c.V) : c'.V := ⟨m.obj x.1, (m.rep_hom x.1).trans (congrArg m.obj x.2)⟩

/-- **The conjugated generators, carried along** — the same generator, read at the pushed-forward
representatives. -/
def pre : GenObj c.Gen ⥤q GenObj c'.Gen where
  obj X := ⟨m.vtx X.as⟩
  map {_ _} e :=
    { dom := m.obj e.dom
      cod := m.obj e.cod
      gen := m.hom.pre.map (Polygraph.cell e.gen)
      not_mem := fun h => e.not_mem ((m.mem_iff e.gen).mp h)
      rep_dom := (m.rep_hom e.dom).trans (congrArg m.obj e.rep_dom)
      rep_cod := (m.rep_hom e.cod).trans (congrArg m.obj e.rep_cod) }

/-- **The representative of a pushed-forward 0-cell, two ways** — the only transport in the file. -/
theorem repObj_pre (u : GenObj P.Gen) : c'.repObj (m.hom.pre.obj u) = m.pre.obj (c.repObj u) :=
  GenObj.ext (Subtype.ext (m.rep_hom u.as))

/-- A conjugated non-contracted letter is carried to the conjugate of its image. -/
theorem pre_map_genCell {u v : GenObj P.Gen} (g : u ⟶ v) (hg : ¬ S g)
    (hg' : ¬ T (m.hom.pre.map g)) :
    m.pre.map (c.genCell g hg)
      = Quiver.homOfEq (c'.genCell (m.hom.pre.map g) hg') (m.repObj_pre u) (m.repObj_pre v) :=
  gen_eq_homOfEq (Subtype.ext (m.rep_hom u.as)) (Subtype.ext (m.rep_hom v.as))
    (c'.genCell (m.hom.pre.map g) hg') (m.pre.map (c.genCell g hg)) rfl rfl HEq.rfl

/-- **The conjugation squares with the map, on a letter** — a contracted letter becomes the empty
word on both sides, any other becomes itself. -/
theorem pre_cell {u v : GenObj P.Gen} (g : u ⟶ v) :
    m.pre.mapPath (c.cell g)
      = cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre v)
          (c'.cell (m.hom.pre.map g)) := by
  by_cases hg : S g
  · have hg' : T (m.hom.pre.map g) := (m.mem_iff g).mpr hg
    refine Eq.trans (congrArg m.pre.mapPath (c.cell_of_S g hg)) ?_
    refine Eq.trans (Prefunctor.mapPath_cellCongr m.pre rfl (c.repObj_eq_of_S g hg)
      Quiver.Path.nil) ?_
    refine Eq.trans ?_ (congrArg (cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre v))
      (c'.cell_of_S (m.hom.pre.map g) hg')).symm
    refine Eq.trans ?_ (cellCongr_trans Quiver.Path rfl
      (c'.repObj_eq_of_S (m.hom.pre.map g) hg') (m.repObj_pre u) (m.repObj_pre v)
      Quiver.Path.nil).symm
    exact cellCongr_nil_eq _ _ _ _
  · have hg' : ¬ T (m.hom.pre.map g) := fun h => hg ((m.mem_iff g).mp h)
    refine Eq.trans (congrArg m.pre.mapPath (c.cell_of_not_S g hg)) ?_
    refine Eq.trans (congrArg Quiver.Hom.toPath (m.pre_map_genCell g hg hg')) ?_
    refine Eq.trans (cellCongr_toPath (V := GenObj c'.Gen) (m.repObj_pre u) (m.repObj_pre v)
      (c'.genCell (m.hom.pre.map g) hg')).symm ?_
    exact congrArg (cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre v))
      (c'.cell_of_not_S (m.hom.pre.map g) hg').symm

/-- **…and on a whole word.** -/
theorem pre_words {u v : GenObj P.Gen} (R : Quiver.Path u v) :
    m.pre.mapPath (c.words.map R)
      = cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre v)
          (c'.words.map (m.hom.pre.mapPath R)) := by
  induction R with
  | nil =>
      refine Eq.trans (congrArg m.pre.mapPath (c.words_nil u)) ?_
      refine Eq.trans ?_ (congrArg (cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre u))
        (c'.words_nil (m.hom.pre.obj u)).symm)
      exact cellCongr_nil_eq rfl rfl (m.repObj_pre u) (m.repObj_pre u)
  | @cons y z R e ih =>
      refine Eq.trans (congrArg m.pre.mapPath (c.words_cons R e)) ?_
      refine Eq.trans (Prefunctor.mapPath_comp m.pre (c.words.map R) (c.cell e)) ?_
      refine Eq.trans (congrArg₂ Quiver.Path.comp ih (m.pre_cell e)) ?_
      refine Eq.trans (cellCongr_comp (m.repObj_pre u) (m.repObj_pre y) (m.repObj_pre z) _ _) ?_
      exact congrArg (cellCongr Quiver.Path (m.repObj_pre u) (m.repObj_pre z))
        (c'.words_cons (m.hom.pre.mapPath R) (m.hom.pre.map e)).symm

/-- …read at a 2-cell's boundary, which is where the two boundary laws need it. -/
theorem pre_mapPath_cellCongr_words {X Y : GenObj c.Gen} {u v : GenObj P.Gen}
    (hu : c.repObj u = X) (hv : c.repObj v = Y) (R : Quiver.Path u v) :
    m.pre.mapPath (cellCongr Quiver.Path hu hv (c.words.map R))
      = cellCongr Quiver.Path ((m.repObj_pre u).trans (congrArg m.pre.obj hu))
          ((m.repObj_pre v).trans (congrArg m.pre.obj hv))
          (c'.words.map (m.hom.pre.mapPath R)) :=
  (Prefunctor.mapPath_cellCongr m.pre hu hv (c.words.map R)).trans
    ((congrArg (cellCongr Quiver.Path (congrArg m.pre.obj hu) (congrArg m.pre.obj hv))
        (m.pre_words R)).trans
      (cellCongr_trans Quiver.Path (m.repObj_pre u) (m.repObj_pre v) (congrArg m.pre.obj hu)
        (congrArg m.pre.obj hv) _))

/-- **The contracted polygraph, on a map.** -/
noncomputable def poly : c.poly ⟶ c'.poly where
  pre := m.pre
  two {_ _} α :=
    { dom := m.hom.pre.obj α.dom
      cod := m.hom.pre.obj α.cod
      cell := m.hom.two α.cell
      rep_dom := (m.repObj_pre α.dom).trans (congrArg m.pre.obj α.rep_dom)
      rep_cod := (m.repObj_pre α.cod).trans (congrArg m.pre.obj α.rep_cod) }
  src_two α :=
    (congrArg (fun W => cellCongr Quiver.Path
        ((m.repObj_pre α.dom).trans (congrArg m.pre.obj α.rep_dom))
        ((m.repObj_pre α.cod).trans (congrArg m.pre.obj α.rep_cod)) (c'.words.map W))
      (m.hom.src_two α.cell)).trans
    (m.pre_mapPath_cellCongr_words α.rep_dom α.rep_cod (P.src α.cell)).symm
  tgt_two α :=
    (congrArg (fun W => cellCongr Quiver.Path
        ((m.repObj_pre α.dom).trans (congrArg m.pre.obj α.rep_dom))
        ((m.repObj_pre α.cod).trans (congrArg m.pre.obj α.rep_cod)) (c'.words.map W))
      (m.hom.tgt_two α.cell)).trans
    (m.pre_mapPath_cellCongr_words α.rep_dom α.rep_cod (P.tgt α.cell)).symm

@[simp] theorem poly_pre : m.poly.pre = m.pre := rfl

/-! ## …and reading a 1-cell back

`backPre` conjugates a letter by the two chosen merges, and `word_hom`/`invWord_hom` carry exactly
those, so the square for `backSpelling` needs no transport at all. -/

/-- **The conjugate of a letter, carried along.** -/
theorem pre_backWord {u v : GenObj P.Gen} (g : u ⟶ v) :
    m.hom.pre.mapPath (c.backWord g)
      = cellCongr Quiver.Path (congrArg Q.pt (m.rep_hom u.as))
          (congrArg Q.pt (m.rep_hom v.as)) (c'.backWord (m.hom.pre.map g)) := by
  refine Eq.trans (Prefunctor.mapPath_comp m.hom.pre (c.invWord u.as)
    (g.toPath.comp (c.word v.as))) ?_
  refine Eq.trans (congrArg (Quiver.Path.comp (m.hom.pre.mapPath (c.invWord u.as)))
    ((Prefunctor.mapPath_comp m.hom.pre g.toPath (c.word v.as)).trans
      (congrArg (fun t => Quiver.Path.comp t (m.hom.pre.mapPath (c.word v.as)))
        (Prefunctor.mapPath_toPath m.hom.pre g)))) ?_
  refine Eq.trans (congrArg₂ Quiver.Path.comp (m.invWord_hom u.as)
    (congrArg (Quiver.Path.comp (m.hom.pre.map g).toPath) (m.word_hom v.as))) ?_
  refine Eq.trans (congrArg (Quiver.Path.comp
      (cellCongr Quiver.Path (congrArg Q.pt (m.rep_hom u.as)) rfl (c'.invWord (m.obj u.as))))
    (cellCongr_comp rfl rfl (congrArg Q.pt (m.rep_hom v.as)) (m.hom.pre.map g).toPath
      (c'.word (m.obj v.as)))) ?_
  exact cellCongr_comp (congrArg Q.pt (m.rep_hom u.as)) rfl
    (congrArg Q.pt (m.rep_hom v.as)) (c'.invWord (m.obj u.as)) _

/-- **…so a 1-cell of the contraction reads back to the 1-cell its image reads back to.** -/
theorem pre_backPre {X Y : GenObj c.Gen} (e : X ⟶ Y) :
    m.hom.pre.mapPath (c.backPre.map e) = c'.backPre.map (m.pre.map e) := by
  refine Eq.trans (Prefunctor.mapPath_cellCongr m.hom.pre (congrArg P.pt e.rep_dom)
    (congrArg P.pt e.rep_cod) (c.backWord (Polygraph.cell e.gen))) ?_
  refine Eq.trans (congrArg (cellCongr Quiver.Path (congrArg m.hom.pre.obj
      (congrArg P.pt e.rep_dom)) (congrArg m.hom.pre.obj (congrArg P.pt e.rep_cod)))
    (m.pre_backWord (Polygraph.cell e.gen))) ?_
  exact cellCongr_trans Quiver.Path _ _ _ _ _

/-- **…and that is the square, on a letter.** -/
theorem backSpelling_functor_map_quot {X Y : GenObj c.poly.Gen} (e : X ⟶ Y) :
    c'.backSpelling.functor.map (m.poly.functor.map (c.poly.quot.map e.toPath))
      = m.hom.functor.map (c.backSpelling.functor.map (c.poly.quot.map e.toPath)) :=
  show Q.quot.map ((Paths.lift c'.backPre).map (m.pre.map e).toPath)
      = Q.quot.map (m.hom.pre.mapPath ((Paths.lift c.backPre).map e.toPath)) from
  (congrArg Q.quot.map (Paths.lift_toPath c'.backPre (m.pre.map e))).trans
    ((congrArg Q.quot.map (m.pre_backPre e).symm).trans
      (congrArg (fun t => Q.quot.map (m.hom.pre.mapPath t))
        (Paths.lift_toPath c.backPre e).symm))

/-- **Reading back is natural for a map of contractions** — on the nose, no coherence. -/
theorem backSpelling_functor_naturality :
    m.poly.functor ⋙ c'.backSpelling.functor = c.backSpelling.functor ⋙ m.hom.functor :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e =>
    heq_of_eq (m.backSpelling_functor_map_quot e)

/-! ## The laws -/

/-- The identity. -/
def id (c : Contraction P S) : Map c c where
  hom := 𝟙 P
  mem_iff _ := Iff.rfl
  rep_hom _ := rfl
  word_hom x := (Prefunctor.mapPath_id (c.word x)).trans (cellCongr_self Quiver.Path _ _ _).symm
  invWord_hom x :=
    (Prefunctor.mapPath_id (c.invWord x)).trans (cellCongr_self Quiver.Path _ _ _).symm

/-- Composition. -/
def comp (m : Map c c') (m' : Map c' c'') : Map c c'' where
  hom := m.hom ≫ m'.hom
  mem_iff g := (m'.mem_iff _).trans (m.mem_iff g)
  rep_hom x := (m'.rep_hom (m.obj x)).trans (congrArg m'.obj (m.rep_hom x))
  word_hom x := by
    refine Eq.trans (show (m.hom ≫ m'.hom).pre.mapPath (c.word x)
        = m'.hom.pre.mapPath (m.hom.pre.mapPath (c.word x)) from
      Prefunctor.mapPath_comp_apply m.hom.pre m'.hom.pre (c.word x)) ?_
    refine Eq.trans (congrArg m'.hom.pre.mapPath (m.word_hom x)) ?_
    refine Eq.trans (Prefunctor.mapPath_cellCongr m'.hom.pre _ _ _) ?_
    refine Eq.trans (congrArg (cellCongr Quiver.Path _ _) (m'.word_hom (m.obj x))) ?_
    exact cellCongr_trans Quiver.Path _ _ _ _ _
  invWord_hom x := by
    refine Eq.trans (show (m.hom ≫ m'.hom).pre.mapPath (c.invWord x)
        = m'.hom.pre.mapPath (m.hom.pre.mapPath (c.invWord x)) from
      Prefunctor.mapPath_comp_apply m.hom.pre m'.hom.pre (c.invWord x)) ?_
    refine Eq.trans (congrArg m'.hom.pre.mapPath (m.invWord_hom x)) ?_
    refine Eq.trans (Prefunctor.mapPath_cellCongr m'.hom.pre _ _ _) ?_
    refine Eq.trans (congrArg (cellCongr Quiver.Path _ _) (m'.invWord_hom (m.obj x))) ?_
    exact cellCongr_trans Quiver.Path _ _ _ _ _

theorem poly_id : (Map.id c).poly = 𝟙 c.poly := rfl

theorem poly_comp (m : Map c c') (m' : Map c' c'') : (m.comp m').poly = m.poly ≫ m'.poly := rfl

/-- **A family of contractions along a functor into `Polygraph` is a functor** — the two laws are
the underlying functor's, a map being its map of polygraphs. -/
noncomputable def polyFunctor {D : Type u} [Category.{v} D] (G : D ⥤ Polygraph.{w, u', w₂})
    (Sd : ∀ d : D, ∀ {a b : (G.obj d).V}, (G.obj d).Gen a b → Prop)
    (cd : ∀ d : D, Contraction (G.obj d) (Sd d))
    (M : ∀ {d d' : D}, (d ⟶ d') → Map (cd d) (cd d'))
    (hM : ∀ {d d' : D} (u : d ⟶ d'), (M u).hom = G.map u) :
    D ⥤ Polygraph.{max u' w, u', max u' w₂} where
  obj d := (cd d).poly
  map u := (M u).poly
  map_id d := (congrArg Map.poly (Map.ext ((hM (𝟙 d)).trans (G.map_id d)))).trans poly_id
  map_comp u v :=
    (congrArg Map.poly
        (Map.ext ((hM (u ≫ v)).trans ((G.map_comp u v).trans
          (congrArg₂ CategoryStruct.comp (hM u).symm (hM v).symm))))).trans
      (poly_comp (M u) (M v))

end Map

end Contraction

end CategoryTheory
