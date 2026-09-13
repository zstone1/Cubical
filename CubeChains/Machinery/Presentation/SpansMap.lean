import CubeChains.Machinery.Presentation.Reduce

/-!
# Machinery/Presentation/SpansMap — a span is functorial in the polygraph

A map of polygraphs *preserving* the two kept families and carrying each chosen word to the chosen
word induces a map of the sub-polygraphs.  The square below is `Map.pre_mapPath_subWords`, and the
two boundary laws of `Map.poly` are it read at a 2-cell's source and target word.

                     s.subWords
    P.Word ───────────────────────▸ Paths (GenObj (keptGen T₁))
      │ m.hom.words                     │ m.pre
      ▾                                 ▾
    Q.Word ───────────────────────▸ Paths (GenObj (keptGen U₁))
                     s'.subWords

It commutes on the nose, so `poly` needs no transport: `Polygraph.Hom`'s boundary laws are equations
of words, which is why `word_hom` cannot be weakened to an equation in `Q.presented`.
-/

universe w u' w₂ v u

namespace CategoryTheory

namespace Spans

variable {P Q R : Polygraph.{w, u', w₂}}
  {T₁ : ∀ {a b : P.V}, P.Gen a b → Prop} {T₂ : ∀ {x y : GenObj P.Gen}, P.Rel x y → Prop}
  {U₁ : ∀ {a b : Q.V}, Q.Gen a b → Prop} {U₂ : ∀ {x y : GenObj Q.Gen}, Q.Rel x y → Prop}
  {V₁ : ∀ {a b : R.V}, R.Gen a b → Prop} {V₂ : ∀ {x y : GenObj R.Gen}, R.Rel x y → Prop}
  {s : Spans P T₁ T₂} {s' : Spans Q U₁ U₂} {s'' : Spans R V₁ V₂}

/-- **Data carrying one span to another**: a map of polygraphs preserving both kept families and
spelling each chosen word by the chosen word. -/
structure Map (s : Spans P T₁ T₂) (s' : Spans Q U₁ U₂) where
  /-- the map of polygraphs -/
  hom : P ⟶ Q
  /-- …which keeps a kept 1-cell -/
  mem_one {a b : P.V} {g : P.Gen a b} : T₁ g → U₁ (hom.pre.map (Polygraph.cell g))
  /-- …and a kept 2-cell -/
  mem_two {x y : GenObj P.Gen} {α : P.Rel x y} : T₂ α → U₂ (hom.two α)
  /-- …and carries the chosen word to the chosen word -/
  word_hom {a b : P.V} (g : P.Gen a b) :
    hom.pre.mapPath (s.word g) = s'.word (hom.pre.map (Polygraph.cell g))

namespace Map

variable (m : Map s s')

/-- **A map is its map of polygraphs** — the other three fields are propositions. -/
theorem ext : ∀ {m m' : Map s s'}, m.hom = m'.hom → m = m'
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by subst h; rfl

/-! ## The kept 1-cells, carried along -/

/-- **The kept 1-cells, carried along** — the same 0-cells, and a kept 1-cell stays kept. -/
def pre : GenObj (keptGen T₁) ⥤q GenObj (keptGen U₁) where
  obj x := ⟨(m.hom.pre.obj ⟨x.as⟩).as⟩
  map e := ⟨m.hom.pre.map (Polygraph.cell e.1), m.mem_one e.2⟩

/-- **…over the map of polygraphs**, which is the whole of the two squares below. -/
theorem pre_comp_keptPre : m.pre ⋙q keptPre U₁ = keptPre T₁ ⋙q m.hom.pre := rfl

theorem keptPre_mapPath_pre {x y : GenObj (keptGen T₁)} (w : Quiver.Path x y) :
    (keptPre U₁).mapPath (m.pre.mapPath w) = m.hom.pre.mapPath ((keptPre T₁).mapPath w) :=
  (Prefunctor.mapPath_comp_apply m.pre (keptPre U₁) w).symm.trans
    ((eq_of_heq (Prefunctor.mapPath_heq_of_eq m.pre_comp_keptPre w)).trans
      (Prefunctor.mapPath_comp_apply (keptPre T₁) m.hom.pre w))

/-- **The substitution squares with the map, on a letter** — `word_hom`, read on the kept
1-cells. -/
theorem pre_mapPath_subPre {x y : GenObj P.Gen} (g : x ⟶ y) :
    m.pre.mapPath (s.pre.map g) = s'.pre.map (m.hom.pre.map g) :=
  keptPre_mapPath_injective U₁
    (((m.keptPre_mapPath_pre _).trans
        (congrArg m.hom.pre.mapPath (keptPre_mapPath_keptWord T₁ (s.word g) (s.word_all g)))).trans
      ((m.word_hom g).trans
        (keptPre_mapPath_keptWord U₁ (s'.word (m.hom.pre.map g)) (s'.word_all _)).symm))

/-- **…and on a whole word.** -/
theorem pre_mapPath_subWords : ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y),
    m.pre.mapPath (s.subWords.map u) = s'.subWords.map (m.hom.pre.mapPath u) := by
  intro x y u
  induction u with
  | nil => rfl
  | cons u e ih =>
      refine Eq.trans (congrArg m.pre.mapPath (Paths.lift_cons s.pre u e)) ?_
      refine Eq.trans (Prefunctor.mapPath_comp m.pre (s.subWords.map u) (s.pre.map e)) ?_
      refine Eq.trans (congrArg₂ Quiver.Path.comp ih (m.pre_mapPath_subPre e)) ?_
      exact (Paths.lift_cons s'.pre (m.hom.pre.mapPath u) (m.hom.pre.map e)).symm

/-- **The sub-polygraph, on a map.** -/
def poly : s.poly ⟶ s'.poly where
  pre := m.pre
  two α := ⟨m.hom.two α.1, m.mem_two α.2⟩
  src_two α := (congrArg s'.subWords.map (m.hom.src_two α.1)).trans
    (m.pre_mapPath_subWords (P.src α.1)).symm
  tgt_two α := (congrArg s'.subWords.map (m.hom.tgt_two α.1)).trans
    (m.pre_mapPath_subWords (P.tgt α.1)).symm

@[simp] theorem poly_pre : m.poly.pre = m.pre := rfl

/-! ## …and the inclusion is natural for it -/

/-- **Including the kept cells commutes with the map, on a word.** -/
theorem incl_functor_map_quot {x y : GenObj s.poly.Gen} (u : Quiver.Path x y) :
    s'.incl.functor.map (m.poly.functor.map (s.poly.quot.map u))
      = m.hom.functor.map (s.incl.functor.map (s.poly.quot.map u)) :=
  ((s'.incl_functor_quot (m.pre.mapPath u)).trans
      (congrArg Q.quot.map (m.keptPre_mapPath_pre u))).trans
    (congrArg m.hom.functor.map (s.incl_functor_quot u)).symm

/-- **…so the sub-polygraph lies over the polygraph it spans** — `pre_comp_keptPre`, read in the
presented categories. -/
theorem incl_functor_naturality :
    m.poly.functor ⋙ s'.incl.functor = s.incl.functor ⋙ m.hom.functor :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e =>
    heq_of_eq (m.incl_functor_map_quot e.toPath)

/-! ## The laws -/

/-- The identity. -/
def id (s : Spans P T₁ T₂) : Map s s where
  hom := 𝟙 P
  mem_one h := h
  mem_two h := h
  word_hom g := Prefunctor.mapPath_id (s.word g)

/-- Composition. -/
def comp (m : Map s s') (m' : Map s' s'') : Map s s'' where
  hom := m.hom ≫ m'.hom
  mem_one h := m'.mem_one (m.mem_one h)
  mem_two h := m'.mem_two (m.mem_two h)
  word_hom g :=
    (Prefunctor.mapPath_comp_apply m.hom.pre m'.hom.pre (s.word g)).trans
      ((congrArg m'.hom.pre.mapPath (m.word_hom g)).trans
        (m'.word_hom (m.hom.pre.map (Polygraph.cell g))))

theorem poly_id : (Map.id s).poly = 𝟙 s.poly := rfl

theorem poly_comp (m : Map s s') (m' : Map s' s'') : (m.comp m').poly = m.poly ≫ m'.poly := rfl

/-- **A family of spans along a functor into `Polygraph` is a functor** — the two laws are the
underlying functor's, a map being its map of polygraphs. -/
def polyFunctor {D : Type u} [Category.{v} D] (G : D ⥤ Polygraph.{w, u', w₂})
    (T₁ : ∀ d : D, ∀ {a b : (G.obj d).V}, (G.obj d).Gen a b → Prop)
    (T₂ : ∀ d : D, ∀ {x y : GenObj (G.obj d).Gen}, (G.obj d).Rel x y → Prop)
    (sd : ∀ d : D, Spans (G.obj d) (T₁ d) (T₂ d))
    (M : ∀ {d d' : D}, (d ⟶ d') → Map (sd d) (sd d'))
    (hM : ∀ {d d' : D} (u : d ⟶ d'), (M u).hom = G.map u) :
    D ⥤ Polygraph.{w, u', w₂} where
  obj d := (sd d).poly
  map u := (M u).poly
  map_id d := (congrArg Map.poly (Map.ext ((hM (𝟙 d)).trans (G.map_id d)))).trans poly_id
  map_comp u v :=
    (congrArg Map.poly
        (Map.ext ((hM (u ≫ v)).trans ((G.map_comp u v).trans
          (congrArg₂ CategoryStruct.comp (hM u).symm (hM v).symm))))).trans
      (poly_comp (M u) (M v))

end Map

end Spans

end CategoryTheory
