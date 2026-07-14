import CubeChains.Flow.ChainConcat
import CubeChains.Salvetti.FreeGroupoidProd

/-!
# Flow/Flow — the directed flow 2-category of `K`

    0-cells  vertices of `K`
    1-cells  `u ⟶ v` = executions from `u` to `v`: a cube chain `a` together with a *line*
             `L : LinesObj a` (a chamber per bead — the order its concurrent events fire)
    2-cells  braids: the morphisms of `ConcGrpd (K.repoint u v)`

Composition of 1-cells is concatenation: dimension sequences append (`List.append`), the two
classifying maps glue at the junction vertex, and the lines pair up.  It is **strict** — no
associator, no unitors — because `List.append` is strictly associative and unital.

`flowHom K u v = ConcGrpd (K.repoint u v)`, so `flowHom K K.init K.final = ConcGrpd K`.

Everything here is unconditional: no `NonSelfLinked`, no `AdmitsAltitude`, no thinness.

By `concGrpdRunEquiv` (`Salvetti/Normalize`) every 1-cell is 2-isomorphic to a **run** (a word in
edges), so this enrichment is equivalent to the one whose 1-cells are runs; the `(chain, line)`
model is the one to *build* (composition is definitional on it), the run model the one to *think*
in.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace CubeChains

open ChainCat CubeChain

/-! ## Chambers of a dimension sequence, and their concatenation

`LinesObj a` reads only `a.dims`, so it is really a function of a `List ℕ+`; and `dims` concatenate.
The recursion below is written so that every type equality is definitional
(`(n :: A) ++ B ≡ n :: (A ++ B)`, `(n :: L).get 0 ≡ n`, `(n :: L).get j.succ ≡ L.get j`) — hence no
casts inside `chambersConcat`. -/

/-- One chamber per entry of a dimension sequence: `LinesObj a` *is* `Chambers a.dims`. -/
def Chambers (d : List ℕ+) : Type := ∀ i : Fin d.length, Chamber ((d.get i : ℕ))

/-- Transport a chamber along an equality of dimensions (a `restrict` along `Fin.cast`). -/
def Chamber.castDim {d e : ℕ} (h : d = e) (c : Chamber e) : Chamber d :=
  c.restrict (Fin.cast h) (by subst h; intro a b hab; simpa using hab)

theorem Chamber.castDim_self {d : ℕ} (h : d = d) (c : Chamber d) : c.castDim h = c :=
  c.restrict_id_of _ (fun _ => rfl)

/-- **Concatenation of lines**: each bead of `A ++ B` keeps its own factor's chamber. -/
def chambersConcat : (A B : List ℕ+) → Chambers A → Chambers B → Chambers (A ++ B)
  | [], _, _, M => M
  | n :: A', B, L, M =>
      Fin.cases (motive := fun i => Chamber ((((n :: A') ++ B).get i : ℕ)))
        (L 0) (fun j => chambersConcat A' B (fun k => L k.succ) M j)

/-! ### The two block index maps of an append -/

/-- The index of the `i`-th `A`-bead inside `A ++ B`. -/
def lidx : (A B : List ℕ+) → Fin A.length → Fin (A ++ B).length
  | [], _, i => i.elim0
  | _ :: A', B, i =>
      Fin.cases (0 : Fin ((A' ++ B).length + 1)) (fun j => (lidx A' B j).succ) i

/-- The index of the `j`-th `B`-bead inside `A ++ B`. -/
def ridx : (A B : List ℕ+) → Fin B.length → Fin (A ++ B).length
  | [], _, j => j
  | _ :: A', B, j => (ridx A' B j).succ

theorem get_lidx : ∀ (A B : List ℕ+) (i : Fin A.length),
    (A ++ B).get (lidx A B i) = A.get i
  | [], _, i => i.elim0
  | n :: A', B, i => by
      induction i using Fin.cases with
      | zero => rfl
      | succ j => exact get_lidx A' B j

theorem get_ridx : ∀ (A B : List ℕ+) (j : Fin B.length),
    (A ++ B).get (ridx A B j) = B.get j
  | [], _, _ => rfl
  | _ :: A', B, j => get_ridx A' B j

/-- Every bead of `A ++ B` is a bead of `A` or a bead of `B`. -/
theorem lidx_or_ridx : ∀ (A B : List ℕ+) (i : Fin (A ++ B).length),
    (∃ ia, i = lidx A B ia) ∨ (∃ jb, i = ridx A B jb)
  | [], _, i => Or.inr ⟨i, rfl⟩
  | n :: A', B, i => by
      induction i using Fin.cases with
      | zero => exact Or.inl ⟨0, rfl⟩
      | succ j =>
          rcases lidx_or_ridx A' B j with ⟨ia, hia⟩ | ⟨jb, hjb⟩
          · exact Or.inl ⟨ia.succ, by rw [show lidx (n :: A') B ia.succ
              = (lidx A' B ia).succ from rfl, ← hia]⟩
          · exact Or.inr ⟨jb, by rw [show ridx (n :: A') B jb
              = (ridx A' B jb).succ from rfl, ← hjb]⟩

/-! ### `chambersConcat` on the two blocks -/

theorem chambersConcat_lidx : ∀ (A B : List ℕ+) (L : Chambers A) (M : Chambers B)
    (i : Fin A.length),
    chambersConcat A B L M (lidx A B i)
      = Chamber.castDim (congrArg (fun c : ℕ+ => (c : ℕ)) (get_lidx A B i)) (L i)
  | [], _, _, _, i => i.elim0
  | n :: A', B, L, M, i => by
      induction i using Fin.cases with
      | zero => exact ((L 0).castDim_self _).symm
      | succ j => exact chambersConcat_lidx A' B (fun k => L k.succ) M j

theorem chambersConcat_ridx : ∀ (A B : List ℕ+) (L : Chambers A) (M : Chambers B)
    (j : Fin B.length),
    chambersConcat A B L M (ridx A B j)
      = Chamber.castDim (congrArg (fun c : ℕ+ => (c : ℕ)) (get_ridx A B j)) (M j)
  | [], _, _, M, j => ((M j).castDim_self _).symm
  | _ :: A', B, L, M, j => chambersConcat_ridx A' B (fun k => L k.succ) M j

/-! ## The bead inclusions of an appended wedge -/

/-- The box equality behind `lidx`. -/
theorem box_lidx (A B : List ℕ+) (i : Fin A.length) :
    ▫(((A ++ B).get (lidx A B i) : ℕ)) = ▫((A.get i : ℕ)) :=
  congrArg (fun c : ℕ+ => ▫(c : ℕ)) (get_lidx A B i)

/-- The box equality behind `ridx`. -/
theorem box_ridx (A B : List ℕ+) (j : Fin B.length) :
    ▫(((A ++ B).get (ridx A B j) : ℕ)) = ▫((B.get j : ℕ)) :=
  congrArg (fun c : ℕ+ => ▫(c : ℕ)) (get_ridx A B j)

/-- The `A`-beads of `⋁(A ++ B)` are the beads of `⋁A`, pushed in along `wedgeInclL`. -/
theorem ι_lidx : ∀ (A B : List ℕ+) (i : Fin A.length),
    ιᵂ (A ++ B) (lidx A B i)
      = yoneda.map (eqToHom (box_lidx A B i)) ≫ ιᵂ A i ≫ wedgeInclL A B
  | [], _, i => i.elim0
  | n :: A', B, i => by
      induction i using Fin.cases with
      | zero =>
          have h0 : yoneda.map (eqToHom (box_lidx (n :: A') B 0))
              = 𝟙 ((□(n : ℕ)).toPsh) := yoneda.map_id ▫((n : ℕ))
          rw [h0]
          erw [Category.id_comp]
          exact (inl_wedgeInclL_cons n A' B).symm
      | succ j =>
          have key : ιᵂ (n :: A') j.succ ≫ wedgeInclL (n :: A') B
              = (ιᵂ A' j ≫ wedgeInclL A' B)
                ≫ pushout.inr (□(n : ℕ)).finalVertex (⋁(A' ++ B)).initVertex :=
            ((Category.assoc (ιᵂ A' j)
                  (pushout.inr (□(n : ℕ)).finalVertex (⋁A').initVertex)
                  (wedgeInclL (n :: A') B)).trans
                (congrArg (fun t => ιᵂ A' j ≫ t) (inr_wedgeInclL_cons n A' B))).trans
              (Category.assoc (ιᵂ A' j) (wedgeInclL A' B)
                (pushout.inr (□(n : ℕ)).finalVertex (⋁(A' ++ B)).initVertex)).symm
          exact (congrArg (· ≫ pushout.inr (□(n : ℕ)).finalVertex (⋁(A' ++ B)).initVertex)
              (ι_lidx A' B j)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun t => yoneda.map (eqToHom (box_lidx A' B j)) ≫ t) key.symm))

/-- The `B`-beads of `⋁(A ++ B)` are the beads of `⋁B`, pushed in along `wedgeInclR`. -/
theorem ι_ridx : ∀ (A B : List ℕ+) (j : Fin B.length),
    ιᵂ (A ++ B) (ridx A B j)
      = yoneda.map (eqToHom (box_ridx A B j)) ≫ ιᵂ B j ≫ wedgeInclR A B
  | [], B, j => by
      have h0 : yoneda.map (eqToHom (box_ridx [] B j))
          = 𝟙 ((□((B.get j : ℕ))).toPsh) := yoneda.map_id ▫(((B.get j) : ℕ))
      rw [h0]
      exact (Category.comp_id (ιᵂ B j)).symm.trans (Category.id_comp _).symm
  | n :: A', B, j => by
      have key : ιᵂ B j ≫ wedgeInclR (n :: A') B
          = (ιᵂ B j ≫ wedgeInclR A' B)
            ≫ pushout.inr (□(n : ℕ)).finalVertex (⋁(A' ++ B)).initVertex :=
        (Category.assoc _ _ _).symm
      exact (congrArg (· ≫ pushout.inr (□(n : ℕ)).finalVertex (⋁(A' ++ B)).initVertex)
          (ι_ridx A' B j)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => yoneda.map (eqToHom (box_ridx A' B j)) ≫ t) key.symm))

/-! ## Lines restrict blockwise along a concatenated chain map

The heart of the enrichment: a refinement of each factor restricts the concatenated line to the
concatenation of the restricted lines.  Both block cases go through `restrict_factor`, fed the
factorisation of a bead's inclusion through `wedgeInclL`/`wedgeInclR` (`ι_lidx`/`ι_ridx`) and the
block data of the factor (`blockFace_spec`). -/

variable {K : BPSet}

/-- `faceEmb` of an `eqToHom`-conjugate keeps the underlying value. -/
private theorem faceEmb_conj {d e m m' : ℕ} (p : ▫d = ▫e) (t : ▫e ⟶ ▫m) (q : ▫m = ▫m')
    (x : Fin d) (y : Fin e) (hxy : (y : ℕ) = (x : ℕ)) :
    ((faceEmb (eqToHom p ≫ t ≫ eqToHom q)) x : ℕ) = (faceEmb t y : ℕ) := by
  rw [faceEmb_comp, faceEmb_comp, faceEmb_eqToHom_val]
  rw [show faceEmb (eqToHom p) x = y from Fin.ext ((faceEmb_eqToHom_val p x).trans hxy.symm)]

/-- A bead of `⋁A` reaches its block of `⋁(A ++ B)` through `wedgeInclL`, inverted. -/
private theorem ι_lidx' (A B : List ℕ+) (r : Fin A.length) :
    ιᵂ A r ≫ wedgeInclL A B
      = yoneda.map (eqToHom (box_lidx A B r).symm) ≫ ιᵂ (A ++ B) (lidx A B r) := by
  rw [ι_lidx A B r, ← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- A bead of `⋁B` reaches its block of `⋁(A ++ B)` through `wedgeInclR`, inverted. -/
private theorem ι_ridx' (A B : List ℕ+) (r : Fin B.length) :
    ιᵂ B r ≫ wedgeInclR A B
      = yoneda.map (eqToHom (box_ridx A B r).symm) ≫ ιᵂ (A ++ B) (ridx A B r) := by
  rw [ι_ridx A B r, ← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The definitional unfolding of `linesRestrict` at a bead. -/
theorem linesRestrict_bead {a b : Ch K} (p : a ⟶ b) (L : LinesObj b) (i : ChainCat.Bead a) :
    linesRestrict p L i
      = (L (blockIdx pᵂ i)).restrict (faceEmb (blockFace pᵂ i))
          (faceEmb (blockFace pᵂ i)).injective :=
  rfl

/-- **The concatenated line restricts blockwise.** -/
theorem linesRestrict_chConcMor {u v w : K.cells 0}
    {a a' : Ch (K.repoint u v)} {b b' : Ch (K.repoint v w)}
    (f : a' ⟶ a) (g : b' ⟶ b) (L : LinesObj a) (M : LinesObj b) :
    linesRestrict (chConcMor f g) (chambersConcat a.dims b.dims L M)
      = chambersConcat a'.dims b'.dims (linesRestrict f L) (linesRestrict g M) := by
  funext i
  rcases lidx_or_ridx a'.dims b'.dims i with ⟨ia, rfl⟩ | ⟨jb, rfl⟩
  · -- `A`-block
    have hfact : ιᵂ (a'.dims ++ b'.dims) (lidx a'.dims b'.dims ia) ≫ (concatHomφ f g).hom
        = yoneda.map (eqToHom (box_lidx a'.dims b'.dims ia)
            ≫ blockFace (ChainCat.Hom.φ f).hom ia
            ≫ eqToHom (box_lidx a.dims b.dims (blockIdx (ChainCat.Hom.φ f).hom ia)).symm)
          ≫ ιᵂ (a.dims ++ b.dims) (lidx a.dims b.dims (blockIdx (ChainCat.Hom.φ f).hom ia)) := by
      rw [ι_lidx a'.dims b'.dims ia, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp]
      erw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
        concatHomφ_inclL f g,
        reassoc_of% (blockFace_spec (ChainCat.Hom.φ f).hom ia), Category.assoc,
        ι_lidx' a.dims b.dims (blockIdx (ChainCat.Hom.φ f).hom ia)]
      rfl
    have h1 := restrict_factor (concatHomφ f g).hom (lidx a'.dims b'.dims ia)
      (lidx a.dims b.dims (blockIdx (ChainCat.Hom.φ f).hom ia)) _ hfact
      (chambersConcat a.dims b.dims L M)
    rw [linesRestrict_bead, chConcMor_φ]
    refine h1.trans ?_
    rw [chambersConcat_lidx a.dims b.dims L M _,
      chambersConcat_lidx a'.dims b'.dims (linesRestrict f L) (linesRestrict g M) ia,
      linesRestrict_bead]
    simp only [Chamber.castDim]
    rw [Chamber.restrict_restrict, Chamber.restrict_restrict]
    exact Chamber.restrict_congr (L (blockIdx (ChainCat.Hom.φ f).hom ia)) _ _
      (fun x => Fin.ext (faceEmb_conj (box_lidx a'.dims b'.dims ia)
        (blockFace (ChainCat.Hom.φ f).hom ia)
        (box_lidx a.dims b.dims (blockIdx (ChainCat.Hom.φ f).hom ia)).symm
        x (Fin.cast (congrArg (fun c : ℕ+ => (c : ℕ)) (get_lidx a'.dims b'.dims ia)) x) rfl))
  · -- `B`-block
    have hfact : ιᵂ (a'.dims ++ b'.dims) (ridx a'.dims b'.dims jb) ≫ (concatHomφ f g).hom
        = yoneda.map (eqToHom (box_ridx a'.dims b'.dims jb)
            ≫ blockFace (ChainCat.Hom.φ g).hom jb
            ≫ eqToHom (box_ridx a.dims b.dims (blockIdx (ChainCat.Hom.φ g).hom jb)).symm)
          ≫ ιᵂ (a.dims ++ b.dims) (ridx a.dims b.dims (blockIdx (ChainCat.Hom.φ g).hom jb)) := by
      rw [ι_ridx a'.dims b'.dims jb, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp]
      erw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
        concatHomφ_inclR f g,
        reassoc_of% (blockFace_spec (ChainCat.Hom.φ g).hom jb), Category.assoc,
        ι_ridx' a.dims b.dims (blockIdx (ChainCat.Hom.φ g).hom jb)]
      rfl
    have h1 := restrict_factor (concatHomφ f g).hom (ridx a'.dims b'.dims jb)
      (ridx a.dims b.dims (blockIdx (ChainCat.Hom.φ g).hom jb)) _ hfact
      (chambersConcat a.dims b.dims L M)
    rw [linesRestrict_bead, chConcMor_φ]
    refine h1.trans ?_
    rw [chambersConcat_ridx a.dims b.dims L M _,
      chambersConcat_ridx a'.dims b'.dims (linesRestrict f L) (linesRestrict g M) jb,
      linesRestrict_bead]
    simp only [Chamber.castDim]
    rw [Chamber.restrict_restrict, Chamber.restrict_restrict]
    exact Chamber.restrict_congr (M (blockIdx (ChainCat.Hom.φ g).hom jb)) _ _
      (fun x => Fin.ext (faceEmb_conj (box_ridx a'.dims b'.dims jb)
        (blockFace (ChainCat.Hom.φ g).hom jb)
        (box_ridx a.dims b.dims (blockIdx (ChainCat.Hom.φ g).hom jb)).symm
        x (Fin.cast (congrArg (fun c : ℕ+ => (c : ℕ)) (get_ridx a'.dims b'.dims jb)) x) rfl))

/-! ## Composition of executions: the flow 2-category

`concConc` composes 1-cells; `concGrpdConc` is its groupoidification — the enrichment's `comp`. -/

/-- The identity 1-cell at a vertex: the empty chain with its (empty) line. -/
noncomputable def concId (K : BPSet) (v : K.cells 0) : ConcCat (K.repoint v v) :=
  ⟨op (chId K v), fun i => i.elim0⟩

/-- **Composition of executions** `ConcCat (K;u,v) × ConcCat (K;v,w) ⥤ ConcCat (K;u,w)`: chains
concatenate, lines pair up. -/
noncomputable def concConc (K : BPSet) (u v w : K.cells 0) :
    ConcCat (K.repoint u v) × ConcCat (K.repoint v w) ⥤ ConcCat (K.repoint u w) where
  obj p := ⟨op (chConc p.1.1.unop p.2.1.unop),
    chambersConcat (p.1.1.unop).dims (p.2.1.unop).dims p.1.2 p.2.2⟩
  map {p q} fg :=
    ⟨(chConcMor fg.1.1.unop fg.2.1.unop).op, by
      have e1 : linesRestrict (fg.1.1.unop) p.1.2 = q.1.2 := fg.1.2
      have e2 : linesRestrict (fg.2.1.unop) p.2.2 = q.2.2 := fg.2.2
      have h := linesRestrict_chConcMor fg.1.1.unop fg.2.1.unop p.1.2 p.2.2
      rw [e1, e2] at h
      exact h⟩
  map_id p := by
    apply Subtype.ext
    exact congrArg Quiver.Hom.op (chConcMor_id (p.1.1.unop) (p.2.1.unop))
  map_comp {p q r} fg gh := by
    apply Subtype.ext
    exact congrArg Quiver.Hom.op
      (chConcMor_comp (gh.1.1.unop) (fg.1.1.unop) (gh.2.1.unop) (fg.2.1.unop))

/-- The composition of executions, groupoidified: **the enrichment's composition law**.
`freeGroupoidProdEquiv` is exactly what lets `FreeGroupoid.map concConc` be read on the *product* of
the two hom-groupoids. -/
noncomputable def concGrpdConc (K : BPSet) (u v w : K.cells 0) :
    ConcGrpd (K.repoint u v) × ConcGrpd (K.repoint v w) ⥤ ConcGrpd (K.repoint u w) :=
  (freeGroupoidProdEquiv (ConcCat (K.repoint u v)) (ConcCat (K.repoint v w))).inverse
    ⋙ FreeGroupoid.map (concConc K u v w)

/-- The hom-groupoid of the flow 2-category: the concurrency braid groupoid of the executions
`u ⟶ v`.  `flowHom K K.init K.final = ConcGrpd K`. -/
abbrev flowHom (K : BPSet) (u v : K.cells 0) : Type _ := ConcGrpd (K.repoint u v)

/-- The identity 2-cell datum: the identity 1-cell at `v`, as an object of `flowHom K v v`. -/
noncomputable def flowId (K : BPSet) (v : K.cells 0) : flowHom K v v :=
  FreeGroupoid.mk (concId K v)

/-- The composition of the flow 2-category. -/
noncomputable def flowComp (K : BPSet) (u v w : K.cells 0) :
    flowHom K u v × flowHom K v w ⥤ flowHom K u w :=
  concGrpdConc K u v w

end CubeChains
