import CubeChains.Chains.WedgeHom
import Mathlib.Logic.Equiv.Sum
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Chains/WedgeExtend — lifting a (co)presheaf on `Box` to serial wedges

Both variances of the same slogan: a functor on cubes extends, *functorially in every wedge map*,
to the serial wedges — because `⋁a` is an (iterated) colimit of cubes and the extension is the
(co)tensor with the wedge.  `Salvetti/Runs` is the instance `F = runPresheaf` of the contravariant
half; this file is the abstraction, with the covariant half added.

* **Contravariant** (a presheaf `F : Boxᵒᵖ ⥤ Type`): `F↑ X := (X.toPsh ⟶ F)`, the lift is
  precomposition (`pshExtRestrict`), and — the "`Run` is monoidal" content — `F↑ (X ∨ Y) ≃
  F↑ X × F↑ Y` when `F` has a single vertex (`pshExtWedge2`, iterated to `pshExtProd`).  Nothing is
  computed down to a product of bead-values unless you ask: the classifying object is `F↑ (⋁a)`.

* **Covariant** (a copresheaf `F : Box ⥤ Type`): `F↓ X := X.toPsh ⊗_Box F`, the *cubical coend*
  `∫^n X(n) × F(n)` built as a plain `Quot` (computable — no `Functor.lan`), the lift is the
  functoriality of the coend in `X` (`Cotensor.map`), and the bead value is recovered by co-Yoneda
  (`Cotensor.cubeEquiv`).  A generator `⟨n, x, y⟩` is an element of the category of elements of `X`
  decorated by `F`; the relation is the morphisms of that category.

The two decompositions are one duality.  `F↑` turns the wedge *colimit* into a *limit* and `F↓`
into a *colimit*; the condition on `F ▫0` degenerates each:

* `F ▫0` a **point** (single vertex) ⟹ `F↑ (⋁a)` is the **product** `∏ᵢ F ▫aᵢ` (`pshExtProd`);
* `F ▫0` **empty** ⟹ `F↓ (⋁a)` is the **coproduct** `⊕ᵢ F ▫aᵢ` (`wedgeCoprodEquiv`) — the
  concrete, quotient-free presentation of a `Cotensor` (a shared vertex would decorate an empty
  cell, so a coend class lives on exactly one bead).
-/

open CategoryTheory Opposite BPSet

namespace ChainCat

/-! ## The covariant lift `F↓ X = X ⊗_Box F` — a cubical coend

`∫^n X(n) × F(n)` as a `Quot`.  The forward functoriality in `X` is what lifts a wedge map, and it
is free (post-compose the `X`-cell); co-Yoneda collapses the coend at a cube to the bead value. -/

/-- A generator of the coend `X ⊗_Box F`: an `n`-cell of `X` decorated by an element of `F ▫n`. -/
abbrev CotensorGen (F : Box ⥤ Type) (X : PrecubicalSet) : Type :=
  Σ n : ℕ, X.obj (op ▫n) × F.obj ▫n

/-- The coend (dinaturality) relation: restricting the `X`-cell along `φ` equals pushing the
`F`-decoration along `φ`.  These are exactly the morphisms of `X`'s category of elements. -/
inductive CotensorRel (F : Box ⥤ Type) (X : PrecubicalSet) :
    CotensorGen F X → CotensorGen F X → Prop
  | mk {n n' : ℕ} (φ : ▫n ⟶ ▫n') (x : X.obj (op ▫n')) (y : F.obj ▫n) :
      CotensorRel F X ⟨n, (X.map φ.op) x, y⟩ ⟨n', x, (F.map φ) y⟩

/-- `X ⊗_Box F` — the cubical coend of a precubical set `X` with a copresheaf `F`. -/
def Cotensor (F : Box ⥤ Type) (X : PrecubicalSet) : Type := Quot (CotensorRel F X)

/-- A decorated cell, as a coend class. -/
def Cotensor.mk (F : Box ⥤ Type) {X : PrecubicalSet} (n : ℕ) (x : X.obj (op ▫n))
    (y : F.obj ▫n) : Cotensor F X := Quot.mk _ ⟨n, x, y⟩

/-- **The coend identity.**  Restrict-then-decorate = decorate-then-push. -/
theorem Cotensor.map_mk (F : Box ⥤ Type) {X : PrecubicalSet} {n n' : ℕ} (φ : ▫n ⟶ ▫n')
    (x : X.obj (op ▫n')) (y : F.obj ▫n) :
    Cotensor.mk F n ((X.map φ.op) x) y = Cotensor.mk F n' x ((F.map φ) y) :=
  Quot.sound (CotensorRel.mk φ x y)

@[elab_as_elim]
theorem Cotensor.ind (F : Box ⥤ Type) {X : PrecubicalSet} {motive : Cotensor F X → Prop}
    (h : ∀ (n : ℕ) (x : X.obj (op ▫n)) (y : F.obj ▫n), motive (Cotensor.mk F n x y)) :
    ∀ t, motive t := fun t => Quot.ind (fun p => h p.1 p.2.1 p.2.2) t

/-- **Functoriality of the coend in `X`** — precompose the `X`-cell with `g`.  This is the whole
lift; it needs nothing but naturality of `g`. -/
def Cotensor.map (F : Box ⥤ Type) {X Y : PrecubicalSet} (g : X ⟶ Y) :
    Cotensor F X → Cotensor F Y :=
  Quot.lift (fun p => Cotensor.mk F p.1 (g⟪p.1⟫ p.2.1) p.2.2) <| by
    rintro _ _ ⟨φ, x, y⟩
    change Cotensor.mk F _ (g⟪_⟫ ((X.map φ.op) x)) y = Cotensor.mk F _ (g⟪_⟫ x) ((F.map φ) y)
    rw [NatTrans.naturality_apply g φ.op x]
    exact Cotensor.map_mk F φ (g⟪_⟫ x) y

@[simp] theorem Cotensor.map_apply (F : Box ⥤ Type) {X Y : PrecubicalSet} (g : X ⟶ Y)
    (n : ℕ) (x : X.obj (op ▫n)) (y : F.obj ▫n) :
    Cotensor.map F g (Cotensor.mk F n x y) = Cotensor.mk F n (g⟪n⟫ x) y := rfl

theorem Cotensor.map_id (F : Box ⥤ Type) (X : PrecubicalSet) :
    Cotensor.map F (𝟙 X) = id := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Cotensor.map_apply, id_eq, NatTrans.id_app, types_id_apply]

theorem Cotensor.map_comp (F : Box ⥤ Type) {X Y Z : PrecubicalSet} (g : X ⟶ Y) (h : Y ⟶ Z) :
    Cotensor.map F (g ≫ h) = Cotensor.map F h ∘ Cotensor.map F g := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Function.comp_apply, Cotensor.map_apply, NatTrans.comp_app, types_comp_apply]

/-- **The coend as a bundled functor** `PrecubicalSet ⥤ Type`. -/
def CotensorFunctor (F : Box ⥤ Type) : PrecubicalSet ⥤ Type where
  obj X := Cotensor F X
  map g := TypeCat.ofHom (Cotensor.map F g)
  map_id X := by
    apply ConcreteCategory.hom_ext; intro t
    change Cotensor.map F (𝟙 X) t = t
    simp only [Cotensor.map_id, id_eq]
  map_comp g h := by
    apply ConcreteCategory.hom_ext; intro t
    change Cotensor.map F (g ≫ h) t = Cotensor.map F h (Cotensor.map F g t)
    simp only [Cotensor.map_comp, Function.comp_apply]

/-- **The covariant lift** `F↓ : BPSet ⥤ Type`, `X ↦ X.toPsh ⊗_Box F`. -/
def cotensorLift (F : Box ⥤ Type) : BPSet ⥤ Type := BPSet.toPshFunctor ⋙ CotensorFunctor F

/-! ### Naturality of the coend in the coefficient `F`

The coend is functorial in the copresheaf too: a `NatTrans α : F ⟶ G` pushes the decoration by
`α.app`, untouched by the cell.  This is the dual factor to `Cotensor.map` (which touches the cell),
so the two commute — giving `cotensorLift` bundled over the coefficient. -/

/-- **Functoriality of the coend in `F`** — push the decoration along `α`. -/
def Cotensor.mapF (F G : Box ⥤ Type) (α : F ⟶ G) {X : PrecubicalSet} :
    Cotensor F X → Cotensor G X :=
  Quot.lift (fun p => Cotensor.mk G p.1 p.2.1 (α.app ▫p.1 p.2.2)) <| by
    rintro _ _ ⟨φ, x, y⟩
    change Cotensor.mk G _ ((X.map φ.op) x) (α.app ▫_ y)
      = Cotensor.mk G _ x (α.app ▫_ ((F.map φ) y))
    rw [NatTrans.naturality_apply α φ y]
    exact Cotensor.map_mk G φ x (α.app ▫_ y)

@[simp] theorem Cotensor.mapF_apply (F G : Box ⥤ Type) (α : F ⟶ G) {X : PrecubicalSet}
    (n : ℕ) (x : X.obj (op ▫n)) (y : F.obj ▫n) :
    Cotensor.mapF F G α (Cotensor.mk F n x y) = Cotensor.mk G n x (α.app ▫n y) := rfl

theorem Cotensor.mapF_id (F : Box ⥤ Type) (X : PrecubicalSet) :
    Cotensor.mapF F F (𝟙 F) = (id : Cotensor F X → Cotensor F X) := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Cotensor.mapF_apply, id_eq, NatTrans.id_app, types_id_apply]

theorem Cotensor.mapF_comp (F G H : Box ⥤ Type) (α : F ⟶ G) (β : G ⟶ H) (X : PrecubicalSet) :
    Cotensor.mapF F H (α ≫ β) = (Cotensor.mapF G H β ∘ Cotensor.mapF F G α :
      Cotensor F X → Cotensor H X) := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Function.comp_apply, Cotensor.mapF_apply, NatTrans.comp_app, types_comp_apply]

/-- **The coend bundled over the coefficient** `(Box ⥤ Type) ⥤ (BPSet ⥤ Type)`, `F ↦ F↓`.  The
naturality square is `Cotensor.mapF` (decoration) commuting with `Cotensor.map` (cell). -/
def cotensorLiftFunctor : (Box ⥤ Type) ⥤ (BPSet ⥤ Type) where
  obj F := cotensorLift F
  map {F G} α :=
    { app := fun X => TypeCat.ofHom (Cotensor.mapF F G α)
      naturality := fun {X Y} f => by
        apply ConcreteCategory.hom_ext; intro t
        refine Cotensor.ind F (fun n x y => ?_) t
        change Cotensor.mapF F G α (Cotensor.map F f.hom (Cotensor.mk F n x y))
          = Cotensor.map G f.hom (Cotensor.mapF F G α (Cotensor.mk F n x y))
        simp only [Cotensor.map_apply, Cotensor.mapF_apply] }
  map_id F := by
    apply NatTrans.ext; funext X
    apply ConcreteCategory.hom_ext; intro t
    exact congrFun (Cotensor.mapF_id F X.toPsh) t
  map_comp α β := by
    apply NatTrans.ext; funext X
    apply ConcreteCategory.hom_ext; intro t
    exact congrFun (Cotensor.mapF_comp _ _ _ α β X.toPsh) t

@[simp] theorem cotensorLiftFunctor_obj (F : Box ⥤ Type) :
    cotensorLiftFunctor.obj F = cotensorLift F := rfl

/-! ### Co-Yoneda: the coend at a cube is the bead value -/

/-- **Co-Yoneda.**  `(□m ⊗ F) ≃ F ▫m` — the coend collapses at a representable. -/
def Cotensor.cubeEquiv (F : Box ⥤ Type) (m : ℕ) :
    Cotensor F (yoneda.obj ▫m) ≃ F.obj ▫m where
  toFun := Quot.lift (fun p => (F.map p.2.1) p.2.2) <| by
    rintro _ _ ⟨φ, x, y⟩
    change (F.map ((yoneda.obj ▫m).map φ.op x)) y = (F.map x) ((F.map φ) y)
    have hx : (yoneda.obj ▫m).map φ.op x = φ ≫ x := rfl
    rw [hx, Functor.map_comp_apply]
  invFun z := Cotensor.mk F m (𝟙 ▫m) z
  left_inv := by
    refine Cotensor.ind F (fun n x y => ?_)
    change Cotensor.mk F m (𝟙 ▫m) ((F.map x) y) = Cotensor.mk F n x y
    have key := Cotensor.map_mk F (X := yoneda.obj ▫m) x (𝟙 ▫m) y
    have hx : (yoneda.obj ▫m).map x.op (𝟙 ▫m) = x := by
      change x ≫ 𝟙 ▫m = x
      rw [Category.comp_id]
    rw [hx] at key
    exact key.symm
  right_inv z := by
    change (F.map (𝟙 ▫m)) z = z
    rw [Functor.map_id_apply]

/-- **The lift extends `F`.**  Co-Yoneda is natural in the cube: on cube maps the coend
functoriality *is* `F`, so `Cotensor F ∘ yoneda ≅ F`. -/
theorem Cotensor.cubeEquiv_naturality (F : Box ⥤ Type) {m m' : ℕ} (φ : ▫m ⟶ ▫m')
    (t : Cotensor F (yoneda.obj ▫m)) :
    Cotensor.cubeEquiv F m' (Cotensor.map F (yoneda.map φ) t)
      = (F.map φ) (Cotensor.cubeEquiv F m t) := by
  refine Cotensor.ind F (fun n ρ y => ?_) t
  change (F.map ((yoneda.map φ)⟪n⟫ ρ)) y = (F.map φ) ((F.map ρ) y)
  have hρ : (yoneda.map φ)⟪n⟫ ρ = ρ ≫ φ := rfl
  rw [hρ, Functor.map_comp_apply]

/-! ### The wedge lift -/

/-- **The covariant wedge lift** `(⋁a ⟶ ⋁b) → (F↓⋁a → F↓⋁b)`.  The dual of `Salvetti/Runs`'
`runRestrict`: a wedge map acts on the coend values, functorially and with no side condition. -/
def wedgeCotensorMap (F : Box ⥤ Type) {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) :
    Cotensor F (⋁a).toPsh → Cotensor F (⋁b).toPsh :=
  Cotensor.map F f.hom

@[simp] theorem wedgeCotensorMap_id (F : Box ⥤ Type) (a : List ℕ+) :
    wedgeCotensorMap F (𝟙 (⋁a)) = id := by
  rw [wedgeCotensorMap, id_hom, Cotensor.map_id]

theorem wedgeCotensorMap_comp (F : Box ⥤ Type) {a b c : List ℕ+} (f : ⋁a ⟶ ⋁b) (g : ⋁b ⟶ ⋁c) :
    wedgeCotensorMap F (f ≫ g) = wedgeCotensorMap F g ∘ wedgeCotensorMap F f := by
  rw [wedgeCotensorMap, wedgeCotensorMap, wedgeCotensorMap, comp_hom, Cotensor.map_comp]

/-! ### The covariant "monoidal" decomposition (dual to `pshExtWedge2`)

`F↓` sends the wedge pushout to a pushout of coends over `F↓ □0 = F ▫0`.  When `F ▫0` is *empty*
— the dual of the contravariant single-vertex condition — the shared-vertex gluing becomes
impossible, so a coend class of `X ∨ Y` lives on exactly one side and the pushout is a plain
coproduct.  Compare `pshExtWedge2`, where `F ▫0` a *point* makes the same pushout a product. -/

section Wedge2
variable {F : Box ⥤ Type}

/-- Split a coend class of `X ∨ Y` onto its bead.  `descCell` cases the wedge cell; the glue
condition is vacuous because a shared vertex would decorate the empty `F ▫0`. -/
def Cotensor.wedge2Fwd (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) :
    Cotensor F (X ∨ Y).toPsh → Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh :=
  Quot.lift
    (fun p => Glue.descCell (f := X.finalVertex) (g := Y.initVertex) (op ▫p.1)
      (fun x => Sum.inl (Cotensor.mk F p.1 x p.2.2))
      (fun z => Sum.inr (Cotensor.mk F p.1 z p.2.2))
      (fun s => (hF.false ((F.map s) p.2.2)).elim) p.2.1) <| by
    rintro _ _ ⟨φ, c, y⟩
    rcases CubeChain.wedge2_cell_cases X Y _ c with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · dsimp only
      have hnat : (X ∨ Y).toPsh.map φ.op ((Glue.inl X.finalVertex Y.initVertex)⟪_⟫ x)
          = (Glue.inl X.finalVertex Y.initVertex)⟪_⟫ (X.toPsh.map φ.op x) :=
        (NatTrans.naturality_apply (Glue.inl X.finalVertex Y.initVertex) φ.op x).symm
      rw [hnat, Glue.descCell_inl, Glue.descCell_inl]
      exact congrArg Sum.inl (Cotensor.map_mk F φ x y)
    · dsimp only
      have hnat : (X ∨ Y).toPsh.map φ.op ((Glue.inr X.finalVertex Y.initVertex)⟪_⟫ z)
          = (Glue.inr X.finalVertex Y.initVertex)⟪_⟫ (Y.toPsh.map φ.op z) :=
        (NatTrans.naturality_apply (Glue.inr X.finalVertex Y.initVertex) φ.op z).symm
      rw [hnat, Glue.descCell_inr, Glue.descCell_inr]
      exact congrArg Sum.inr (Cotensor.map_mk F φ z y)

/-- Assemble bead classes into a coend class of `X ∨ Y` — the two wedge inclusions. -/
def Cotensor.wedge2Bwd (X Y : BPSet) :
    Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh → Cotensor F (X ∨ Y).toPsh :=
  Sum.elim (Cotensor.map F (Glue.inl X.finalVertex Y.initVertex))
    (Cotensor.map F (Glue.inr X.finalVertex Y.initVertex))

@[simp] theorem Cotensor.wedge2Fwd_inl (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) (n : ℕ)
    (x : X.cells n) (y : F.obj ▫n) :
    Cotensor.wedge2Fwd hF X Y
        (Cotensor.mk F n ((Glue.inl X.finalVertex Y.initVertex)⟪n⟫ x) y)
      = Sum.inl (Cotensor.mk F n x y) :=
  Glue.descCell_inl (f := X.finalVertex) (g := Y.initVertex) (op ▫n)
    (h := fun x => Sum.inl (Cotensor.mk F n x y))
    (k := fun z => Sum.inr (Cotensor.mk F n z y))
    (w := fun s => (hF.false ((F.map s) y)).elim) x

@[simp] theorem Cotensor.wedge2Fwd_inr (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) (n : ℕ)
    (z : Y.cells n) (y : F.obj ▫n) :
    Cotensor.wedge2Fwd hF X Y
        (Cotensor.mk F n ((Glue.inr X.finalVertex Y.initVertex)⟪n⟫ z) y)
      = Sum.inr (Cotensor.mk F n z y) :=
  Glue.descCell_inr (f := X.finalVertex) (g := Y.initVertex) (op ▫n)
    (h := fun x => Sum.inl (Cotensor.mk F n x y))
    (k := fun z => Sum.inr (Cotensor.mk F n z y))
    (w := fun s => (hF.false ((F.map s) y)).elim) z

/-- **`F↓` sends the wedge to a coproduct.**  The dual of `pshExtWedge2`. -/
def Cotensor.wedge2Equiv (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) :
    Cotensor F (X ∨ Y).toPsh ≃ Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh where
  toFun := Cotensor.wedge2Fwd hF X Y
  invFun := Cotensor.wedge2Bwd X Y
  left_inv := by
    refine Cotensor.ind F (fun n c y => ?_)
    rcases CubeChain.wedge2_cell_cases X Y n c with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · rw [Cotensor.wedge2Fwd_inl]
      exact Cotensor.map_apply F (Glue.inl X.finalVertex Y.initVertex) n x y
    · rw [Cotensor.wedge2Fwd_inr]
      exact Cotensor.map_apply F (Glue.inr X.finalVertex Y.initVertex) n z y
  right_inv := by
    rintro (u | u)
    · exact Cotensor.ind F (fun n x y => Cotensor.wedge2Fwd_inl hF X Y n x y) u
    · exact Cotensor.ind F (fun n z y => Cotensor.wedge2Fwd_inr hF X Y n z y) u

/-- **Monoidality, binary.**  The wedge inclusion `wedgeInl` is the coproduct injection `Sum.inl`
under the decomposition: `F↓` is monoidal `(∨) → (⊕)`, whence the sub-sum is monotone. -/
@[simp] theorem Cotensor.wedge2Equiv_map_inl (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet)
    (u : Cotensor F X.toPsh) :
    Cotensor.wedge2Equiv hF X Y (Cotensor.map F (wedgeInl X Y) u) = Sum.inl u :=
  (Cotensor.wedge2Equiv hF X Y).apply_symm_apply (Sum.inl u)

@[simp] theorem Cotensor.wedge2Equiv_map_inr (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet)
    (u : Cotensor F Y.toPsh) :
    Cotensor.wedge2Equiv hF X Y (Cotensor.map F (wedgeInr X Y) u) = Sum.inr u :=
  (Cotensor.wedge2Equiv hF X Y).apply_symm_apply (Sum.inr u)

/-- The iterated coproduct a wedge decomposes to: one bead value `F ▫aᵢ` per bead, with an `Empty`
tail (the "nil" of the fold). -/
def wedgeCoprodType (F : Box ⥤ Type) : List ℕ+ → Type
  | [] => Empty
  | c :: rest => F.obj ▫(c : ℕ) ⊕ wedgeCoprodType F rest

/-- **`F↓` sends a serial wedge to the iterated coproduct of bead values** — the concrete,
quotient-free presentation of the covariant lift when `F ▫0` is empty.  The dual of `pshExtProd`;
this is "the condition analogous to a unique `0`-cell" made to pay off. -/
def wedgeCoprodEquiv (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) :
    (a : List ℕ+) → Cotensor F (⋁a).toPsh ≃ wedgeCoprodType F a
  | [] => (Cotensor.cubeEquiv F 0).trans (@Equiv.equivEmpty _ hF)
  | c :: rest =>
    (Cotensor.wedge2Equiv hF (□(c : ℕ)) (⋁rest)).trans
      ((Cotensor.cubeEquiv F (c : ℕ)).sumCongr (wedgeCoprodEquiv F hF rest))

/-- Fin-surgery moving the head bead to index `0`: `F ▫c ⊕ (⊕ over rest) ≃ ⊕ over (c :: rest)` in
`Sigma` form.  The `get`-index rewrites are all definitional (`(c::rest).get 0 = c`,
`(c::rest).get j.succ = rest.get j`), so no transport is spelled. -/
def cotensorSigmaSurgery (F : Box ⥤ Type) (c : ℕ+) (rest : List ℕ+) :
    F.obj ▫(c : ℕ) ⊕ (Σ i : Fin rest.length, F.obj ▫((rest.get i : ℕ)))
      ≃ Σ i : Fin (c :: rest).length, F.obj ▫(((c :: rest).get i : ℕ)) where
  toFun := Sum.elim (fun x => ⟨0, x⟩) (fun p => ⟨p.1.succ, p.2⟩)
  invFun p :=
    Fin.cases (motive := fun i => F.obj ▫(((c :: rest).get i : ℕ)) →
        F.obj ▫(c : ℕ) ⊕ (Σ i : Fin rest.length, F.obj ▫((rest.get i : ℕ))))
      (fun x => Sum.inl x) (fun j x => Sum.inr ⟨j, x⟩) p.1 p.2
  left_inv := by rintro (x | ⟨j, x⟩) <;> simp [Fin.cases_succ]
  right_inv := by rintro ⟨i, x⟩; induction i using Fin.cases <;> simp

/-- **The flat `Sigma` presentation of the covariant lift** — one bead value `F ▫aᵢ` per bead,
indexed by `Fin a.length`.  The `Sigma`-flattened `wedgeCoprodEquiv`. -/
def cotensorSigmaEquiv (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) :
    (a : List ℕ+) → Cotensor F (⋁a).toPsh ≃ Σ i : Fin a.length, F.obj ▫((a.get i : ℕ))
  | [] =>
    haveI : IsEmpty (F.obj ▫0) := hF
    haveI : IsEmpty (Cotensor F (⋁([] : List ℕ+)).toPsh) := (Cotensor.cubeEquiv F 0).isEmpty
    haveI : IsEmpty (Σ i : Fin ([] : List ℕ+).length, F.obj ▫(([] : List ℕ+).get i : ℕ)) :=
      ⟨fun x => x.1.elim0⟩
    Equiv.equivOfIsEmpty _ _
  | c :: rest =>
    (Cotensor.wedge2Equiv hF (□(c : ℕ)) (⋁rest)).trans
      (((Cotensor.cubeEquiv F (c : ℕ)).sumCongr (cotensorSigmaEquiv F hF rest)).trans
        (cotensorSigmaSurgery F c rest))

/-- **Computing `cotensorSigmaEquiv.symm`**: `⟨i, x⟩` is bead `i`'s inclusion `ιᵂ a i` decorated by
`x`.  The β-rule for the flattened coproduct equiv — short because the backward maps *are*
`Cotensor.map` of the wedge injections (`wedge2Bwd`), so each cons step is one `map` fusion. -/
theorem cotensorSigmaEquiv_symm_apply (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) :
    ∀ (a : List ℕ+) (i : Fin a.length) (x : F.obj ▫((a.get i : ℕ))),
      (cotensorSigmaEquiv F hF a).symm ⟨i, x⟩
        = Cotensor.map F (ιᵂ a i) ((Cotensor.cubeEquiv F (a.get i : ℕ)).symm x)
  | [], i, _ => i.elim0
  | c :: rest, i, x => by
      induction i using Fin.cases with
      | zero => rfl
      | succ j =>
          change Cotensor.map F (wedgeInr (□(c : ℕ)) (⋁rest))
              ((cotensorSigmaEquiv F hF rest).symm ⟨j, x⟩) = _
          rw [cotensorSigmaEquiv_symm_apply F hF rest j x]
          exact (congrFun (Cotensor.map_comp F (ιᵂ rest j) (wedgeInr (□(c : ℕ)) (⋁rest))) _).symm

/-- Forward form of `cotensorSigmaEquiv_symm_apply`. -/
theorem cotensorSigmaEquiv_apply_map (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0))
    (a : List ℕ+) (i : Fin a.length) (x : F.obj ▫((a.get i : ℕ))) :
    cotensorSigmaEquiv F hF a
        (Cotensor.map F (ιᵂ a i) ((Cotensor.cubeEquiv F (a.get i : ℕ)).symm x)) = ⟨i, x⟩ :=
  (Equiv.eq_symm_apply _).mp (cotensorSigmaEquiv_symm_apply F hF a i x).symm

/-- **The covariant wedge lift, on the direct sum.**  The top-level product: a wedge map acts
directly on `⊕ᵢ F ▫aᵢ`, with the coend only as hidden plumbing (`wedgeCotensorMap` conjugated by
`wedgeCoprodEquiv`).  The covariant dual of `pshExtRestrict`. -/
def wedgeCoprodMap (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) :
    wedgeCoprodType F a → wedgeCoprodType F b :=
  fun t => wedgeCoprodEquiv F hF b (wedgeCotensorMap F f ((wedgeCoprodEquiv F hF a).symm t))

@[simp] theorem wedgeCoprodMap_id (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) (a : List ℕ+) :
    wedgeCoprodMap F hF (𝟙 (⋁a)) = id := by
  funext t
  simp only [wedgeCoprodMap, wedgeCotensorMap_id, id_eq, Equiv.apply_symm_apply]

theorem wedgeCoprodMap_comp (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) {a b c : List ℕ+}
    (f : ⋁a ⟶ ⋁b) (g : ⋁b ⟶ ⋁c) :
    wedgeCoprodMap F hF (f ≫ g) = wedgeCoprodMap F hF g ∘ wedgeCoprodMap F hF f := by
  funext t
  simp only [wedgeCoprodMap, Function.comp_apply, wedgeCotensorMap_comp, Equiv.symm_apply_apply]

/-! ### Monoidality: appending words splits the sum

Dual to `wedgeHomProdAppend`.  The sum over `a₁ ++ a₂` splits as the sum over `a₁` plus the sum
over `a₂`; the two `symm`-injections realise each half as a sub-sum — the monotonicity. -/

/-- **The append iso.**  `⊕_{a₁ ++ a₂} ≃ ⊕_{a₁} ⊕ ⊕_{a₂}` — the covariant dual of
`wedgeHomProdAppend`. -/
def wedgeCoprodAppend (F : Box ⥤ Type) :
    (a₁ a₂ : List ℕ+) → wedgeCoprodType F (a₁ ++ a₂) ≃ wedgeCoprodType F a₁ ⊕ wedgeCoprodType F a₂
  | [], a₂ => (Equiv.emptySum Empty (wedgeCoprodType F a₂)).symm
  | c :: rest, a₂ =>
    ((Equiv.refl (F.obj ▫(c : ℕ))).sumCongr (wedgeCoprodAppend F rest a₂)).trans
      (Equiv.sumAssoc _ _ _).symm

/-- Left sub-sum inclusion `⊕_{a₁} ↪ ⊕_{a₁ ++ a₂}` — the monotone map. -/
def wedgeCoprodInclL (F : Box ⥤ Type) (a₁ a₂ : List ℕ+) :
    wedgeCoprodType F a₁ → wedgeCoprodType F (a₁ ++ a₂) :=
  fun t => (wedgeCoprodAppend F a₁ a₂).symm (Sum.inl t)

/-- Right sub-sum inclusion `⊕_{a₂} ↪ ⊕_{a₁ ++ a₂}`. -/
def wedgeCoprodInclR (F : Box ⥤ Type) (a₁ a₂ : List ℕ+) :
    wedgeCoprodType F a₂ → wedgeCoprodType F (a₁ ++ a₂) :=
  fun t => (wedgeCoprodAppend F a₁ a₂).symm (Sum.inr t)

end Wedge2

/-! ## The contravariant lift `F↑ X = (X.toPsh ⟶ F)`

The `Salvetti/Runs` machinery, abstracted off `runPresheaf`.  The classifying object is `F↑ (⋁a)`
itself — no descent to a product of bead-values is forced; that descent is the *monoidal* content
(`pshExtWedge2`), the general form of "`Run` is monoidal". -/

/-- `F↑ X` — a presheaf `F` read at a bi-pointed set `X`, i.e. the maps `X.toPsh ⟶ F`.  On a serial
wedge, `F = runPresheaf` recovers `Run (⋁a)` (`Salvetti/Runs.runPshEquiv`). -/
def pshExt (F : PrecubicalSet) (X : BPSet) : Type := X.toPsh ⟶ F

/-- **The contravariant wedge lift** — precomposition.  Generalizes `runRestrict`. -/
def pshExtRestrict (F : PrecubicalSet) {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) :
    pshExt F (⋁b) → pshExt F (⋁a) := fun φ => f.hom ≫ φ

@[simp] theorem pshExtRestrict_id (F : PrecubicalSet) {a : List ℕ+} (φ : pshExt F (⋁a)) :
    pshExtRestrict F (𝟙 (⋁a)) φ = φ := by
  rw [pshExtRestrict, id_hom, Category.id_comp]

theorem pshExtRestrict_comp (F : PrecubicalSet) {a b c : List ℕ+} (f : ⋁a ⟶ ⋁b) (g : ⋁b ⟶ ⋁c)
    (φ : pshExt F (⋁c)) :
    pshExtRestrict F (f ≫ g) φ = pshExtRestrict F f (pshExtRestrict F g φ) := by
  rw [pshExtRestrict, pshExtRestrict, pshExtRestrict, comp_hom, Category.assoc]

/-- **The bead value.**  Yoneda: `F↑ (□n) ≃ F ▫n`.  Dual to `Cotensor.cubeEquiv`. -/
def pshExtCubeEquiv (F : PrecubicalSet) (n : ℕ) : pshExt F (□n) ≃ F.obj (op ▫n) :=
  yonedaEquiv (X := ▫n) (F := F)

/-- **`F↑` sends the wedge to the product** — the general "`Run` is monoidal", i.e. the abstract
`runSplitEquiv`.  Single-vertexness makes the gluing condition vacuous, so the pushout defining
`X ∨ Y` maps to an honest product. -/
def pshExtWedge2 (F : PrecubicalSet) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) (X Y : BPSet) :
    pshExt F (X ∨ Y) ≃ pshExt F X × pshExt F Y where
  toFun φ := (Glue.inl X.finalVertex Y.initVertex ≫ φ, Glue.inr X.finalVertex Y.initVertex ≫ φ)
  invFun p := Glue.desc (f := X.finalVertex) (g := Y.initVertex) p.1 p.2 (hF _ _)
  left_inv φ := Glue.hom_ext (by rw [Glue.inl_desc]) (by rw [Glue.inr_desc])
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact Glue.inl_desc _ _ _
    · exact Glue.inr_desc _ _ _

/-- The iterated product a wedge decomposes to: one bead value per bead. -/
def pshExtProdType (F : PrecubicalSet) : List ℕ+ → Type
  | [] => PUnit
  | c :: rest => pshExt F (□(c : ℕ)) × pshExtProdType F rest

/-- **`F↑` sends a serial wedge to the iterated product of bead values** — the general
`runSegalProd`.  `pt` inhabits the empty-wedge value, `hF` collapses it. -/
def pshExtProd (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) :
    (a : List ℕ+) → pshExt F (⋁a) ≃ pshExtProdType F a
  | [] =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => pt
      left_inv := fun φ => hF pt φ
      right_inv := fun _ => rfl }
  | c :: rest =>
    (pshExtWedge2 F hF (□(c : ℕ)) (⋁rest)).trans
      ((Equiv.refl (pshExt F (□(c : ℕ)))).prodCongr (pshExtProd F pt hF rest))

/-! ## A computable cocartesian monoidal structure on `Type`

`⊗ = ⊕`, unit `PEmpty`, associator/unitors the `Sum` equivalences.  Mathlib's
`monoidalOfHasFiniteCoproducts` is built on `Limits.coprod` (a `Classical.choice`-opaque colimit);
this one computes, so — like `wedge2` on `Glue` — the lift below stays executable. -/

section TypeSum
open MonoidalCategory

/-- `Sum` as a `MonoidalCategoryStruct` on `Type`. -/
@[reducible] def typeSumMonoidalStruct : MonoidalCategoryStruct (Type u) where
  tensorObj X Y := X ⊕ Y
  tensorHom f g := TypeCat.ofHom (Sum.map f g)
  whiskerLeft _ _ _ g := TypeCat.ofHom (Sum.map id g)
  whiskerRight f _ := TypeCat.ofHom (Sum.map f id)
  tensorUnit := PEmpty
  associator X Y Z := (Equiv.sumAssoc X Y Z).toIso
  leftUnitor X := (Equiv.emptySum PEmpty X).toIso
  rightUnitor X := (Equiv.sumEmpty X PEmpty).toIso

/-- The cocartesian (`Sum`) monoidal structure on `Type` — computable.  Kept a `def`, brought in
by `local instance` only where needed (`Type` carries no canonical monoidal product). -/
@[reducible] def typeSumMonoidal : MonoidalCategory (Type u) :=
  letI := typeSumMonoidalStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by intro X Y; ext x; cases x <;> rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂; ext x; cases x <;> rfl)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃; ext x; rcases x with (x | x) | x <;> rfl)
    (leftUnitor_naturality := by
      intro X Y f; ext x; rcases x with x | x
      · exact x.elim
      · rfl)
    (rightUnitor_naturality := by
      intro X Y f; ext x; rcases x with x | x
      · rfl
      · exact x.elim)
    (pentagon := by intro W X Y Z; ext x; rcases x with ((x | x) | x) | x <;> rfl)
    (triangle := by
      intro X Y; ext x; rcases x with (x | x) | x
      · rfl
      · exact x.elim
      · rfl)

attribute [local instance] typeSumMonoidal

/-- `⊗ = ⊕` — **not** `@[simp]`: like the structural `rfl` lemmas below, letting `simp` normalize
`⊗ → ⊕` in object positions un-spells the `⊗`-keyed injection-β rules and re-exposes the coercion
wall.  Callers who genuinely want the `Sum` spelling opt in explicitly. -/
theorem typeSum_tensorObj (X Y : Type u) : X ⊗ Y = (X ⊕ Y) := rfl

/-- The `= TypeCat.ofHom (Sum.map …)` forms are kept as plain (non-`simp`) `rfl` lemmas: they would
otherwise fire *before* the injection-β rules below and re-expose the coercion wall. -/
theorem typeSum_tensorHom {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) :
    f ⊗ₘ g = TypeCat.ofHom (Sum.map f g) := rfl

theorem typeSum_whiskerLeft (X : Type u) {Y Z : Type u} (g : Y ⟶ Z) :
    X ◁ g = TypeCat.ofHom (Sum.map id g) := rfl

theorem typeSum_whiskerRight {X Y : Type u} (f : X ⟶ Y) (Z : Type u) :
    f ▷ Z = TypeCat.ofHom (Sum.map f id) := rfl

theorem typeSum_associator_hom (X Y Z : Type u) :
    (α_ X Y Z).hom = TypeCat.ofHom (fun x => Equiv.sumAssoc X Y Z x) := rfl

theorem typeSum_leftUnitor_hom (X : Type u) :
    (λ_ X).hom = TypeCat.ofHom (fun x => Equiv.emptySum PEmpty X x) := rfl

theorem typeSum_rightUnitor_hom (X : Type u) :
    (ρ_ X).hom = TypeCat.ofHom (fun x => Equiv.sumEmpty X PEmpty x) := rfl

/-! ### The coproduct universal property — a morphism-level API

`Sum` is the coproduct, so a map out of `X ⊕ Y` is pinned by its two injections
(`typeSum_hom_ext`), and every structure map has a clean injection-β rule.  These let the coherence
proofs run as morphism equations (`typeSum_hom_ext <;> simp`), never touching the `Type` coercion —
exactly as for mathlib's `monoidalOfHasFiniteCoproducts`. -/

/-- The coproduct injections, **typed by the tensor** `⊗` (not the raw `Sum`): this keeps the
`≫` object arguments `⊗`-spelled, so the injection-β rules below match the coherence goals — the
`coprod.inl` of `monoidalOfHasFiniteCoproducts`, transposed to `Sum`. -/
def typeSumInl (X Y : Type u) : X ⟶ X ⊗ Y := TypeCat.ofHom Sum.inl

def typeSumInr (X Y : Type u) : Y ⟶ X ⊗ Y := TypeCat.ofHom Sum.inr

@[simp] theorem typeSumInl_apply (X Y : Type u) (x : X) : typeSumInl X Y x = Sum.inl x := rfl
@[simp] theorem typeSumInr_apply (X Y : Type u) (y : Y) : typeSumInr X Y y = Sum.inr y := rfl

/-- **Coproduct extensionality**: a map out of `X ⊗ Y` is determined by its two injections. -/
theorem typeSum_hom_ext {X Y Z : Type u} {f g : (X ⊗ Y) ⟶ Z}
    (hl : typeSumInl X Y ≫ f = typeSumInl X Y ≫ g)
    (hr : typeSumInr X Y ≫ f = typeSumInr X Y ≫ g) : f = g := by
  apply ConcreteCategory.hom_ext
  rintro (x | x)
  · simpa using ConcreteCategory.congr_hom hl x
  · simpa using ConcreteCategory.congr_hom hr x

@[reassoc (attr := simp)] theorem typeSumInl_whiskerRight {X Y : Type u} (f : X ⟶ Y) (Z : Type u) :
    typeSumInl X Z ≫ (f ▷ Z) = f ≫ typeSumInl Y Z := rfl

@[reassoc (attr := simp)] theorem typeSumInr_whiskerRight {X Y : Type u} (f : X ⟶ Y) (Z : Type u) :
    typeSumInr X Z ≫ (f ▷ Z) = typeSumInr Y Z := rfl

@[reassoc (attr := simp)] theorem typeSumInl_whiskerLeft (X : Type u) {Y Z : Type u} (g : Y ⟶ Z) :
    typeSumInl X Y ≫ (X ◁ g) = typeSumInl X Z := rfl

@[reassoc (attr := simp)] theorem typeSumInr_whiskerLeft (X : Type u) {Y Z : Type u} (g : Y ⟶ Z) :
    typeSumInr X Y ≫ (X ◁ g) = g ≫ typeSumInr X Z := rfl

@[reassoc (attr := simp)] theorem typeSumInl_inl_associator (X Y Z : Type u) :
    (typeSumInl X Y ≫ typeSumInl (X ⊗ Y) Z) ≫ (α_ X Y Z).hom = typeSumInl X (Y ⊗ Z) := rfl

@[reassoc (attr := simp)] theorem typeSumInr_inl_associator (X Y Z : Type u) :
    (typeSumInr X Y ≫ typeSumInl (X ⊗ Y) Z) ≫ (α_ X Y Z).hom
      = typeSumInl Y Z ≫ typeSumInr X (Y ⊗ Z) := rfl

@[reassoc (attr := simp)] theorem typeSumInr_associator (X Y Z : Type u) :
    typeSumInr (X ⊗ Y) Z ≫ (α_ X Y Z).hom = typeSumInr Y Z ≫ typeSumInr X (Y ⊗ Z) := rfl

@[reassoc (attr := simp)] theorem typeSumInr_leftUnitor (X : Type u) :
    typeSumInr (𝟙_ (Type u)) X ≫ (λ_ X).hom = 𝟙 X := rfl

@[reassoc (attr := simp)] theorem typeSumInl_rightUnitor (X : Type u) :
    typeSumInl X (𝟙_ (Type u)) ≫ (ρ_ X).hom = 𝟙 X := rfl

end TypeSum

/-! ## `cotensorLift F` is lax monoidal `(BPSet, ∨) ⥤ (Type, ⊕)`

The tensorator is the two wedge inclusions assembled by `wedge2Bwd` (a `Sum.elim`, computable); the
unit `ε` is the empty map out of `PEmpty`.  Each coherence square is `ext` down to the `Sum`
summands, `Cotensor.map` functoriality to fuse (`Cotensor.map_map`), then the matching
`WedgeMonoidal` restriction lemma. -/

section LaxMonoidal
open MonoidalCategory

attribute [local instance] typeSumMonoidal

variable (F : Box ⥤ Type)

/-- `.hom` of the wedge tensor on morphisms. -/
@[simp] theorem tensorHom_bpset_hom {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g).hom = wedge2MapPsh f g := rfl

@[simp] theorem whiskerRight_bpset_hom {X Y : BPSet} (f : X ⟶ Y) (Z : BPSet) :
    (f ▷ Z).hom = wedge2MapPsh f (𝟙 Z) := rfl

@[simp] theorem whiskerLeft_bpset_hom (X : BPSet) {Y Z : BPSet} (f : Y ⟶ Z) :
    (X ◁ f).hom = wedge2MapPsh (𝟙 X) f := rfl

@[simp] theorem associator_bpset_hom_hom (X Y Z : BPSet) :
    (α_ X Y Z).hom.hom = wedge2AssocFwd X Y Z := rfl

@[simp] theorem leftUnitor_bpset_hom_hom (X : BPSet) :
    (λ_ X).hom.hom = wedge2LeftUnitPsh X := rfl

@[simp] theorem rightUnitor_bpset_hom_hom (X : BPSet) :
    (ρ_ X).hom.hom = wedge2RightUnitPsh X := rfl

/-- The wedge tensor spelled as `wedge2` (matches the `WedgeMonoidal` restriction lemmas, which
`⊗` will not syntactically unify with).  Fed to `simp` in the coherence proofs, not global. -/
theorem bpTensorObj_eq (X Y : BPSet) : (X ⊗ Y) = wedge2 X Y := rfl

/-- The wedge unit spelled as `□0` — the companion of `bpTensorObj_eq` for the unitor lemmas. -/
theorem bpUnit_eq : (𝟙_ BPSet) = □0 := rfl

/-- Fuse two coend functorialities: post-composing the underlying maps. -/
theorem Cotensor.map_map {X Y Z : PrecubicalSet} (g : X ⟶ Y) (h : Y ⟶ Z) (t : Cotensor F X) :
    Cotensor.map F h (Cotensor.map F g t) = Cotensor.map F (g ≫ h) t :=
  (congrFun (Cotensor.map_comp F g h) t).symm

/-- `F↓`'s value on objects, unfolded.  `@[simp]` so `simp` normalizes every coend object to the
single spelling `Cotensor F X.toPsh` — the one shared by the injection-β rules
(`typeSumInl_cotensorμ`) and the fusion lemma (`cotensorMap_ofHom_comp`).  With one spelling those
compose in a single pass, so a caller who whiskers `μ` just runs `simp`. -/
@[simp] theorem cotensorLift_obj (X : BPSet) : (cotensorLift F).obj X = Cotensor F X.toPsh := rfl

/-- `(cotensorLift F).map` acts on a coend value by the underlying map's coend functoriality. -/
@[simp] theorem cotensorLift_map_apply {X Y : BPSet} (f : X ⟶ Y) (t : (cotensorLift F).obj X) :
    (cotensorLift F).map f t = Cotensor.map F f.hom t := rfl

/-- `(cotensorLift F).map`, as a `Type` morphism — the coend functoriality of the underlying map. -/
@[simp] theorem cotensorLift_map {X Y : BPSet} (f : X ⟶ Y) :
    (cotensorLift F).map f = TypeCat.ofHom (Cotensor.map F f.hom) := rfl

/-- Coend functoriality fuses as a morphism composite. -/
@[reassoc (attr := simp)] theorem cotensorMap_ofHom_comp {X Y Z : PrecubicalSet}
    (g : X ⟶ Y) (h : Y ⟶ Z) :
    TypeCat.ofHom (Cotensor.map F g) ≫ TypeCat.ofHom (Cotensor.map F h)
      = TypeCat.ofHom (Cotensor.map F (g ≫ h)) := by
  apply ConcreteCategory.hom_ext; intro t; exact Cotensor.map_map F g h t

/-- Coend functoriality of an identity is the identity morphism. -/
@[simp] theorem cotensorMap_id_ofHom (X : PrecubicalSet) :
    TypeCat.ofHom (Cotensor.map F (𝟙 X)) = 𝟙 (Cotensor F X) := by
  apply ConcreteCategory.hom_ext; intro t; exact congrFun (Cotensor.map_id F X) t

/-- The tensorator `F↓X ⊕ F↓Y ⟶ F↓(X ∨ Y)`: the two wedge inclusions (`wedge2Bwd`).  Typed in the
unfolded `Cotensor F _.toPsh` spelling (defeq to `(cotensorLift F).obj _`, so it still serves as the
`LaxMonoidal.μ` field) — this keeps the `≫`-middle object unfolded, so `typeSumInl_cotensorμ` fires
against a whiskered `μ` without an unfolding barrier. -/
def cotensorμ (X Y : BPSet) :
    Cotensor F X.toPsh ⊗ Cotensor F Y.toPsh ⟶ Cotensor F (X ⊗ Y).toPsh :=
  TypeCat.ofHom (Cotensor.wedge2Bwd X Y)

/-- The unit: the empty map out of the monoidal unit `PEmpty`. -/
def cotensorε : 𝟙_ (Type) ⟶ Cotensor F (𝟙_ BPSet).toPsh :=
  TypeCat.ofHom (fun x => x.elim)

@[simp] theorem cotensorμ_inl (X Y : BPSet) (u : Cotensor F X.toPsh) :
    cotensorμ F X Y (Sum.inl u) = Cotensor.map F (wedgeInl X Y) u := rfl

@[simp] theorem cotensorμ_inr (X Y : BPSet) (u : Cotensor F Y.toPsh) :
    cotensorμ F X Y (Sum.inr u) = Cotensor.map F (wedgeInr X Y) u := rfl

/-- The tensorator on the left injection is the left wedge inclusion (morphism form).  Stated in the
unfolded `Cotensor F X.toPsh` object spelling (`cotensorLift_obj` normalizes goals to it), so it
composes with `cotensorMap_ofHom_comp` — same objects, one `simp` pass. -/
@[reassoc (attr := simp)] theorem typeSumInl_cotensorμ (X Y : BPSet) :
    typeSumInl (Cotensor F X.toPsh) (Cotensor F Y.toPsh) ≫ cotensorμ F X Y
      = TypeCat.ofHom (Cotensor.map F (wedgeInl X Y)) := rfl

@[reassoc (attr := simp)] theorem typeSumInr_cotensorμ (X Y : BPSet) :
    typeSumInr (Cotensor F X.toPsh) (Cotensor F Y.toPsh) ≫ cotensorμ F X Y
      = TypeCat.ofHom (Cotensor.map F (wedgeInr X Y)) := rfl


/-! With every coend object normalized to `Cotensor F _.toPsh` (`cotensorLift_obj`), each coherence
square is: split by the injections (`typeSum_hom_ext`), let the injection-β rules slide past the
whiskering / (co)tensorator / (co)unitor, fuse the two coend functorialities
(`cotensorMap_ofHom_comp`), and finish with the matching `WedgeMonoidal` restriction lemma — all one
`simp`.  Callers who whisker `μ` get the same one-pass reduction. -/

private theorem cotensorμ_natural_left {X Y : BPSet} (f : X ⟶ Y) (X' : BPSet) :
    (cotensorLift F).map f ▷ (cotensorLift F).obj X' ≫ cotensorμ F Y X'
      = cotensorμ F X X' ≫ (cotensorLift F).map (f ▷ X') := by
  apply typeSum_hom_ext
  · simp [wedge2MapPsh_inl]
  · simp [wedge2MapPsh_inr]

private theorem cotensorμ_natural_right {X Y : BPSet} (X' : BPSet) (f : X ⟶ Y) :
    (cotensorLift F).obj X' ◁ (cotensorLift F).map f ≫ cotensorμ F X' Y
      = cotensorμ F X' X ≫ (cotensorLift F).map (X' ◁ f) := by
  apply typeSum_hom_ext
  · simp [wedge2MapPsh_inl]
  · simp [wedge2MapPsh_inr]

private theorem cotensorμ_associativity (X Y Z : BPSet) :
    cotensorμ F X Y ▷ (cotensorLift F).obj Z ≫ cotensorμ F (X ⊗ Y) Z
        ≫ (cotensorLift F).map (α_ X Y Z).hom
      = (α_ ((cotensorLift F).obj X) ((cotensorLift F).obj Y) ((cotensorLift F).obj Z)).hom
        ≫ (cotensorLift F).obj X ◁ cotensorμ F Y Z ≫ cotensorμ F X (Y ⊗ Z) := by
  refine typeSum_hom_ext (typeSum_hom_ext ?_ ?_) ?_ <;>
    simp only [typeSumInl_inl_associator_assoc, typeSumInr_inl_associator_assoc,
      typeSumInr_associator_assoc, typeSumInl_whiskerRight_assoc, typeSumInr_whiskerRight_assoc,
      typeSumInl_whiskerLeft_assoc, typeSumInr_whiskerLeft_assoc, typeSumInl_cotensorμ,
      typeSumInr_cotensorμ, typeSumInl_cotensorμ_assoc, typeSumInr_cotensorμ_assoc, cotensorLift_map,
      cotensorLift_obj, associator_bpset_hom_hom, cotensorMap_ofHom_comp]
  · exact congrArg (fun m => TypeCat.ofHom (Cotensor.map F m)) (wedge2AssocFwd_inl_inl X Y Z)
  · exact congrArg (fun m => TypeCat.ofHom (Cotensor.map F m)) (wedge2AssocFwd_inr_inl X Y Z)
  · exact congrArg (fun m => TypeCat.ofHom (Cotensor.map F m)) (wedge2AssocFwd_inr X Y Z)

private theorem cotensorμ_left_unitality (X : BPSet) :
    (λ_ ((cotensorLift F).obj X)).hom
      = cotensorε F ▷ (cotensorLift F).obj X ≫ cotensorμ F (𝟙_ BPSet) X
        ≫ (cotensorLift F).map (λ_ X).hom := by
  refine typeSum_hom_ext ?_ ?_
  · apply ConcreteCategory.hom_ext; rintro ⟨⟩
  · simp [bpUnit_eq, wedge2LeftUnitPsh_inr]

private theorem cotensorμ_right_unitality (X : BPSet) :
    (ρ_ ((cotensorLift F).obj X)).hom
      = (cotensorLift F).obj X ◁ cotensorε F ≫ cotensorμ F X (𝟙_ BPSet)
        ≫ (cotensorLift F).map (ρ_ X).hom := by
  refine typeSum_hom_ext ?_ ?_
  · simp [bpUnit_eq, wedge2RightUnitPsh_inl]
  · apply ConcreteCategory.hom_ext; rintro ⟨⟩

/-- **`F↓ = cotensorLift F` is lax monoidal** `(BPSet, ∨) → (Type, ⊕)`.  Computable: the tensorator
is `wedge2Bwd` (a `Sum.elim`), the target monoidal is the `Sum`-based `typeSumMonoidal`. -/
instance : (cotensorLift F).LaxMonoidal where
  ε := cotensorε F
  μ := cotensorμ F
  μ_natural_left := cotensorμ_natural_left F
  μ_natural_right := cotensorμ_natural_right F
  associativity := cotensorμ_associativity F
  left_unitality := cotensorμ_left_unitality F
  right_unitality := cotensorμ_right_unitality F

/-- Caller ergonomics: the associativity square is the abstract `LaxMonoidal` coherence — one term,
no `wedgeInl`/`wedge2AssocFwd` and no `⊗`-vs-`∨` unfolding (those live only in the instance proof). -/
example (X Y Z : BPSet) :
    Functor.LaxMonoidal.μ (cotensorLift F) X Y ▷ (cotensorLift F).obj Z
        ≫ Functor.LaxMonoidal.μ (cotensorLift F) (X ⊗ Y) Z
        ≫ (cotensorLift F).map (α_ X Y Z).hom
      = (α_ _ _ _).hom ≫ (cotensorLift F).obj X ◁ Functor.LaxMonoidal.μ (cotensorLift F) Y Z
        ≫ Functor.LaxMonoidal.μ (cotensorLift F) X (Y ⊗ Z) :=
  Functor.LaxMonoidal.associativity (cotensorLift F) X Y Z

end LaxMonoidal

end ChainCat
