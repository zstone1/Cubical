import CubeChains.Salvetti.ConcGroupoid
import Mathlib.CategoryTheory.Elements

/-!
# Salvetti/Reversal — the concurrency groupoid is time-reversal invariant

Reversing time (`t ↦ 1 - t`) is the involution `Box.rev : Box ⥤ Box` that swaps the two faces in
every direction (`coface ε i ↦ coface (!ε) i`, coordinate index untouched); it acts on `BPSet` by
precomposition + swapping `init`/`final` (`BPSet.reverse`), and `BPSet.reverse` is an equivalence
of `BPSet` with itself as inverse (`revBPEquiv`).

`Ch` is **covariant** under it — `chRevEquiv : Ch K ≌ Ch (K.reverse)`, *not* `(Ch K)ᵒᵖ` — because a
morphism of `Ch K` is a **refinement**: reversal reverses the bead list of a chain but carries
refinements to refinements, in the same direction.  The chamber presheaf follows (a chamber, "which
direction flips first", reverses to the opposite strict total order), giving

    concGrpdReverse : ConcGrpd (K.reverse) ≌ ConcGrpd K.

So `ConcGrpd` sees concurrency and not causality — but the reason is already visible one level
down: the *refinement order itself* is direction-blind.  (What is genuinely directional is the
d-path/execution structure, not `Ch`.)

**Gotchas.**  `(□n).toPsh` and `yoneda.obj ▫n` are defeq but not syntactically equal, and `≫` at
`PrecubicalSet` (a functor category) does not respond to `rw`/`simp` with `Category.assoc`.  Both
break keyed matching, so the composite chases below run in term mode (`congrArg`, `.trans`).
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace StdCube

/-! ## Reversal on cells of the standard cube -/

theorem noneSet_map_not {N : ℕ} (v : Fin N → Option Bool) :
    noneSet (fun j => (v j).map not) = noneSet v := by
  ext j
  simp only [mem_noneSet]
  cases v j <;> simp

/-- Time reversal of a cell of `□ᴺ`: flip every fixed coordinate, keep the free ones. -/
def revCell {N k : ℕ} (c : Cell N k) : Cell N k :=
  ⟨fun j => (c.val j).map not, by rw [noneSet_map_not, c.prop]⟩

@[simp] theorem revCell_val {N k : ℕ} (c : Cell N k) (j : Fin N) :
    (revCell c).val j = (c.val j).map not := rfl

@[simp] theorem revCell_revCell {N k : ℕ} (c : Cell N k) : revCell (revCell c) = c := by
  apply Subtype.ext
  funext j
  cases h : c.val j <;> simp [h]

theorem noneSet_revCell {N k : ℕ} (c : Cell N k) :
    noneSet (revCell c).val = noneSet c.val := noneSet_map_not _

/-- Reversal does not move the free coordinates, so it does not move their enumeration. -/
theorem nones_revCell {N k : ℕ} (c : Cell N k) : nones (revCell c) = nones c := by
  have hmem : ∀ x, nones c x ∈ noneSet (revCell c).val := by
    intro x
    rw [noneSet_revCell]
    exact Finset.orderEmbOfFin_mem _ c.prop x
  exact (Finset.orderEmbOfFin_unique' (revCell c).prop hmem).symm

/-- Reversal swaps the two faces in each direction. -/
theorem revCell_faceCell {N k : ℕ} (ε : Bool) (i : Fin (k + 1)) (c : Cell N (k + 1)) :
    revCell (faceCell ε i c) = faceCell (!ε) i (revCell c) := by
  apply Subtype.ext
  funext j
  change (Function.update c.val (nones c i) (some ε) j).map not
      = Function.update (revCell c).val (nones (revCell c) i) (some !ε) j
  rw [nones_revCell]
  by_cases hj : j = nones c i
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, revCell_val]

@[simp] theorem revCell_topCell (n : ℕ) : revCell (topCell n) = topCell n := by
  apply Subtype.ext; funext _; rfl

@[simp] theorem revCell_constVertex (n : ℕ) (ε : Bool) :
    revCell (constVertex n ε) = constVertex n (!ε) := by
  apply Subtype.ext; funext _; rfl

/-- Time reversal of a precubical map of standard cubes: conjugate by the sign flip.  It is *not*
a map over `𝟭 Box` — it swaps `d⁰` and `d¹`. -/
def revHom {m n : ℕ} (f : stdPre m ⟶ stdPre n) : stdPre m ⟶ stdPre n where
  app _ c := revCell (PrecubicalConstructions.Hom.app f _ (revCell c))
  app_face ε i c := by
    change revCell (PrecubicalConstructions.Hom.app f _ (revCell (faceCell ε i c)))
      = faceCell ε i (revCell (PrecubicalConstructions.Hom.app f _ (revCell c)))
    rw [revCell_faceCell,
      show PrecubicalConstructions.Hom.app f _ (faceCell (!ε) i (revCell c))
          = faceCell (!ε) i (PrecubicalConstructions.Hom.app f _ (revCell c)) from
        f.app_face (!ε) i (revCell c),
      revCell_faceCell, Bool.not_not]

@[simp] theorem revHom_app {m n k : ℕ} (f : stdPre m ⟶ stdPre n) (c : Cell m k) :
    PrecubicalConstructions.Hom.app (revHom f) k c
      = revCell (PrecubicalConstructions.Hom.app f k (revCell c)) := rfl

theorem revHom_revHom {m n : ℕ} (f : stdPre m ⟶ stdPre n) : revHom (revHom f) = f := by
  apply PrecubicalConstructions.hom_ext
  intro k c
  rw [revHom_app, revHom_app, revCell_revCell, revCell_revCell]

end StdCube

open StdCube

/-- **Time reversal** on the box category: the identity on objects, the sign flip on morphisms.
An involution (`Box.rev_rev`), and *not* the identity: `rev (coface ε i) = coface (!ε) i`. -/
def Box.rev : Box ⥤ Box where
  obj b := b
  map f := revHom f
  map_id _ := by
    apply PrecubicalConstructions.hom_ext
    intro k c
    exact revCell_revCell c
  map_comp f g := by
    apply PrecubicalConstructions.hom_ext
    intro k c
    change revCell (PrecubicalConstructions.Hom.app (f ≫ g) k (revCell c))
      = PrecubicalConstructions.Hom.app (revHom g) k
          (PrecubicalConstructions.Hom.app (revHom f) k c)
    rw [revHom_app, revHom_app, revCell_revCell]
    rfl

namespace Box

@[simp] theorem rev_obj (b : Box) : Box.rev.obj b = b := rfl

theorem rev_rev {m n : Box} (f : m ⟶ n) : Box.rev.map (Box.rev.map f) = f :=
  revHom_revHom f

end Box

namespace StdCube

/-- `revCell (topCell m) = topCell m` definitionally, so this is `rfl`. -/
theorem ev_rev {m n : ℕ} (f : ▫m ⟶ ▫n) : ev (Box.rev.map f) = revCell (ev f) := rfl

theorem rev_canonicalMap {N k : ℕ} (c : Cell N k) :
    Box.rev.map (canonicalMap c : ▫k ⟶ ▫N) = canonicalMap (revCell c) := by
  refine (cubeRepr (stdPre N) k).injective ?_
  change ev (Box.rev.map (canonicalMap c)) = ev (canonicalMap (revCell c))
  rw [ev_rev, ev_canonicalMap, ev_canonicalMap]

/-- Reversal swaps the two cofaces in each direction — the defining property. -/
theorem rev_coface (ε : Bool) {n : ℕ} (i : Fin (n + 1)) :
    Box.rev.map (PrecubicalSet.coface ε i) = PrecubicalSet.coface (!ε) i := by
  rw [PrecubicalSet.coface, rev_canonicalMap, revCell_faceCell, revCell_topCell,
    PrecubicalSet.coface]
  rfl

theorem rev_initVertexMap (n : ℕ) :
    Box.rev.map (PrecubicalSet.initVertexMap n) = PrecubicalSet.finalVertexMap n := by
  rw [PrecubicalSet.initVertexMap, rev_canonicalMap, revCell_constVertex,
    PrecubicalSet.finalVertexMap]
  rfl

theorem rev_finalVertexMap (n : ℕ) :
    Box.rev.map (PrecubicalSet.finalVertexMap n) = PrecubicalSet.initVertexMap n := by
  rw [PrecubicalSet.finalVertexMap, rev_canonicalMap, revCell_constVertex,
    PrecubicalSet.initVertexMap]
  rfl

end StdCube

/-- Reversal keeps the free coordinates of a face, hence its order embedding. -/
theorem CubeChain.faceEmb_rev {k m : ℕ} (f : ▫k ⟶ ▫m) :
    CubeChain.faceEmb (Box.rev.map f) = CubeChain.faceEmb f :=
  nones_revCell (ev f)

namespace CubeChains

/-! ## Reversal of precubical sets and of bi-pointed sets -/

/-- Time reversal of a precubical set: precompose with `rev`.  Cells are unchanged; only the
face maps swap (`d⁰ ↔ d¹`). -/
def revPsh : PrecubicalSet ⥤ PrecubicalSet where
  obj X := Box.rev.op ⋙ X
  map α := Functor.whiskerLeft Box.rev.op α
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem revPsh_map_app {X Y : PrecubicalSet} (α : X ⟶ Y) (n : ℕ) :
    (revPsh.map α)⟪n⟫ = α⟪n⟫ := rfl

/-- The reversed precubical set has the same cells. -/
theorem revPsh_cells (X : PrecubicalSet) (n : ℕ) :
    (revPsh.obj X).cells n = X.cells n := rfl

theorem revPsh_vertex₀ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    (revPsh.obj X).vertex₀ c = X.vertex₁ c := by
  change X.map (Box.rev.map (PrecubicalSet.initVertexMap n)).op c = _
  rw [StdCube.rev_initVertexMap]
  rfl

theorem revPsh_vertex₁ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    (revPsh.obj X).vertex₁ c = X.vertex₀ c := by
  change X.map (Box.rev.map (PrecubicalSet.finalVertexMap n)).op c = _
  rw [StdCube.rev_finalVertexMap]
  rfl

/-- Double reversal is the identity, with identity components (`rev` is an involution on `Box`). -/
def revPshInvol (X : PrecubicalSet) : revPsh.obj (revPsh.obj X) ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro b c g
    change X.map (Box.rev.op.map (Box.rev.op.map g)) ≫ 𝟙 _ = 𝟙 _ ≫ X.map g
    rw [Category.comp_id, Category.id_comp]
    congr 1
    exact congrArg Quiver.Hom.op (Box.rev_rev g.unop))

@[simp] theorem revPshInvol_hom_app (X : PrecubicalSet) (b : Boxᵒᵖ) :
    (revPshInvol X).hom.app b = 𝟙 _ := rfl

@[simp] theorem revPshInvol_inv_app (X : PrecubicalSet) (b : Boxᵒᵖ) :
    (revPshInvol X).inv.app b = 𝟙 _ := rfl

/-- Naturality of the involution `revPsh ⋙ revPsh ≅ 𝟭`. -/
theorem revPshInvol_naturality {X Y : PrecubicalSet} (α : X ⟶ Y) :
    revPsh.map (revPsh.map α) ≫ (revPshInvol Y).hom = (revPshInvol X).hom ≫ α := by
  ext b x
  simp
  rfl

/-- Reversal of a bi-pointed precubical set: reverse the underlying presheaf and swap the two
base points. -/
def BPSet.reverse (K : BPSet) : BPSet where
  toPsh := revPsh.obj K.toPsh
  init := K.final
  final := K.init

@[simp] theorem BPSet.reverse_init (K : BPSet) : (BPSet.reverse K).init = K.final := rfl
@[simp] theorem BPSet.reverse_final (K : BPSet) : (BPSet.reverse K).final = K.init := rfl

/-- Reversal of a bi-pointed map.  Kept as a standalone definition (rather than only as
`revBP.map`) so that its source and target print as `BPSet.reverse X`: `revBP.obj X` does not
unfold at `instances` transparency, and keyed rewriting then fails. -/
def revHomBP {X Y : BPSet} (f : X ⟶ Y) : BPSet.reverse X ⟶ BPSet.reverse Y where
  hom := revPsh.map (f : BPSet.Hom _ _).hom
  app_init := (f : BPSet.Hom _ _).app_final
  app_final := (f : BPSet.Hom _ _).app_init

@[simp] theorem revHomBP_hom {X Y : BPSet} (f : X ⟶ Y) :
    (revHomBP f : BPSet.Hom _ _).hom = revPsh.map (f : BPSet.Hom _ _).hom := rfl

@[simp] theorem revHomBP_id (X : BPSet) : revHomBP (𝟙 X) = 𝟙 (BPSet.reverse X) := rfl

@[simp] theorem revHomBP_comp {X Y Z : BPSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
    revHomBP (f ≫ g) = revHomBP f ≫ revHomBP g := rfl

/-- Reversal as an endofunctor of `BPSet`. -/
def revBP : BPSet ⥤ BPSet where
  obj K := BPSet.reverse K
  map f := revHomBP f
  map_id := revHomBP_id
  map_comp := revHomBP_comp

/-- Double reversal is the identity on `BPSet`. -/
def revInvolAt (X : BPSet) : BPSet.reverse (BPSet.reverse X) ≅ X where
  hom := { hom := (revPshInvol X.toPsh).hom, app_init := rfl, app_final := rfl }
  inv := { hom := (revPshInvol X.toPsh).inv, app_init := rfl, app_final := rfl }
  hom_inv_id := BPSet.hom_ext (revPshInvol X.toPsh).hom_inv_id
  inv_hom_id := BPSet.hom_ext (revPshInvol X.toPsh).inv_hom_id

@[simp] theorem revInvolAt_hom_hom (X : BPSet) :
    ((revInvolAt X).hom : BPSet.Hom _ _).hom = (revPshInvol X.toPsh).hom := rfl

theorem revInvolAt_naturality {X Y : BPSet} (f : X ⟶ Y) :
    revHomBP (revHomBP f) ≫ (revInvolAt Y).hom = (revInvolAt X).hom ≫ f :=
  BPSet.hom_ext (revPshInvol_naturality (f : BPSet.Hom _ _).hom)

/-- `revBP` is an involution. -/
def revBPInvol : revBP ⋙ revBP ≅ 𝟭 BPSet :=
  NatIso.ofComponents revInvolAt (fun f => revInvolAt_naturality f)

/-- Reversal is an equivalence of `BPSet` (self-inverse). -/
noncomputable def revBPEquiv : BPSet ≌ BPSet :=
  CategoryTheory.Equivalence.mk revBP revBP revBPInvol.symm revBPInvol

instance : revBP.Faithful := revBPEquiv.faithful_functor
instance : revBP.Full := revBPEquiv.full_functor

theorem BPSet.eqToHom_hom {X Y : BPSet} (h : X = Y) :
    (eqToHom h : BPSet.Hom X Y).hom = eqToHom (congrArg BPSet.toPsh h) := by
  subst h; rfl

/-! ## Reversal of cube chains

A cube chain of `K.reverse` is a cube chain of `K` read backwards: the *same* cells, in the
reverse order (`revPsh_vertex₀`/`revPsh_vertex₁` swap the two ends of each cube). -/

open CubeChain

theorem isCubeChain_append {X : PrecubicalSet} :
    ∀ (l₁ l₂ : List (Σ n : ℕ+, X.cells (n : ℕ))) (a b : X.cells 0),
      IsCubeChain a (l₁ ++ l₂) b ↔ ∃ m, IsCubeChain a l₁ m ∧ IsCubeChain m l₂ b
  | [], l₂, a, b => by
      constructor
      · exact fun h => ⟨a, rfl, h⟩
      · rintro ⟨m, rfl, h⟩; exact h
  | ⟨n, c⟩ :: l₁, l₂, a, b => by
      rw [List.cons_append]
      change (X.vertex₀ c = a ∧ IsCubeChain (X.vertex₁ c) (l₁ ++ l₂) b) ↔ _
      rw [isCubeChain_append l₁ l₂ (X.vertex₁ c) b]
      constructor
      · rintro ⟨h0, m, h1, h2⟩; exact ⟨m, ⟨h0, h1⟩, h2⟩
      · rintro ⟨m, ⟨h0, h1⟩, h2⟩; exact ⟨h0, m, h1, h2⟩

/-- **A chain reverses**: the same cubes, listed backwards, form a chain of the reversed
precubical set from `b` to `a`. -/
theorem isCubeChain_reverse {X : PrecubicalSet} :
    ∀ (cubes : List (Σ n : ℕ+, X.cells (n : ℕ))) (a b : X.cells 0),
      IsCubeChain a cubes b →
      IsCubeChain (K := revPsh.obj X) b cubes.reverse a
  | [], a, b, h => h.symm
  | ⟨n, c⟩ :: tl, a, b, h => by
      rw [List.reverse_cons]
      refine (isCubeChain_append (X := revPsh.obj X) tl.reverse [⟨n, c⟩] b a).mpr
        ⟨X.vertex₁ c, isCubeChain_reverse tl _ b h.2, ?_⟩
      exact ⟨revPsh_vertex₀ X c, (revPsh_vertex₁ X c).trans h.1⟩

/-! ## The reversed serial wedge

`(⋁d).reverse` is the serial wedge on the reversed dimension sequence.  We build the comparison
map from the *bead chain* of `⋁d` read backwards, and prove it is an isomorphism by a single
cube-list computation (`wRev_comp_vRev`) — no cell-level cast bookkeeping. -/

/-- The beads of a serial wedge, as a cube chain of `⋁d`. -/
noncomputable def beadsOf (d : List ℕ+) : List (Σ n : ℕ+, (⋁d).cells (n : ℕ)) :=
  wedgeToCubes ⟨d, 𝟙 (⋁d).toPsh⟩

theorem beadsOf_dims (d : List ℕ+) : (beadsOf d).map (·.1) = d :=
  wedgeToCubes_dims d _

theorem beadsOf_isCubeChain (d : List ℕ+) :
    IsCubeChain (⋁d).init (beadsOf d) (⋁d).final :=
  wedgeToCubes_isCubeChain d (𝟙 (⋁d).toPsh)

theorem beadsOf_getElem (d : List ℕ+) (k : ℕ) (hk : k < (beadsOf d).length)
    (hk' : k < d.length) :
    (beadsOf d)[k] = ⟨d.get ⟨k, hk'⟩, yonedaEquiv (ιᵂ d ⟨k, hk'⟩)⟩ := by
  have h := wedgeToCubes_get d (𝟙 (⋁d).toPsh) ⟨k, hk⟩
  rw [List.get_eq_getElem] at h
  refine h.trans (congrArg (Sigma.mk _) (congrArg yonedaEquiv (Category.comp_id _)))

/-- The beads of `⋁d`, read backwards: a cube chain of `(⋁d).reverse`. -/
noncomputable def revBeads (d : List ℕ+) :
    List (Σ n : ℕ+, (BPSet.reverse (⋁d)).cells (n : ℕ)) :=
  (beadsOf d).reverse

theorem revBeads_dims (d : List ℕ+) : (revBeads d).map (·.1) = d.reverse :=
  List.map_reverse.trans (congrArg List.reverse (beadsOf_dims d))

theorem revBeads_isCubeChain (d : List ℕ+) :
    IsCubeChain (BPSet.reverse (⋁d)).init (revBeads d) (BPSet.reverse (⋁d)).final :=
  isCubeChain_reverse (beadsOf d) _ _ (beadsOf_isCubeChain d)

/-- The comparison map `⋁(d.reverse) ⟶ (⋁d).reverse`: the bead chain of `⋁d`, backwards. -/
noncomputable def wRev (d e : List ℕ+) (he : e = d.reverse) : ⋁e ⟶ BPSet.reverse (⋁d) :=
  eqToHom (congrArg BPSet.serialWedge
      (show e = (revBeads d).map (·.1) from he.trans (revBeads_dims d).symm))
    ≫ wedgeDescHom (revBeads d)
        (wedgeDesc _ _ (revBeads d) (revBeads_isCubeChain d))

/-- `wedgeToCubes` is insensitive to an `eqToHom` reindexing of the dimension sequence. -/
theorem wedgeToCubes_eqToHom_comp {X : BPSet} {d₁ d₂ : List ℕ+} (E : d₂ = d₁)
    (h : (⋁d₂).toPsh = (⋁d₁).toPsh) (φ : (⋁d₁).toPsh ⟶ X.toPsh) :
    wedgeToCubes ⟨d₂, eqToHom h ≫ φ⟩ = wedgeToCubes ⟨d₁, φ⟩ := by
  subst E
  rw [eqToHom_refl, Category.id_comp]

/-- **The cube list of the comparison map** is exactly the reversed bead chain. -/
theorem wedgeToCubes_wRev (d e : List ℕ+) (he : e = d.reverse) :
    wedgeToCubes ⟨e, (wRev d e he : BPSet.Hom _ _).hom⟩ = revBeads d := by
  have hE : e = (revBeads d).map (·.1) := he.trans (revBeads_dims d).symm
  have h1 : (wRev d e he : BPSet.Hom _ _).hom
      = eqToHom (congrArg (fun l : List ℕ+ => (⋁l).toPsh) hE)
        ≫ (wedgeDesc _ _ (revBeads d) (revBeads_isCubeChain d)).map := by
    rw [wRev, BPSet.comp_hom, BPSet.eqToHom_hom]
    rfl
  rw [h1, wedgeToCubes_eqToHom_comp hE]
  exact wedgeToCubes_wedgeDesc _ _ (revBeads d) (revBeads_isCubeChain d)

/-- Reading the cubes off a post-composed wedge map pushes each cube forward. -/
theorem wedgeToCubes_comp {X Y : BPSet} :
    ∀ (dims : List ℕ+) (φ : (⋁dims).toPsh ⟶ X.toPsh) (g : X.toPsh ⟶ Y.toPsh),
      wedgeToCubes ⟨dims, φ ≫ g⟩
        = (wedgeToCubes ⟨dims, φ⟩).map (fun c => ⟨c.1, g⟪(c.1 : ℕ)⟫ c.2⟩)
  | [], _, _ => by simp [wedgeToCubes]
  | _ :: rest, φ, g => by
      simp only [wedgeToCubes, List.map_cons]
      refine congr_arg₂ List.cons ?_ ?_
      · refine congrArg (Sigma.mk _) ?_
        exact (congrArg yonedaEquiv (Category.assoc _ _ _).symm).trans
          (yonedaEquiv_comp (pushout.inl _ _ ≫ φ) g)
      · refine (congrArg (fun hom => wedgeToCubes ⟨rest, hom⟩)
          (Category.assoc (pushout.inr _ _) φ g).symm).trans ?_
        exact wedgeToCubes_comp rest (pushout.inr _ _ ≫ φ) g

/-- The candidate inverse of `wRev`: the reversal-transpose of the comparison map for `e`. -/
noncomputable def vRev (d e : List ℕ+) (he : e = d.reverse) : BPSet.reverse (⋁d) ⟶ ⋁e :=
  revHomBP (wRev e d (by rw [he, List.reverse_reverse]))
    ≫ (revInvolAt (⋁e)).hom

/-- `vRev` and `wRev` act by the *same function* on cells (reversal is the identity on cells,
and the involution has identity components). -/
theorem vRev_hom_app (d e : List ℕ+) (he : e = d.reverse) (hd : d = e.reverse) {m : ℕ}
    (x : (BPSet.reverse (⋁d)).cells m) :
    (vRev d e he : BPSet.Hom _ _).hom⟪m⟫ x = (wRev e d hd : BPSet.Hom _ _).hom⟪m⟫ x := rfl

/-- **The comparison map is split epi**: `wRev ≫ vRev = 𝟙`.  Proved by a single cube-list
computation — reversal pushes the bead chain of `⋁d` to the bead chain of `⋁e`. -/
theorem wRev_comp_vRev (d e : List ℕ+) (he : e = d.reverse) :
    wRev d e he ≫ vRev d e he = 𝟙 (⋁e) := by
  have hd : d = e.reverse := by rw [he, List.reverse_reverse]
  refine BPSet.hom_ext (wedgeToCubes_inj e _ _ ?_ ?_)
  · have h1 : wedgeToCubes ⟨e, (wRev d e he ≫ vRev d e he : BPSet.Hom _ _).hom⟩
        = (wedgeToCubes ⟨e, (wRev d e he : BPSet.Hom _ _).hom⟩).map
            (fun c => ⟨c.1, (vRev d e he : BPSet.Hom _ _).hom⟪(c.1 : ℕ)⟫ c.2⟩) := by
      rw [BPSet.comp_hom]
      exact wedgeToCubes_comp e _ _
    rw [h1, wedgeToCubes_wRev d e he]
    calc (revBeads d).map (fun c => ⟨c.1, (vRev d e he : BPSet.Hom _ _).hom⟪(c.1 : ℕ)⟫ c.2⟩)
        = (revBeads d).map
            (fun c => ⟨c.1, (wRev e d hd : BPSet.Hom _ _).hom⟪(c.1 : ℕ)⟫ c.2⟩) :=
          List.map_congr_left fun c _ =>
            congrArg (Sigma.mk c.1) (vRev_hom_app d e he hd c.2)
      _ = ((beadsOf d).map
            (fun c => ⟨c.1, (wRev e d hd : BPSet.Hom _ _).hom⟪(c.1 : ℕ)⟫ c.2⟩)).reverse :=
          List.map_reverse
      _ = (wedgeToCubes ⟨d, (wRev e d hd : BPSet.Hom _ _).hom⟩).reverse := by
          refine congrArg List.reverse ?_
          refine ((wedgeToCubes_comp d (𝟙 (⋁d).toPsh) _).symm).trans ?_
          exact congrArg (fun φ => wedgeToCubes ⟨d, φ⟩) (Category.id_comp _)
      _ = (revBeads e).reverse := congrArg List.reverse (wedgeToCubes_wRev e d hd)
      _ = beadsOf e := List.reverse_reverse _
  · exact (wRev d e he ≫ vRev d e he : BPSet.Hom _ _).app_init

theorem vRev_isSplitMono (d e : List ℕ+) (he : e = d.reverse) :
    IsSplitMono (vRev d e he) := by
  have hd : d = e.reverse := by rw [he, List.reverse_reverse]
  refine IsSplitMono.mk' ⟨(revInvolAt (⋁e)).inv ≫ revHomBP (vRev e d hd), ?_⟩
  rw [vRev, Category.assoc, Iso.hom_inv_id_assoc, ← revHomBP_comp,
    wRev_comp_vRev e d hd, revHomBP_id]

/-- **The serial wedge reverses**: `⋁(d.reverse) ≅ (⋁d).reverse` in `BPSet`. -/
noncomputable def wedgeRevIso (d e : List ℕ+) (he : e = d.reverse) :
    ⋁e ≅ BPSet.reverse (⋁d) where
  hom := wRev d e he
  inv := vRev d e he
  hom_inv_id := wRev_comp_vRev d e he
  inv_hom_id := by
    haveI := vRev_isSplitMono d e he
    rw [← cancel_mono (vRev d e he), Category.assoc, wRev_comp_vRev d e he,
      Category.comp_id, Category.id_comp]

/-! ### The bead formula

Which bead of `⋁d` does `wRev` send bead `i` of `⋁e` to?  Bead `j` with `i + j + 1 = d.length`,
via the *reversed* face inclusion — this is what makes `Lines` reversal-compatible. -/

/-- The Yoneda classifier of a cell of `X` inside `revPsh.obj X`, in map form: reverse the box
map.  (`X` and `revPsh.obj X` have the same cells, but not the same face maps.) -/
noncomputable def revCubeNat (m : ℕ) : yoneda.obj ▫m ⟶ revPsh.obj (yoneda.obj ▫m) :=
  yonedaEquiv.symm (𝟙 ▫m : (revPsh.obj (yoneda.obj ▫m)).obj (op ▫m))

@[simp] theorem yonedaEquiv_revCubeNat_self (m : ℕ) :
    yonedaEquiv (revCubeNat m) = 𝟙 ▫m :=
  yonedaEquiv.apply_symm_apply _

/-- `Box.rev` on morphisms, retyped: `rev` is the identity on objects, but `Box.rev.map f`'s
stated type mentions `Box.rev.obj`, which blocks keyed rewriting. -/
def boxRev {m n : Box} (f : m ⟶ n) : m ⟶ n := Box.rev.map f

theorem boxRev_comp {a b c : Box} (f : a ⟶ b) (g : b ⟶ c) :
    boxRev (f ≫ g) = boxRev f ≫ boxRev g := Box.rev.map_comp f g

theorem boxRev_eqToHom {a b : Box} (h : a = b) : boxRev (eqToHom h) = eqToHom h := by
  subst h
  exact Box.rev.map_id a

theorem faceEmb_boxRev {k m : ℕ} (f : ▫k ⟶ ▫m) :
    CubeChain.faceEmb (boxRev f) = CubeChain.faceEmb f := CubeChain.faceEmb_rev f

theorem revCubeNat_app {m : ℕ} (X : Boxᵒᵖ) (f : X.unop ⟶ ▫m) :
    (revCubeNat m).app X f = boxRev f :=
  Category.comp_id (Box.rev.map f)

theorem yonedaEquiv_revCubeNat {X : PrecubicalSet} {m : ℕ} (g : yoneda.obj ▫m ⟶ X) :
    yonedaEquiv (revCubeNat m ≫ revPsh.map g) = yonedaEquiv g := by
  rw [yonedaEquiv_comp, yonedaEquiv_revCubeNat_self]
  rfl

/-- Two cube maps classifying the same `Σ`-cell agree up to the dimension `eqToHom`. -/
theorem yoneda_map_of_sigma {X : PrecubicalSet} {n₁ n₂ : ℕ+} (hdim : n₁ = n₂)
    (f₁ : yoneda.obj ▫((n₁ : ℕ)) ⟶ X) (f₂ : yoneda.obj ▫((n₂ : ℕ)) ⟶ X)
    (h : (⟨n₁, yonedaEquiv f₁⟩ : Σ n : ℕ+, X.cells (n : ℕ)) = ⟨n₂, yonedaEquiv f₂⟩) :
    f₁ = yoneda.map (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) hdim)) ≫ f₂ := by
  subst hdim
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact yonedaEquiv.injective h

theorem beadsOf_length (d : List ℕ+) : (beadsOf d).length = d.length :=
  wedgeToCubes_length d _

theorem revBeads_getElem (d : List ℕ+) (i j : ℕ) (hi : i < (revBeads d).length)
    (hj : j < (beadsOf d).length) (hij : i + j + 1 = d.length) :
    (revBeads d)[i] = (beadsOf d)[j] := by
  have hlen : (beadsOf d).length = d.length := beadsOf_length d
  rw [show (revBeads d)[i] = ((beadsOf d).reverse)[i] from rfl, List.getElem_reverse]
  congr 1
  omega

/-- The `j`-th bead inclusion of `⋁d`, read in `(⋁d).reverse`. -/
noncomputable def revι (d : List ℕ+) (j : Fin d.length) :
    yoneda.obj ▫((d.get j : ℕ+) : ℕ) ⟶ (BPSet.reverse (⋁d)).toPsh :=
  revCubeNat ((d.get j : ℕ+) : ℕ) ≫ revPsh.map (ιᵂ d j)

theorem yonedaEquiv_revι (d : List ℕ+) (j : Fin d.length) :
    yonedaEquiv (F := (BPSet.reverse (⋁d)).toPsh) (revι d j)
      = yonedaEquiv (F := (⋁d).toPsh) (ιᵂ d j) :=
  yonedaEquiv_revCubeNat (ιᵂ d j)

/-- **The bead formula**: `wRev` carries bead `i` of `⋁e` to bead `j` of `⋁d` (`i + j + 1 =
d.length`), via the reversal of that bead's inclusion. -/
theorem ι_comp_wRev (d e : List ℕ+) (he : e = d.reverse) (i : Fin e.length) (j : Fin d.length)
    (hij : (i : ℕ) + (j : ℕ) + 1 = d.length) (hdim : e.get i = d.get j) :
    ιᵂ e i ≫ (wRev d e he : BPSet.Hom _ _).hom
      = yoneda.map (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) hdim)) ≫ revι d j := by
  refine yoneda_map_of_sigma hdim _ _ ?_
  have hi : (i : ℕ) < (wedgeToCubes ⟨e, (wRev d e he : BPSet.Hom _ _).hom⟩).length := by
    rw [wedgeToCubes_length]; exact i.2
  have hi' : (i : ℕ) < (revBeads d).length := by
    rw [← wedgeToCubes_wRev d e he]; exact hi
  have hj : (j : ℕ) < (beadsOf d).length := by
    rw [beadsOf_length]; exact j.2
  calc (⟨e.get i, yonedaEquiv (F := (BPSet.reverse (⋁d)).toPsh)
            (ιᵂ e i ≫ (wRev d e he : BPSet.Hom _ _).hom)⟩
          : Σ n : ℕ+, (BPSet.reverse (⋁d)).cells (n : ℕ))
      = (wedgeToCubes ⟨e, (wRev d e he : BPSet.Hom _ _).hom⟩)[(i : ℕ)] := by
        have h := wedgeToCubes_get e (wRev d e he : BPSet.Hom _ _).hom ⟨(i : ℕ), hi⟩
        rw [List.get_eq_getElem] at h
        exact h.symm
    _ = (revBeads d)[(i : ℕ)] := List.getElem_of_eq (wedgeToCubes_wRev d e he) hi
    _ = (beadsOf d)[(j : ℕ)] := revBeads_getElem d _ _ hi' hj hij
    _ = ⟨d.get j, yonedaEquiv (F := (⋁d).toPsh) (ιᵂ d j)⟩ := beadsOf_getElem d (j : ℕ) hj j.2
    _ = ⟨d.get j, yonedaEquiv (F := (BPSet.reverse (⋁d)).toPsh) (revι d j)⟩ :=
        congrArg (Sigma.mk _) (yonedaEquiv_revι d j).symm

/-- The two-list form of `wRev_comp_vRev`: the reversed dimension sequence is determined, so any
two choices of it are compared by an `eqToHom`. -/
theorem wRev_comp_vRev' (d e e' : List ℕ+) (he : e = d.reverse) (he' : e' = d.reverse) :
    wRev d e he ≫ vRev d e' he'
      = eqToHom (congrArg BPSet.serialWedge (he.trans he'.symm)) := by
  subst he
  subst he'
  rw [eqToHom_refl]
  exact wRev_comp_vRev d d.reverse rfl

/-- The involution is compatible with reversal (both sides have identity components). -/
theorem revHomBP_revInvolAt (X : BPSet) :
    revHomBP ((revInvolAt X).hom) = (revInvolAt (BPSet.reverse X)).hom := rfl

/-! ## The chain category reverses *covariantly*

`Ch K` is ordered by **refinement**, and refinement does not see the direction of time: reversing
a chain reverses its bead list but sends refinements to refinements, in the same direction. -/

theorem eqToHom_symm_comp_assoc {C : Type*} [Category C] {X Y Z : C} (h : X = Y) (f : Y ⟶ Z) :
    eqToHom h.symm ≫ eqToHom h ≫ f = f := by
  subst h; simp

theorem revHomBP_injective {X Y : BPSet} {f g : X ⟶ Y} (h : revHomBP f = revHomBP g) : f = g :=
  revBP.map_injective h

theorem revHomBP_surjective {X Y : BPSet} (g : BPSet.reverse X ⟶ BPSet.reverse Y) :
    ∃ f : X ⟶ Y, revHomBP f = g := revBP.map_surjective g

/-- The reversal iso of the wedge on a chain's dimension sequence. -/
noncomputable abbrev chIso {K : BPSet} (a : Ch K) : ⋁a.dims.reverse ≅ BPSet.reverse (⋁a.dims) :=
  wedgeRevIso a.dims a.dims.reverse rfl

/-- Time reversal of cube chains: reverse each cube and the order of the beads. -/
noncomputable def chRev (K : BPSet) : Ch K ⥤ Ch (BPSet.reverse K) where
  obj a :=
    { dims := a.dims.reverse
      map := (chIso a).hom ≫ revHomBP a.map }
  map {a b} f :=
    { φ := (chIso a).hom ≫ revHomBP (ChainCat.Hom.φ f) ≫ (chIso b).inv
      w := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← revHomBP_comp, ChainCat.Hom.w] }
  map_id a := by
    apply ChainCat.hom_ext'
    simp
  map_comp f g := by
    apply ChainCat.hom_ext'
    simp only [ChainCat.comp_φ, Category.assoc, Iso.inv_hom_id_assoc, revHomBP_comp]

@[simp] theorem chRev_obj_dims {K : BPSet} (a : Ch K) :
    ((chRev K).obj a).dims = a.dims.reverse := rfl

@[simp] theorem chRev_obj_map {K : BPSet} (a : Ch K) :
    ((chRev K).obj a).map = (chIso a).hom ≫ revHomBP a.map := rfl

@[simp] theorem chRev_map_φ {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    ChainCat.Hom.φ ((chRev K).map f)
      = (chIso a).hom ≫ revHomBP (ChainCat.Hom.φ f) ≫ (chIso b).inv := rfl

instance chRev_faithful (K : BPSet) : (chRev K).Faithful where
  map_injective {a b} f g h := by
    apply ChainCat.hom_ext'
    have h' := congrArg ChainCat.Hom.φ h
    simp only [chRev_map_φ] at h'
    have h2 := (Iso.cancel_iso_hom_left (chIso a) _ _).mp h'
    exact revHomBP_injective ((Iso.cancel_iso_inv_right _ _ (chIso b)).mp h2)

instance chRev_full (K : BPSet) : (chRev K).Full where
  map_surjective {a b} ψ := by
    obtain ⟨φ, hφ⟩ := revHomBP_surjective
      ((chIso a).inv ≫ ChainCat.Hom.φ ψ ≫ (chIso b).hom)
    have hψ : ChainCat.Hom.φ ψ ≫ (chIso b).hom ≫ revHomBP b.map
        = (chIso a).hom ≫ revHomBP a.map := ChainCat.Hom.w ψ
    have hw : φ ≫ b.map = a.map := by
      refine revHomBP_injective ?_
      calc revHomBP (φ ≫ b.map)
          = revHomBP φ ≫ revHomBP b.map := revHomBP_comp _ _
        _ = ((chIso a).inv ≫ ChainCat.Hom.φ ψ ≫ (chIso b).hom) ≫ revHomBP b.map :=
            congrArg (· ≫ revHomBP b.map) hφ
        _ = (chIso a).inv ≫ (ChainCat.Hom.φ ψ ≫ (chIso b).hom ≫ revHomBP b.map) := by
            simp only [Category.assoc]
        _ = (chIso a).inv ≫ ((chIso a).hom ≫ revHomBP a.map) :=
            congrArg ((chIso a).inv ≫ ·) hψ
        _ = revHomBP a.map := Iso.inv_hom_id_assoc _ _
    refine ⟨⟨φ, hw⟩, ChainCat.hom_ext' ?_⟩
    rw [chRev_map_φ, hφ]
    simp

/-- The chain of `K` underlying a chain of `K.reverse`. -/
noncomputable def chRevPre {K : BPSet} (c : Ch (BPSet.reverse K)) : Ch K where
  dims := c.dims.reverse
  map := wRev c.dims c.dims.reverse rfl ≫ revHomBP c.map ≫ (revInvolAt K).hom

theorem chRev_obj_chRevPre {K : BPSet} (c : Ch (BPSet.reverse K)) :
    ((chRev K).obj (chRevPre c)).map
      = eqToHom (congrArg BPSet.serialWedge (List.reverse_reverse c.dims)) ≫ c.map := by
  have hrr : c.dims.reverse.reverse = c.dims := List.reverse_reverse c.dims
  have hnat : revHomBP (revHomBP c.map) ≫ revHomBP ((revInvolAt K).hom)
      = (revInvolAt (⋁c.dims)).hom ≫ c.map := by
    rw [revHomBP_revInvolAt]
    exact revInvolAt_naturality c.map
  change wRev c.dims.reverse c.dims.reverse.reverse rfl
      ≫ revHomBP (wRev c.dims c.dims.reverse rfl ≫ revHomBP c.map ≫ (revInvolAt K).hom)
    = eqToHom (congrArg BPSet.serialWedge hrr) ≫ c.map
  calc wRev c.dims.reverse c.dims.reverse.reverse rfl
        ≫ revHomBP (wRev c.dims c.dims.reverse rfl ≫ revHomBP c.map ≫ (revInvolAt K).hom)
      = wRev c.dims.reverse c.dims.reverse.reverse rfl
        ≫ (revHomBP (wRev c.dims c.dims.reverse rfl)
          ≫ (revHomBP (revHomBP c.map) ≫ revHomBP ((revInvolAt K).hom))) := by
        rw [revHomBP_comp, revHomBP_comp]
    _ = wRev c.dims.reverse c.dims.reverse.reverse rfl
        ≫ (revHomBP (wRev c.dims c.dims.reverse rfl)
          ≫ ((revInvolAt (⋁c.dims)).hom ≫ c.map)) :=
        congrArg (wRev c.dims.reverse c.dims.reverse.reverse rfl ≫ ·)
          (congrArg (revHomBP (wRev c.dims c.dims.reverse rfl) ≫ ·) hnat)
    _ = (wRev c.dims.reverse c.dims.reverse.reverse rfl
          ≫ vRev c.dims.reverse c.dims (by rw [hrr])) ≫ c.map := by
        rw [vRev]
        simp only [Category.assoc]
    _ = eqToHom (congrArg BPSet.serialWedge hrr) ≫ c.map := by
        rw [wRev_comp_vRev' c.dims.reverse c.dims.reverse.reverse c.dims rfl (by rw [hrr])]

instance chRev_essSurj (K : BPSet) : (chRev K).EssSurj where
  mem_essImage c := by
    have hrr : c.dims.reverse.reverse = c.dims := List.reverse_reverse c.dims
    have hmap := chRev_obj_chRevPre c
    exact ⟨chRevPre c, ⟨{
      hom := ⟨eqToHom (congrArg BPSet.serialWedge hrr), hmap.symm⟩
      inv := ⟨eqToHom (congrArg BPSet.serialWedge hrr.symm), by
        rw [hmap]; exact eqToHom_symm_comp_assoc _ _⟩
      hom_inv_id := by apply ChainCat.hom_ext'; simp
      inv_hom_id := by apply ChainCat.hom_ext'; simp }⟩⟩

instance chRev_isEquivalence (K : BPSet) : (chRev K).IsEquivalence := {}

/-- **The chain category is reversal-invariant**: `Ch (K.reverse) ≌ Ch K`.  Note the *covariance*
— a refinement of a reversed chain is the reverse of a refinement. -/
noncomputable def chRevEquiv (K : BPSet) : Ch K ≌ Ch (BPSet.reverse K) :=
  (chRev K).asEquivalence

/-! ## The block data of a reversed chain map

Bead `i` of `⋁(a.dims.reverse)` is bead `revBead a.dims i` of `⋁a.dims`; a reversed chain map
sends it to the reversed target block, through the *reversed* face inclusion. -/

theorem revBead_lt {d : List ℕ+} (i : Fin d.reverse.length) : (i : ℕ) < d.length := by
  simpa using i.2

/-- Bead `i` of `d.reverse` is bead `revBead d i` of `d`. -/
def revBead (d : List ℕ+) (i : Fin d.reverse.length) : Fin d.length :=
  ⟨d.length - 1 - (i : ℕ), by have := revBead_lt i; omega⟩

theorem revBead_add (d : List ℕ+) (i : Fin d.reverse.length) :
    (i : ℕ) + (revBead d i : ℕ) + 1 = d.length := by
  have := revBead_lt i
  change (i : ℕ) + (d.length - 1 - (i : ℕ)) + 1 = d.length
  omega

theorem revBead_dim (d : List ℕ+) (i : Fin d.reverse.length) :
    d.reverse.get i = d.get (revBead d i) := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_reverse]
  rfl

/-- The bead index of `d.reverse` matching bead `j` of `d`. -/
def revBead' (d : List ℕ+) (j : Fin d.length) : Fin d.reverse.length :=
  ⟨d.length - 1 - (j : ℕ), by rw [List.length_reverse]; have := j.2; omega⟩

theorem revBead_revBead' (d : List ℕ+) (j : Fin d.length) :
    revBead d (revBead' d j) = j := by
  apply Fin.ext
  have := j.2
  change d.length - 1 - (d.length - 1 - (j : ℕ)) = (j : ℕ)
  omega

/-- `Fin`-level reversal of the bead index. -/
def finRevEquiv (d : List ℕ+) : Fin d.length ≃ Fin d.reverse.length where
  toFun := revBead' d
  invFun := revBead d
  left_inv j := revBead_revBead' d j
  right_inv i := by
    apply Fin.ext
    have := revBead_lt i
    change d.length - 1 - (d.length - 1 - (i : ℕ)) = (i : ℕ)
    omega

theorem revBead'_add (d : List ℕ+) (j : Fin d.length) :
    (revBead' d j : ℕ) + (j : ℕ) + 1 = d.length := by
  have := j.2
  change (d.length - 1 - (j : ℕ)) + (j : ℕ) + 1 = d.length
  omega

theorem revBead'_dim (d : List ℕ+) (j : Fin d.length) :
    d.reverse.get (revBead' d j) = d.get j := by
  rw [revBead_dim d (revBead' d j), revBead_revBead' d j]

/-- The reversal of a bead's face inclusion, retyped along the two dimension equalities. -/
noncomputable def revFace {ad bd : List ℕ+} {j : Fin ad.length} {r : Fin bd.length}
    (g : ▫((ad.get j : ℕ+) : ℕ) ⟶ ▫((bd.get r : ℕ+) : ℕ)) :
    ▫((ad.reverse.get (revBead' ad j) : ℕ+) : ℕ) ⟶ ▫((bd.reverse.get (revBead' bd r) : ℕ+) : ℕ) :=
  eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim ad j))
    ≫ boxRev g
    ≫ eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim bd r).symm)

theorem faceEmb_revFace {ad bd : List ℕ+} {j : Fin ad.length} {r : Fin bd.length}
    (g : ▫((ad.get j : ℕ+) : ℕ) ⟶ ▫((bd.get r : ℕ+) : ℕ))
    (x : Fin ((ad.reverse.get (revBead' ad j) : ℕ+) : ℕ)) :
    ((CubeChain.faceEmb (revFace g)) x : ℕ)
      = ((CubeChain.faceEmb g) (Fin.cast (congrArg (fun n : ℕ+ => (n : ℕ))
          (revBead'_dim ad j)) x) : ℕ) := by
  have h1 : CubeChain.faceEmb (revFace g) x
      = CubeChain.faceEmb (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ)))
            (revBead'_dim bd r).symm))
          (CubeChain.faceEmb (boxRev g)
            (CubeChain.faceEmb (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ)))
              (revBead'_dim ad j))) x)) := by
    rw [revFace, CubeChain.faceEmb_comp
      (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim ad j)))
      (boxRev g ≫ eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim bd r).symm)) x,
      CubeChain.faceEmb_comp (boxRev g)
        (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim bd r).symm))]
  have hx : CubeChain.faceEmb
        (eqToHom (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim ad j))) x
      = Fin.cast (congrArg (fun n : ℕ+ => (n : ℕ)) (revBead'_dim ad j)) x :=
    Fin.ext (CubeChain.faceEmb_eqToHom_val
      (congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim ad j)) x)
  rw [h1, CubeChain.faceEmb_eqToHom_val, faceEmb_boxRev, hx]

/-- `revι` absorbs a post-composition. -/
theorem revι_comp {d : List ℕ+} {X : PrecubicalSet} (j : Fin d.length)
    (ψ : (⋁d).toPsh ⟶ X) :
    revι d j ≫ revPsh.map ψ
      = revCubeNat ((d.get j : ℕ+) : ℕ) ≫ revPsh.map (ιᵂ d j ≫ ψ) :=
  (Category.assoc (revCubeNat _) (revPsh.map (ιᵂ d j)) (revPsh.map ψ)).trans
    (congrArg (revCubeNat ((d.get j : ℕ+) : ℕ) ≫ ·) (revPsh.map_comp (ιᵂ d j) ψ).symm)

/-- Conjugating a box map by the reversal comparison gives its reversal. -/
theorem revCubeNat_conj {m n : ℕ} (h : ▫m ⟶ ▫n) :
    revCubeNat m ≫ revPsh.map (yoneda.map h ≫ revCubeNat n)
        ≫ (revPshInvol (yoneda.obj ▫n)).hom
      = yoneda.map (boxRev h) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_yoneda_map, ← Category.assoc, yonedaEquiv_comp,
    yonedaEquiv_comp, yonedaEquiv_revCubeNat_self]
  change (revPshInvol (yoneda.obj ▫n)).hom.app (op ▫m)
      ((revCubeNat n).app (op ▫m) ((yoneda.map h).app (op ▫m) (𝟙 ▫m))) = _
  rw [revPshInvol_hom_app]
  change (revCubeNat n).app (op ▫m) ((yoneda.map h).app (op ▫m) (𝟙 ▫m)) = _
  rw [revCubeNat_app]
  congr 1

/-- **Block factorization of a reversed chain map**: bead `j` of `a` reverses to bead
`revBead' a.dims j` of the reversed chain, and lands in the reversed target block through the
reversed face. -/
theorem ι_comp_chRev {K : BPSet} {a b : Ch K} (f : a ⟶ b) (j : Fin a.dims.length) :
    ιᵂ a.dims.reverse (revBead' a.dims j) ≫ ((chRev K).map f)ᵂ
      = yoneda.map (revFace (blockFace fᵂ j))
        ≫ ιᵂ b.dims.reverse (revBead' b.dims (blockIdx fᵂ j)) := by
  have hbd : b.dims = b.dims.reverse.reverse := (List.reverse_reverse _).symm
  set bi := blockIdx fᵂ j with hbi
  set bf := blockFace fᵂ j with hbf
  set r := revBead' b.dims bi with hr
  set hA := congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim a.dims j) with hAdef
  set hB := congrArg (fun n : ℕ+ => ▫((n : ℕ))) (revBead'_dim b.dims bi).symm with hBdef
  set Wb := (wRev b.dims.reverse b.dims hbd : BPSet.Hom _ _).hom with hWb
  set inv2 := (revPshInvol ((⋁b.dims.reverse).toPsh)).hom with hinv2
  set T : (BPSet.reverse (⋁a.dims)).toPsh ⟶ (⋁b.dims.reverse).toPsh :=
    revPsh.map fᵂ ≫ (revPsh.map Wb ≫ inv2) with hT
  have hφ : ((chRev K).map f)ᵂ
      = (wRev a.dims a.dims.reverse rfl : BPSet.Hom _ _).hom ≫ T := rfl
  have s1 : ιᵂ a.dims.reverse (revBead' a.dims j)
        ≫ (wRev a.dims a.dims.reverse rfl : BPSet.Hom _ _).hom
      = yoneda.map (eqToHom hA) ≫ revι a.dims j :=
    ι_comp_wRev a.dims a.dims.reverse rfl (revBead' a.dims j) j
      (revBead'_add a.dims j) (revBead'_dim a.dims j)
  have s5 : ιᵂ b.dims bi ≫ Wb
      = yoneda.map (eqToHom hB) ≫ revι b.dims.reverse r := by
    refine ι_comp_wRev b.dims.reverse b.dims hbd bi r ?_ (revBead'_dim b.dims bi).symm
    have hlt := bi.2
    change (bi : ℕ) + (b.dims.length - 1 - (bi : ℕ)) + 1 = b.dims.reverse.length
    rw [List.length_reverse]
    omega
  -- All of the following is at `PrecubicalSet` (a functor category), where `rw`/`simp` fail on
  -- `Category.assoc` (instance-path mismatch); hence the term-mode `congrArg` chains.
  set m := ((b.dims.reverse.get r : ℕ+) : ℕ) with hm
  set G : ▫((a.dims.get j : ℕ+) : ℕ) ⟶ ▫m := bf ≫ eqToHom hB with hG
  have hinner : ιᵂ a.dims j ≫ (fᵂ ≫ Wb)
      = yoneda.map G ≫ revι b.dims.reverse r :=
    calc ιᵂ a.dims j ≫ (fᵂ ≫ Wb)
        = (ιᵂ a.dims j ≫ fᵂ) ≫ Wb := (Category.assoc _ _ _).symm
      _ = (yoneda.map bf ≫ ιᵂ b.dims bi) ≫ Wb := congrArg (· ≫ Wb) (blockFace_spec fᵂ j)
      _ = yoneda.map bf ≫ (ιᵂ b.dims bi ≫ Wb) := Category.assoc _ _ _
      _ = yoneda.map bf ≫ (yoneda.map (eqToHom hB) ≫ revι b.dims.reverse r) :=
          congrArg (yoneda.map bf ≫ ·) s5
      _ = (yoneda.map bf ≫ yoneda.map (eqToHom hB)) ≫ revι b.dims.reverse r :=
          (Category.assoc _ _ _).symm
      _ = yoneda.map G ≫ revι b.dims.reverse r :=
          congrArg (· ≫ revι b.dims.reverse r) (yoneda.map_comp bf (eqToHom hB)).symm
  have hconj : revCubeNat ((a.dims.get j : ℕ+) : ℕ)
        ≫ (revPsh.map (yoneda.map G ≫ revCubeNat m)
          ≫ (revPshInvol (yoneda.obj ▫m)).hom)
      = yoneda.map (boxRev G) := revCubeNat_conj G
  have key : revι a.dims j ≫ T
      = yoneda.map (boxRev G) ≫ ιᵂ b.dims.reverse r :=
    calc revι a.dims j ≫ T
        = revι a.dims j ≫ ((revPsh.map fᵂ ≫ revPsh.map Wb) ≫ inv2) :=
          congrArg (revι a.dims j ≫ ·) (Category.assoc _ _ _).symm
      _ = revι a.dims j ≫ (revPsh.map (fᵂ ≫ Wb) ≫ inv2) :=
          congrArg (fun x => revι a.dims j ≫ (x ≫ inv2)) (revPsh.map_comp fᵂ Wb).symm
      _ = (revι a.dims j ≫ revPsh.map (fᵂ ≫ Wb)) ≫ inv2 := (Category.assoc _ _ _).symm
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ revPsh.map (ιᵂ a.dims j ≫ (fᵂ ≫ Wb))) ≫ inv2 :=
          congrArg (· ≫ inv2) (revι_comp j (fᵂ ≫ Wb))
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ revPsh.map (yoneda.map G ≫ (revCubeNat m ≫ revPsh.map (ιᵂ b.dims.reverse r))))
          ≫ inv2 :=
          congrArg (fun x => (revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map x) ≫ inv2) hinner
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ revPsh.map ((yoneda.map G ≫ revCubeNat m)
              ≫ revPsh.map (ιᵂ b.dims.reverse r))) ≫ inv2 :=
          congrArg (fun x => (revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map x) ≫ inv2)
            (Category.assoc _ _ _).symm
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ (revPsh.map (yoneda.map G ≫ revCubeNat m)
              ≫ revPsh.map (revPsh.map (ιᵂ b.dims.reverse r)))) ≫ inv2 :=
          congrArg (fun x => (revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ x) ≫ inv2)
            (revPsh.map_comp (yoneda.map G ≫ revCubeNat m) (revPsh.map (ιᵂ b.dims.reverse r)))
      _ = ((revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map (yoneda.map G ≫ revCubeNat m))
            ≫ revPsh.map (revPsh.map (ιᵂ b.dims.reverse r))) ≫ inv2 :=
          congrArg (· ≫ inv2) (Category.assoc _ _ _).symm
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map (yoneda.map G ≫ revCubeNat m))
            ≫ (revPsh.map (revPsh.map (ιᵂ b.dims.reverse r)) ≫ inv2) :=
          Category.assoc _ _ _
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map (yoneda.map G ≫ revCubeNat m))
            ≫ ((revPshInvol (yoneda.obj ▫m)).hom ≫ ιᵂ b.dims.reverse r) :=
          congrArg ((revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ revPsh.map (yoneda.map G ≫ revCubeNat m)) ≫ ·)
            (revPshInvol_naturality (ιᵂ b.dims.reverse r))
      _ = ((revCubeNat ((a.dims.get j : ℕ+) : ℕ) ≫ revPsh.map (yoneda.map G ≫ revCubeNat m))
            ≫ (revPshInvol (yoneda.obj ▫m)).hom) ≫ ιᵂ b.dims.reverse r :=
          (Category.assoc _ _ _).symm
      _ = (revCubeNat ((a.dims.get j : ℕ+) : ℕ)
            ≫ (revPsh.map (yoneda.map G ≫ revCubeNat m)
              ≫ (revPshInvol (yoneda.obj ▫m)).hom)) ≫ ιᵂ b.dims.reverse r :=
          congrArg (· ≫ ιᵂ b.dims.reverse r) (Category.assoc _ _ _)
      _ = yoneda.map (boxRev G) ≫ ιᵂ b.dims.reverse r :=
          congrArg (· ≫ ιᵂ b.dims.reverse r) hconj
  -- `(□n).toPsh` and `yoneda.obj ▫n` are defeq but not syntactically equal, so `calc`'s `Trans`
  -- synthesis fails here; term-mode `.trans` tolerates the defeq.
  refine (congrArg (ιᵂ a.dims.reverse (revBead' a.dims j) ≫ ·) hφ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun x => x ≫ T) s1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun x => yoneda.map (eqToHom hA) ≫ x) key).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun x => x ≫ ιᵂ b.dims.reverse r)
    (yoneda.map_comp (eqToHom hA) (boxRev G)).symm).trans ?_
  rw [hG, boxRev_comp, boxRev_eqToHom]
  rfl

/-! ## `Lines` is reversal-compatible

A chamber records which direction of a bead flips first; under time reversal it becomes the
*opposite* strict total order. -/

/-- The opposite order of a chamber: the direction that flipped first now flips last. -/
def Chamber.op {d : ℕ} (c : Chamber d) : Chamber d where
  lt := Function.swap c.lt
  sto :=
    haveI := c.sto
    inferInstance

@[simp] theorem Chamber.op_lt {d : ℕ} (c : Chamber d) (a b : Fin d) :
    c.op.lt a b = c.lt b a := rfl

theorem Chamber.op_op {d : ℕ} (c : Chamber d) : c.op.op = c := Chamber.ext rfl

theorem Chamber.op_restrict {d e : ℕ} (c : Chamber e) (g : Fin d → Fin e)
    (hg : Function.Injective g) :
    (c.restrict g hg).op = c.op.restrict g hg := Chamber.ext rfl

/-- Taking the opposite order, as an equivalence. -/
def Chamber.opEquiv (d : ℕ) : Chamber d ≃ Chamber d where
  toFun := Chamber.op
  invFun := Chamber.op
  left_inv := Chamber.op_op
  right_inv := Chamber.op_op

/-- Transport a chamber along a dimension equality — as a `restrict`, so that it composes with the
other reindexings. -/
def chamberCast {n m : ℕ} (h : n = m) (c : Chamber n) : Chamber m :=
  c.restrict (Fin.cast h.symm) (Fin.cast_injective _)

theorem chamberCast_chamberCast {n m : ℕ} (h : n = m) (c : Chamber n) :
    chamberCast h.symm (chamberCast h c) = c := by
  rw [chamberCast, chamberCast, Chamber.restrict_restrict]
  exact c.restrict_id_of _ (fun _ => rfl)

/-- `chamberCast`, as an equivalence. -/
def chamberCastEquiv {n m : ℕ} (h : n = m) : Chamber n ≃ Chamber m where
  toFun := chamberCast h
  invFun := chamberCast h.symm
  left_inv c := chamberCast_chamberCast h c
  right_inv c := chamberCast_chamberCast h.symm c

/-- Reversing the chambers of a chain: reverse the bead order, and take the opposite order of the
directions inside each bead. -/
noncomputable def revChambersEquiv (d : List ℕ+) :
    (∀ j : Fin d.length, Chamber ((d.get j : ℕ+) : ℕ))
      ≃ (∀ i : Fin d.reverse.length, Chamber ((d.reverse.get i : ℕ+) : ℕ)) :=
  Equiv.piCongr (finRevEquiv d) fun j =>
    (Chamber.opEquiv _).trans
      (chamberCastEquiv (congrArg (fun n : ℕ+ => ((n : ℕ))) (revBead'_dim d j).symm))

theorem revChambersEquiv_apply (d : List ℕ+)
    (L : ∀ j : Fin d.length, Chamber ((d.get j : ℕ+) : ℕ)) (j : Fin d.length) :
    revChambersEquiv d L (revBead' d j)
      = chamberCast (congrArg (fun n : ℕ+ => ((n : ℕ))) (revBead'_dim d j).symm) (L j).op :=
  Equiv.piCongr_apply_apply (finRevEquiv d) _ L j

/-- **Reversal intertwines chamber restriction**: reversing a chain map's chamber restriction is
the chamber restriction of the reversed chain map. -/
theorem linesRestrict_chRev {K : BPSet} {a b : Ch K} (f : a ⟶ b) (L : LinesObj b) :
    revChambersEquiv a.dims (linesRestrict f L)
      = linesRestrict ((chRev K).map f) (revChambersEquiv b.dims L) := by
  funext i
  obtain ⟨j, rfl⟩ : ∃ j : Fin a.dims.length, revBead' a.dims j = i :=
    ⟨revBead a.dims i, (finRevEquiv a.dims).right_inv i⟩
  set bi := blockIdx fᵂ j with hbi
  set bf := blockFace fᵂ j with hbf
  have hfac := restrict_factor ((chRev K).map f)ᵂ (revBead' a.dims j)
    (revBead' b.dims bi) (revFace bf) (ι_comp_chRev f j) (revChambersEquiv b.dims L)
  have hLHS : revChambersEquiv a.dims (linesRestrict f L) (revBead' a.dims j)
      = chamberCast (congrArg (fun n : ℕ+ => ((n : ℕ))) (revBead'_dim a.dims j).symm)
        ((L bi).op.restrict (CubeChain.faceEmb bf) (CubeChain.faceEmb bf).injective) := by
    rw [revChambersEquiv_apply, linesRestrict, ← Chamber.op_restrict]
  have hRHS : linesRestrict ((chRev K).map f) (revChambersEquiv b.dims L) (revBead' a.dims j)
      = (chamberCast (congrArg (fun n : ℕ+ => ((n : ℕ))) (revBead'_dim b.dims bi).symm)
          ((L bi).op)).restrict (CubeChain.faceEmb (revFace bf))
            (CubeChain.faceEmb (revFace bf)).injective := by
    rw [linesRestrict, hfac, revChambersEquiv_apply]
    rfl
  rw [hLHS, hRHS, chamberCast, chamberCast, Chamber.restrict_restrict,
    Chamber.restrict_restrict]
  refine Chamber.restrict_congr _ _ _ fun x => ?_
  apply Fin.ext
  exact (faceEmb_revFace bf x).symm

/-- **`Lines` is reversal-compatible.** -/
noncomputable def linesRevIso (K : BPSet) :
    Lines K ≅ (chRev K).op ⋙ Lines (BPSet.reverse K) :=
  NatIso.ofComponents (fun A => Equiv.toIso (revChambersEquiv A.unop.dims))
    (by
      intro A B φ
      apply ConcreteCategory.hom_ext
      intro L
      simp only [Functor.comp_map, types_comp_apply]
      exact linesRestrict_chRev φ.unop L)

end CubeChains

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

/-- Elements transport along an equivalence of the base together with an iso of the presheaves. -/
noncomputable def elementsCongr {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (e : C ≌ D) {F : C ⥤ Type w} {G : D ⥤ Type w} (θ : F ≅ e.functor ⋙ G) :
    F.Elements ≌ G.Elements := by
  let P : F.Elements ⥤ G.Elements :=
    { obj := fun x => ⟨e.functor.obj x.1, θ.hom.app x.1 x.2⟩
      map := fun {x y} f => ⟨e.functor.map f.val, by
        have h := NatTrans.naturality_apply θ.hom f.val x.2
        rw [f.property] at h
        exact h.symm⟩
      map_id := fun x => by apply CategoryOfElements.ext; simp
      map_comp := fun f g => by apply CategoryOfElements.ext; simp }
  haveI : P.Faithful := ⟨fun {x y} f g h => by
    apply CategoryOfElements.ext
    exact e.functor.map_injective (congrArg Subtype.val h)⟩
  haveI : P.Full := ⟨fun {x y} ψ => by
    obtain ⟨h, hh⟩ := e.functor.map_surjective ψ.val
    refine ⟨⟨h, ?_⟩, ?_⟩
    · refine (θ.app y.1).toEquiv.injective ?_
      have hnat := NatTrans.naturality_apply θ.hom h x.2
      have hψ := ψ.property
      rw [Functor.comp_map, hh] at hnat
      exact hnat.trans hψ
    · apply CategoryOfElements.ext
      exact hh⟩
  haveI : P.EssSurj := ⟨fun z => by
    refine ⟨⟨e.inverse.obj z.1,
      θ.inv.app (e.inverse.obj z.1) (G.map (e.counitIso.app z.1).inv z.2)⟩, ⟨?_⟩⟩
    refine CategoryOfElements.isoMk _ _ (e.counitIso.app z.1) ?_
    change G.map (e.counitIso.app z.1).hom
        (θ.hom.app _ (θ.inv.app _ (G.map (e.counitIso.app z.1).inv z.2))) = z.2
    rw [← types_comp_apply (θ.inv.app _) (θ.hom.app _), θ.inv_hom_id_app]
    rw [types_id_apply, ← types_comp_apply (G.map _) (G.map _), ← G.map_comp,
      Iso.inv_hom_id, G.map_id, types_id_apply]⟩
  haveI : P.IsEquivalence := {}
  exact P.asEquivalence

end CategoryTheory

namespace CubeChains

/-- **The concurrency category is time-reversal invariant.** -/
noncomputable def concCatRevEquiv (K : BPSet) : ConcCat K ≌ ConcCat (BPSet.reverse K) :=
  elementsCongr (chRevEquiv K).op (linesRevIso K)

/-- **The concurrency braid groupoid is time-reversal invariant**: `ConcGrpd (K.reverse) ≌
ConcGrpd K`.  Concurrency is symmetric in time — only the *causal* structure is not, and the
chamber presheaf (hence its groupoid of elements) does not see it.

The chain category itself is reversal-invariant too (`chRevEquiv`), for the more basic reason
that its morphisms are **refinements**: reversing time reverses the bead list of a chain but takes
refinements to refinements, in the same direction. -/
noncomputable def concGrpdReverse (K : BPSet) : ConcGrpd (BPSet.reverse K) ≌ ConcGrpd K :=
  (freeGroupoidCongr (concCatRevEquiv K)).symm

end CubeChains
