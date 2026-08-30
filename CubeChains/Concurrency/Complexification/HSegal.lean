import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Concurrency.Complexification.RunClassifier

/-!
# Concurrency/Complexification/HSegal — `H` makes the wedge the tensor

`▪(p+q)` **is** the wedge `▪p ∨ ▪q` in the symmetric box category: an injective word of length
`p+q` is a word of length `p` followed by a disjoint one of length `q`.  `Box` sees only the one
splitting, `SBox` sees all `binom(p+q,p)` — that gap is the braiding, and `H(□ⁿ) ≅ J*y(▪n)` closes
it.
-/

open CategoryTheory Opposite StdCube BPSet ChainCat CubeChain

namespace CubeChains

/-! ### Composability in `SBox`, read on coordinates -/

/-- The final vertex of `▪m`, coordinatewise: every direction is held at `1`. -/
theorem coord_J_finalVertexMap (m : ℕ) (z : Fin m) :
    SHom.coord (J.map (PrecubicalSet.finalVertexMap m)) z = Sum.inl true := by
  rw [J_map_coord, sign_finalVertexMap]
  exact (cellCoord_eq_inl_iff _ _ _).2 rfl

/-- …and the initial vertex holds every direction at `0`. -/
theorem coord_J_initVertexMap (m : ℕ) (z : Fin m) :
    SHom.coord (J.map (PrecubicalSet.initVertexMap m)) z = Sum.inl false := by
  rw [J_map_coord, sign_initVertexMap]
  exact (cellCoord_eq_inl_iff _ _ _).2 rfl

namespace SHom

variable {p q n : ℕ} {f : SHom p n} {g : SHom q n}

/-- Composability of `f` and `g`, coordinate by coordinate: `f`'s free directions read `1` where
`g` reads a sign, `g`'s read `0`, and off both the signs agree. -/
theorem coord_of_vertex_eq
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) (k : Fin n) :
    ((f.coord k).elim Sum.inl (fun _ => Sum.inl true) : Bool ⊕ Fin 0)
      = (g.coord k).elim Sum.inl (fun _ => Sum.inl false) := by
  have hk := congrFun (congrArg SHom.coord h) k
  rw [SBox.comp_coord, SBox.comp_coord] at hk
  rw [show SHom.coord (J.map (PrecubicalSet.finalVertexMap p))
      = fun _ => Sum.inl true from funext (coord_J_finalVertexMap p),
    show SHom.coord (J.map (PrecubicalSet.initVertexMap q))
      = fun _ => Sum.inl false from funext (coord_J_initVertexMap q)] at hk
  exact hk

/-- **Disjointness**: where `g` runs a direction, `f` holds the sign `0`. -/
theorem coord_left_of_right
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) {k : Fin n} {j : Fin q}
    (hg : g.coord k = Sum.inr j) : f.coord k = Sum.inl false := by
  have hk := coord_of_vertex_eq h k
  rw [hg] at hk
  rcases hc : f.coord k with b | i
  · rw [hc] at hk; exact congrArg Sum.inl (Sum.inl.inj hk)
  · rw [hc] at hk; exact absurd (Sum.inl.inj hk) (by simp)

/-- …and where `f` runs a direction, `g` holds the sign `1`. -/
theorem coord_right_of_left
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) {k : Fin n} {i : Fin p}
    (hf : f.coord k = Sum.inr i) : g.coord k = Sum.inl true := by
  have hk := coord_of_vertex_eq h k
  rw [hf] at hk
  rcases hc : g.coord k with b | j
  · rw [hc] at hk; exact congrArg Sum.inl (Sum.inl.inj hk).symm
  · rw [hc] at hk; exact absurd (Sum.inl.inj hk) (by simp)

/-- …and off both they agree. -/
theorem coord_sign_eq
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) {k : Fin n} {b b' : Bool}
    (hf : f.coord k = Sum.inl b) (hg : g.coord k = Sum.inl b') : b = b' := by
  have hk := coord_of_vertex_eq h k
  rw [hf, hg] at hk
  exact Sum.inl.inj hk

/-! ### The composite -/

/-- **The composite of two composable symmetric cube maps**: `f`'s directions first, then `g`'s. -/
def merge (f : SHom p n) (g : SHom q n)
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) : SHom (p + q) n where
  coord k := (f.coord k).elim
    (fun b => (g.coord k).elim (fun _ => Sum.inl b) (fun j => Sum.inr (Fin.natAdd p j)))
    (fun i => Sum.inr (Fin.castAdd q i))
  pos := Fin.append f.pos g.pos
  coord_pos i := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      show (f.coord (f.pos i)).elim _ _ = _
      rw [f.coord_pos, Sum.elim_inr]
    · rw [Fin.append_right]
      show (f.coord (g.pos j)).elim _ _ = _
      rw [coord_left_of_right h (g.coord_pos j), Sum.elim_inl, g.coord_pos j, Sum.elim_inr]
  pos_eq i k hk := by
    replace hk : (f.coord k).elim
        (fun b => (g.coord k).elim (fun _ => Sum.inl b) (fun j => Sum.inr (Fin.natAdd p j)))
        (fun i => Sum.inr (Fin.castAdd q i)) = Sum.inr i := hk
    rcases hf : f.coord k with b | i'
    · rcases hg : g.coord k with b' | j'
      · rw [hf, Sum.elim_inl, hg, Sum.elim_inl] at hk; exact absurd hk (by simp)
      · rw [hf, Sum.elim_inl, hg, Sum.elim_inr] at hk
        obtain rfl : i = Fin.natAdd p j' := (Sum.inr.inj hk).symm
        rw [Fin.append_right]
        exact g.pos_eq j' k hg
    · rw [hf, Sum.elim_inr] at hk
      obtain rfl : i = Fin.castAdd q i' := (Sum.inr.inj hk).symm
      rw [Fin.append_left]
      exact f.pos_eq i' k hf

theorem coord_merge (f : SHom p n) (g : SHom q n) (h) (k : Fin n) :
    (merge f g h).coord k = (f.coord k).elim
      (fun b => (g.coord k).elim (fun _ => Sum.inl b) (fun j => Sum.inr (Fin.natAdd p j)))
      (fun i => Sum.inr (Fin.castAdd q i)) := rfl

theorem coord_merge_left (f : SHom p n) (g : SHom q n) (h) {k : Fin n} {i : Fin p}
    (hf : f.coord k = Sum.inr i) : (merge f g h).coord k = Sum.inr (Fin.castAdd q i) := by
  rw [coord_merge, hf, Sum.elim_inr]

theorem coord_merge_right (f : SHom p n) (g : SHom q n) (h) {k : Fin n} {j : Fin q}
    (hg : g.coord k = Sum.inr j) : (merge f g h).coord k = Sum.inr (Fin.natAdd p j) := by
  rw [coord_merge, coord_left_of_right h hg, Sum.elim_inl, hg, Sum.elim_inr]

theorem coord_merge_sign (f : SHom p n) (g : SHom q n) (h) {k : Fin n} {b b' : Bool}
    (hf : f.coord k = Sum.inl b) (hg : g.coord k = Sum.inl b') :
    (merge f g h).coord k = Sum.inl b := by
  rw [coord_merge, hf, Sum.elim_inl, hg, Sum.elim_inl]

end SHom

/-! ### `▪(p+q)` is the wedge of `▪p` and `▪q`

Restriction along the two legs of `cubeMerge`, read in `SBox`, splits a word into its first `p`
and last `q` letters. -/

/-- Restriction of a symmetric cube map along the front leg. -/
theorem coord_frontHom_comp {p q n : ℕ} (c : SHom (p + q) n) (k : Fin n) :
    (J.map (frontHom p q) ≫ c : ▪p ⟶ ▪n).coord k
      = (c.coord k).elim Sum.inl fun i =>
          Fin.addCases (fun i' => Sum.inr i') (fun _ => Sum.inl false) i := by
  rw [SBox.comp_coord]
  rcases hc : c.coord k with b | i
  · rfl
  · refine congrArg (fun t => (Sum.inr i : Bool ⊕ Fin (p + q)).elim Sum.inl t) (funext fun z => ?_)
    refine Fin.addCases (fun z' => ?_) (fun z' => ?_) z
    · rw [J_map_coord, cellCoord_frontHom_castAdd, Fin.addCases_left]
    · rw [J_map_coord, cellCoord_frontHom_natAdd, Fin.addCases_right]

/-- …and along the back leg. -/
theorem coord_backHom_comp {p q n : ℕ} (c : SHom (p + q) n) (k : Fin n) :
    (J.map (backHom p q) ≫ c : ▪q ⟶ ▪n).coord k
      = (c.coord k).elim Sum.inl fun i =>
          Fin.addCases (fun _ => Sum.inl true) (fun j' => Sum.inr j') i := by
  rw [SBox.comp_coord]
  rcases hc : c.coord k with b | i
  · rfl
  · refine congrArg (fun t => (Sum.inr i : Bool ⊕ Fin (p + q)).elim Sum.inl t) (funext fun z => ?_)
    refine Fin.addCases (fun z' => ?_) (fun z' => ?_) z
    · rw [J_map_coord, cellCoord_backHom_castAdd, Fin.addCases_left]
    · rw [J_map_coord, cellCoord_backHom_natAdd, Fin.addCases_right]

/-- **A symmetric cube map out of `▪(p+q)` is a composable pair**: `▪(p+q)` is the wedge
`▪p ∨ ▪q`. -/
theorem sbox_existsUnique {p q n : ℕ} (f : SHom p n) (g : SHom q n)
    (h : (J.map (PrecubicalSet.finalVertexMap p) ≫ f : ▪0 ⟶ ▪n)
      = (J.map (PrecubicalSet.initVertexMap q) ≫ g)) :
    ∃! c : SHom (p + q) n, (J.map (frontHom p q) ≫ c : ▪p ⟶ ▪n) = f
      ∧ (J.map (backHom p q) ≫ c : ▪q ⟶ ▪n) = g := by
  refine ⟨SHom.merge f g h, ⟨SHom.ext (funext fun k => ?_), SHom.ext (funext fun k => ?_)⟩,
    fun c hc => SHom.ext (funext fun k => ?_)⟩
  · rw [coord_frontHom_comp]
    rcases hf : f.coord k with b | i
    · rcases hg : g.coord k with b' | j
      · rw [SHom.coord_merge_sign f g h hf hg, Sum.elim_inl]
      · rw [SHom.coord_merge_right f g h hg, Sum.elim_inr, Fin.addCases_right]
        exact (SHom.coord_left_of_right h hg).symm.trans hf
    · rw [SHom.coord_merge_left f g h hf, Sum.elim_inr, Fin.addCases_left]
  · rw [coord_backHom_comp]
    rcases hf : f.coord k with b | i
    · rcases hg : g.coord k with b' | j
      · rw [SHom.coord_merge_sign f g h hf hg, Sum.elim_inl]
        exact congrArg Sum.inl (SHom.coord_sign_eq h hf hg)
      · rw [SHom.coord_merge_right f g h hg, Sum.elim_inr, Fin.addCases_right]
    · rw [SHom.coord_merge_left f g h hf, Sum.elim_inr, Fin.addCases_left]
      exact (SHom.coord_right_of_left h hf).symm
  · have hcf : (J.map (frontHom p q) ≫ c : ▪p ⟶ ▪n) = f := hc.1
    have hcg : (J.map (backHom p q) ≫ c : ▪q ⟶ ▪n) = g := hc.2
    have hf : f.coord k = (c.coord k).elim Sum.inl fun i =>
        Fin.addCases (fun i' => Sum.inr i') (fun _ => Sum.inl false) i := by
      rw [← hcf]; exact coord_frontHom_comp c k
    have hg : g.coord k = (c.coord k).elim Sum.inl fun i =>
        Fin.addCases (fun _ => Sum.inl true) (fun j' => Sum.inr j') i := by
      rw [← hcg]; exact coord_backHom_comp c k
    rcases hck : c.coord k with b | i
    · rw [hck, Sum.elim_inl] at hf hg
      exact (SHom.coord_merge_sign f g h hf hg).symm
    · rw [hck, Sum.elim_inr] at hf hg
      clear hck hcf hcg hc
      revert hf hg
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
      · intro _ hf
        rw [Fin.addCases_left] at hf
        exact (SHom.coord_merge_left f g h hf).symm
      · intro hg _
        rw [Fin.addCases_right] at hg
        exact (SHom.coord_merge_right f g h hg).symm

/-- **The Segal condition for the representable `y(▪n)` restricted along `J`.** -/
theorem isSegal_symYoneda (n : ℕ) : IsSegal (symYoneda.obj ▪n) :=
  (isSegal_iff_existsUnique _).mpr fun _ _ f g hfg => sbox_existsUnique f g hfg

/-- **`H K` is Segal as soon as `K`'s symmetrization is representable** — the general form: what
the cube supplies is a *single* symmetric cell whose faces are all its traversals. -/
theorem isSegal_H_of_symFree_repr {K : PrecubicalSet} {n : ℕ}
    (e : symFree.obj K ≅ yoneda.obj ▪n) : IsSegal (H.obj K) :=
  isSegal_of_iso (symRestrict.mapIso e).symm (isSegal_symYoneda n)

/-- **`H(□ⁿ)` is Segal**: `H` gives the cube one filler for each traversal. -/
theorem isSegal_H_cube (n : ℕ) : IsSegal (H.obj (□n).toPsh) :=
  isSegal_H_of_symFree_repr (symFreeCube n)

/-! ### Too many cells: the decorated point

An edge carries no order and a square carries two, so `H Z` fails *injectivity* — the opposite
failure to `□²`, whose surjectivity is what breaks.  `H` supplies the orders; the cube supplies the
axes to order. -/

instance subsingleton_HZ_edge : Subsingleton ((H.obj Z).cells 1) :=
  ⟨fun _ _ => Prod.ext (Equiv.ext fun _ => Subsingleton.elim (α := Fin 1) _ _)
    (Subsingleton.elim (α := PUnit) _ _)⟩

/-- **The square of the decorated point carries two orders.** -/
theorem cells_two_H_Z_ne :
    (((1 : Equiv.Perm (Fin (1 + 1))), PUnit.unit) : (H.obj Z).cells (1 + 1))
      ≠ ((Equiv.swap (0 : Fin (1 + 1)) (1 : Fin (1 + 1)), PUnit.unit) : (H.obj Z).cells (1 + 1)) := fun hc => by
  have h1 : (1 : Equiv.Perm (Fin (1 + 1))) = Equiv.swap (0 : Fin (1 + 1)) (1 : Fin (1 + 1)) :=
    congrArg Prod.fst hc
  revert h1
  decide

/-- **Every composable pair of edges of the decorated point is filled** — surjectivity is free. -/
theorem surjective_faceComparison_H_Z :
    Function.Surjective (faceComparison (H.obj Z) 1 1) :=
  fun _ => ⟨(1, PUnit.unit), Subsingleton.elim _ _⟩

/-- **The decorated point has too many cells**: two orders on the square against one on its
edges. -/
theorem not_injective_faceComparison_H_Z :
    ¬ Function.Injective (faceComparison (H.obj Z) 1 1) := fun hinj =>
  cells_two_H_Z_ne (hinj (Subsingleton.elim _ _))

theorem not_isSegal_H_Z : ¬ IsSegal (H.obj Z) := fun h =>
  not_injective_faceComparison_H_Z
    ((isSegal_iff_bijective_faceComparison _).mp h 1 1).1

end CubeChains

