import CubeChains.Precubical.Chains.ChainRestrictions
import CubeChains.Machinery.Cube.Reversal

/-!
# Precubical/Chains/Reversal — running a chain backwards

The cubes in reverse order, each one flipped by `Box.rev`.  It is a natural endomorphism
`revChainPsh` of `chainPresheaf`, because `restrictCoord` reads a face only through the directions
it uses and never through its `ε`s — so the same cubes are dropped and the survivors are flipped.

On a chain cutting a bead into `k` pieces it acts by the longest element of `Sₖ`, which is why it
carries the merge out of a run to the greatest crossing onto the same chain.
-/

open CategoryTheory Opposite BPSet StdCube

namespace CubeChains

variable {n b : ℕ}

/-! ### One cube -/

/-- A cube of `□n`, run backwards: flip every fixed sign. -/
def revCube (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : Σ d : ℕ+, (□n).cells (d : ℕ) :=
  ⟨c.1, Box.rev.map c.2⟩

@[simp] theorem revCube_fst (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : (revCube c).1 = c.1 := rfl

@[simp] theorem revCube_revCube (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : revCube (revCube c) = c :=
  congrArg (Sigma.mk c.1) (Box.rev_rev_map c.2)

/-- `Box.sign_rev` at the spelling a *cell* of `□n` carries.  `(□n).cells m` is the hom-type only up
to unfolding, and `rw` will not reach through it. -/
theorem sign_rev_cell {m : ℕ} (c : (□n).cells m) :
    Box.sign (Box.rev.map c) = flipCell (Box.sign c) := Box.sign_rev c

/-- **Reversal negates an extremal vertex inclusion** — `endVertexMap ε` is a constant sign
vector, and flipping a constant negates it.  Everything else about reversal and endpoints is
this, whiskered (`vertexEnd` on a representable *is* precomposition, `vertexEnd_cube`). -/
@[simp] theorem rev_endVertexMap (ε : Bool) (m : ℕ) :
    Box.rev.map (PrecubicalSet.endVertexMap ε m) = PrecubicalSet.endVertexMap (!ε) m :=
  (Box.rev_ofSign _).trans (congrArg Box.ofSign (flipCell_constVertex m ε))

/-- **Reversal exchanges a cube's two extremal vertices.** -/
theorem vertexEnd_rev (ε : Bool) {m : ℕ} (c : (□n).cells m) :
    (□n).toPsh.vertexEnd ε (Box.rev.map c) = Box.rev.map ((□n).toPsh.vertexEnd (!ε) c) := by
  rw [vertexEnd_cube, vertexEnd_cube, Box.rev.map_comp, rev_endVertexMap, Bool.not_not]
  rfl

@[simp] theorem rev_cube_init (n : ℕ) : Box.rev.map ((□n).init) = (□n).final :=
  rev_endVertexMap false n

@[simp] theorem rev_cube_final (n : ℕ) : Box.rev.map ((□n).final) = (□n).init :=
  rev_endVertexMap true n

/-! ### One cube list -/

/-- A cube list, run backwards. -/
def revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  (cubes.map revCube).reverse

@[simp] theorem revCubes_revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    revCubes (revCubes cubes) = cubes := by
  simp [revCubes, List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem revCubes_dims (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    (revCubes cubes).map (·.1) = (cubes.map (·.1)).reverse := by
  simp [revCubes, List.map_reverse, List.map_map, Function.comp_def]

/-- Reversal exchanges the endpoints, because it exchanges each cube's two extremal vertices. -/
theorem isCubeChain_revCubes {u v : (□n).cells 0} :
    ∀ cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ)), IsCubeChain u cubes v →
      IsCubeChain (Box.rev.map v) (revCubes cubes) (Box.rev.map u)
  | [], h => congrArg Box.rev.map h.symm
  | ⟨m, c⟩ :: rest, h => by
      rw [show revCubes ((⟨m, c⟩ : Σ d : ℕ+, (□n).cells (d : ℕ)) :: rest)
            = revCubes rest ++ [revCube ⟨m, c⟩] by simp [revCubes]]
      exact IsCubeChain.append (isCubeChain_revCubes rest h.2)
        ⟨vertexEnd_rev false c, (vertexEnd_rev true c).trans (congrArg Box.rev.map h.1)⟩

/-- **A cube chain, run backwards.** -/
def revCubeChain (C : CubeChain (□n)) : CubeChain (□n) :=
  CubeChain.ofIsCubeChain (revCubes C.cubes) (by
    have h := isCubeChain_revCubes C.cubes (isCubeChain C)
    rwa [rev_cube_final, rev_cube_init] at h)

@[simp] theorem revCubeChain_cubes (C : CubeChain (□n)) :
    (revCubeChain C).cubes = revCubes C.cubes := rfl

@[simp] theorem revCubeChain_dims (C : CubeChain (□n)) :
    (revCubeChain C).dims = C.dims.reverse := revCubes_dims C.cubes

@[simp] theorem revCubeChain_revCubeChain (C : CubeChain (□n)) :
    revCubeChain (revCubeChain C) = C :=
  CubeChain.eq_of_cubes (revCubes_revCubes C.cubes)

/-! ### Reversal is natural for restriction

`restrictCoord` reads `face` only through the directions it uses, never through its `ε`s, so
flipping the signs commutes with it; and `noneSet` is flip-invariant, so the same cubes are
dropped. -/

theorem restrictCoord_flipCell (face : ▫n ⟶ ▫b) {k : ℕ} (s : Cell b k) :
    restrictCoord face (flipCell s) = flipFun (restrictCoord face s) := rfl

theorem cubeOfCoord_flipFun (u : Fin n → Option Bool) :
    cubeOfCoord (flipFun u) = (cubeOfCoord u).map revCube := by
  have hcard : (noneSet (flipFun u)).card = (noneSet u).card :=
    congrArg Finset.card (noneSet_flipFun u)
  by_cases h : 0 < (noneSet u).card
  · have h' : 0 < (noneSet (flipFun u)).card := by rwa [hcard]
    rw [cubeOfCoord_pos h', cubeOfCoord_pos h, Option.map_some]
    refine congrArg some (Sigma.ext (PNat.coe_injective hcard) ?_)
    change HEq (Box.ofSign (⟨flipFun u, rfl⟩ : Cell n _))
      (Box.rev.map (Box.ofSign (⟨u, rfl⟩ : Cell n _)))
    rw [Box.rev_ofSign]
    exact GeoTensor.ofSign_heq hcard (GeoTensor.cell_heq_of_val rfl)
  · have h' : ¬ 0 < (noneSet (flipFun u)).card := by rwa [hcard]
    rw [cubeOfCoord_neg h', cubeOfCoord_neg h, Option.map_none]

theorem restrictCube_revCube (face : ▫n ⟶ ▫b) (c : Σ d : ℕ+, (□b).cells (d : ℕ)) :
    restrictCube face (revCube c) = (restrictCube face c).map revCube := by
  rw [restrictCube_eq, restrictCube_eq,
    show Box.sign (revCube c).2 = flipCell (Box.sign c.2) from Box.sign_rev c.2]
  exact (congrArg cubeOfCoord (restrictCoord_flipCell face (Box.sign c.2))).trans
    (cubeOfCoord_flipFun _)

theorem restrictChain_revCubes (face : ▫n ⟶ ▫b)
    (cubes : List (Σ d : ℕ+, (□b).cells (d : ℕ))) :
    restrictChain face (revCubes cubes) = revCubes (restrictChain face cubes) := by
  have h : restrictCube face ∘ revCube = fun c => (restrictCube face c).map revCube :=
    funext fun c => restrictCube_revCube face c
  rw [revCubes, revCubes, restrictChain, restrictChain, List.filterMap_reverse,
    List.filterMap_map, List.map_filterMap, h]

theorem restrictCubeChain_revCubeChain (face : ▫n ⟶ ▫b) (C : CubeChain (□b)) :
    restrictCubeChain face (revCubeChain C) = revCubeChain (restrictCubeChain face C) :=
  CubeChain.eq_of_cubes (restrictChain_revCubes face C.cubes)

/-- **Reversal is a natural endomorphism of the chain presheaf**: a chain of any cube runs
backwards, compatibly with restriction along every face. -/
def revChainPsh : chainPresheaf ⟶ chainPresheaf where
  app _ := TypeCat.ofHom revCubeChain
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro C
    exact (restrictCubeChain_revCubeChain f.unop C).symm

@[simp] theorem revChainPsh_app_apply (o : Boxᵒᵖ) (C : CubeChain (□o.unop.dim)) :
    revChainPsh.app o C = revCubeChain C := rfl

/-- **Reversal is an involution of the chain presheaf.** -/
@[simp] theorem revChainPsh_revChainPsh : revChainPsh ≫ revChainPsh = 𝟙 chainPresheaf := by
  apply NatTrans.ext_apply
  intro B C
  exact revCubeChain_revCubeChain C

/-! ### Which chains reversal fixes

A cube pins the coordinates it does not free and drives the ones it frees from `0` to `1`, so a
coordinate freed once is pinned to `1` in every later cube.  Reversal makes the first and last cube
free the same coordinates, which for two or more cubes is impossible. -/

/-- An extremal vertex of a cell, coordinate by coordinate: free coordinates take the extreme value,
fixed ones keep theirs. -/
theorem sign_vertexEnd_val (ε : Bool) {m : ℕ} (c : (□n).cells m) (j : Fin n) :
    (Box.sign ((□n).toPsh.vertexEnd ε c)).val j
      = if (Box.sign c).val j = none then some ε else (Box.sign c).val j := by
  rw [sign_vertexEnd, subst_val]
  by_cases h : (Box.sign c).val j = none
  · rw [substFun_of_none _ _ h, if_pos h]; rfl
  · rw [substFun_of_some _ _ h, if_neg h]

/-- A coordinate already at `1` is pinned there: the cube cannot free it, and carries it on. -/
private theorem pinned_step {m : ℕ} (c : (□n).cells m) {j : Fin n}
    (h : (Box.sign ((□n).toPsh.vertexEnd false c)).val j = some true) :
    (Box.sign c).val j ≠ none ∧
      (Box.sign ((□n).toPsh.vertexEnd true c)).val j = some true := by
  rw [sign_vertexEnd_val] at h
  by_cases hc : (Box.sign c).val j = none
  · rw [if_pos hc] at h; exact absurd h (by simp)
  · rw [if_neg hc] at h
    exact ⟨hc, by rw [sign_vertexEnd_val, if_neg hc, h]⟩

@[inherit_doc pinned_step]
private theorem pinned_chain {u v : (□n).cells 0} :
    ∀ (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))), IsCubeChain u cubes v →
      ∀ j : Fin n, (Box.sign u).val j = some true →
        (∀ e ∈ cubes, (Box.sign e.2).val j ≠ none) ∧ (Box.sign v).val j = some true
  | [], h, _, hu => ⟨by simp, h ▸ hu⟩
  | ⟨_, c⟩ :: rest, h, j, hu => by
      obtain ⟨hne, hhi⟩ := pinned_step c (by rw [h.1]; exact hu)
      obtain ⟨hrest, hv⟩ := pinned_chain rest h.2 j hhi
      exact ⟨List.forall_mem_cons.mpr ⟨hne, hrest⟩, hv⟩

/-- **A chain fixed by reversal has at most one cube**: its first and last cube would free the same
coordinates, and a coordinate freed once is pinned to `1` thereafter. -/
theorem length_le_one_of_revCubeChain_eq {C : CubeChain (□n)} (h : revCubeChain C = C) :
    C.cubes.length ≤ 1 := by
  by_contra hlen
  obtain ⟨c, r₀, rest, hc⟩ : ∃ c r₀ rest, C.cubes = c :: r₀ :: rest := by
    match hcc : C.cubes with
    | [] => rw [hcc] at hlen; simp at hlen
    | [_] => rw [hcc] at hlen; simp at hlen
    | c :: r₀ :: rest => exact ⟨c, r₀, rest, rfl⟩
  have hrev : C.cubes = revCubes C.cubes := (congrArg CubeChain.cubes h).symm
  have hlast : (r₀ :: rest).getLast? = some (revCube c) := by
    rw [show (r₀ :: rest).getLast? = C.cubes.getLast? by rw [hc]; simp]
    conv_lhs => rw [hrev]
    rw [revCubes, List.getLast?_reverse, List.head?_map, hc]
    rfl
  obtain ⟨j, hj⟩ : ∃ j, (Box.sign c.2).val j = none := by
    have hpos : 0 < (noneSet (Box.sign c.2).val).card := by
      rw [(Box.sign c.2).prop]; exact c.1.pos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, mem_noneSet.mp hj⟩
  have hchain : IsCubeChain ((□n).toPsh.vertexEnd true c.2) (r₀ :: rest) ((□n).final) := by
    have hC := isCubeChain C
    rw [hc] at hC
    exact hC.2
  have hpin := (pinned_chain _ hchain j (by rw [sign_vertexEnd_val, if_pos hj])).1
    (revCube c) (List.mem_of_getLast? hlast)
  refine hpin ?_
  rw [show (Box.sign (revCube c).2) = flipCell (Box.sign c.2) from sign_rev_cell c.2]
  change ((Box.sign c.2).val j).map not = none
  rw [hj]
  rfl

/-! ### All-edges chains are closed under reversal

Reversal permutes the dimension list (`revCubeChain_dims`), so it preserves "every bead is an
edge" — the subpresheaf of runs is reversal-stable. -/

/-- An all-edges chain, run backwards. -/
def EdgeChain.rev (r : EdgeChain (□n)) : EdgeChain (□n) :=
  ⟨revCubeChain r.1, fun c hc => by
    obtain ⟨c', hc', rfl⟩ := List.exists_of_mem_map (List.mem_reverse.mp hc)
    exact r.2 c' hc'⟩

@[simp] theorem EdgeChain.rev_rev (r : EdgeChain (□n)) : r.rev.rev = r :=
  Subtype.ext (revCubeChain_revCubeChain r.1)

/-- **Reversal commutes with restriction** on all-edges chains. -/
theorem EdgeChain.restrict_rev (face : ▫n ⟶ ▫b) (e : EdgeChain (□b)) :
    EdgeChain.restrict face e.rev = (EdgeChain.restrict face e).rev :=
  Subtype.ext (restrictCubeChain_revCubeChain face e.1)

end CubeChains
