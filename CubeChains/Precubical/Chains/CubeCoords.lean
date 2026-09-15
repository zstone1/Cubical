import CubeChains.Precubical.Chains.Category
import CubeChains.Precubical.Chains.CubeVtx
import CubeChains.Precubical.Wedge.CubeMerge
import Mathlib.Data.Fintype.Inv
import Mathlib.Algebra.BigOperators.Fin

/-!
# Precubical/Chains/CubeCoords — a chain of a cube is a coordinate system

The `⊥`-vertex reading of a chain `χ : ⋁d ⟶ □m` rises along the spine from `0ᵐ` to `1ᵐ`, so every
coordinate is flipped by exactly one bead: `coordFlip χ : beadEvent d ≃ Fin m`, and `m` counts the
events (`wedgeDimSum_eq`).  Bead `i` reads the coordinates of earlier beads as `1` and of later ones
as `0` (`ev_beadFace_eq_blockSign`).  That one potential does the rest: it separates the vertices
of the wedge (`chain_vertex_injective`), pins a wedge map by the chain it induces
(`wedgeHom_ext_chain`), and sends beads monotonically into blocks (`serialWedge_blockIdx_monotone`).
-/

open CategoryTheory Opposite CubeChain ChainCat BPSet StdCube PrecubicalSet

namespace CubeChains

/-! ## The reading of a chain of a cube -/

/-- Bead `i`'s image face in `□m`: `beadCell` at a representable target, read as a `Box` hom. -/
def beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    ▫((a.get i : ℕ)) ⟶ ▫m := beadCell f i

/-- `beadFace` is the Yoneda cell of the bead restriction, in `Box`-hom spelling. -/
theorem yoneda_map_beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) : yoneda.map (beadFace f i) = ιᵂ a i ≫ f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map (beadFace f i))

/-- **A composite restricted to a bead** factors through the block that `φ` puts the bead in —
`blockFace_spec` reassociated. -/
theorem ι_comp_blockFace {a b : List ℕ+} {X : PrecubicalSet} (φ : (⋁a).toPsh ⟶ (⋁b).toPsh)
    (ψ : (⋁b).toPsh ⟶ X) (i : Fin a.length) :
    ιᵂ a i ≫ φ ≫ ψ = yoneda.map (blockFace φ i) ≫ ιᵂ b (blockIdx φ i) ≫ ψ := by
  rw [← Category.assoc, blockFace_spec φ i]
  exact Category.assoc _ _ _

/-- **Bead data composes.**  Bead `i` of `φ ≫ ψ` is bead `blockIdx φ i` of `ψ` restricted along
`φ`'s own block face — `yoneda` faithful. -/
theorem beadFace_comp {a b : List ℕ+} {m : ℕ} (φ : (⋁a).toPsh ⟶ (⋁b).toPsh)
    (ψ : (⋁b).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    beadFace (φ ≫ ψ) i = blockFace φ i ≫ beadFace ψ (blockIdx φ i) :=
  yoneda.map_injective (by
    rw [yoneda_map_beadFace, Functor.map_comp, yoneda_map_beadFace, ι_comp_blockFace]
    rfl)

/-- The **`⊥`-vertex reading** of a cube face.  At `n = 0` a face *is* a vertex and this is cube
Yoneda; above that it is the potential that rises along the spine (`readVec_beadBot_mono`). -/
def readVec {n m : ℕ} (g : ▫n ⟶ ▫m) : Fin m → Bool := cubeVtx g (fun _ => false)

/-- **A vertex of a cube is its reading.** -/
theorem readVec_injective {k : ℕ} : Function.Injective (readVec : (▫0 ⟶ ▫k) → Fin k → Bool) :=
  fun v w h => Box.hom_ext ((vtxEquiv k).injective (funext fun q =>
    (cubeVtx_bot_getD v q).symm.trans ((congrFun h q).trans (cubeVtx_bot_getD w q))))

/-- A cube map acts on a `0`-cell by precomposition with its Yoneda cell (cube Yoneda). -/
theorem cube_app_zero {b m : ℕ} (f : (□b).toPsh ⟶ (□m).toPsh) (x : ▫0 ⟶ ▫b) :
    f⟪0⟫ x = x ≫ yonedaEquiv f := (map_yonedaEquiv f x).symm

/-- Reading a face extended along a `Box` hom is `cubeVtx` of that hom — `cubeVtx_comp` at `⊥`. -/
theorem readVec_vertex_comp {c m n : ℕ} (v : ▫n ⟶ ▫c) (g : ▫c ⟶ ▫m) :
    readVec (v ≫ g) = cubeVtx g (readVec v) :=
  congrArg (fun t : (Fin n → Bool) →o (Fin m → Bool) => t (fun _ => false)) (cubeVtx_comp v g)

/-- Reading a map at a cube-borne `0`-cell factors through `cubeVtx` of the Yoneda cell. -/
theorem readVec_app_zero {b m : ℕ} (f : (□b).toPsh ⟶ (□m).toPsh) (x : ▫0 ⟶ ▫b) :
    readVec (f⟪0⟫ x) = cubeVtx (yonedaEquiv f) (readVec x) := by
  rw [cube_app_zero f x, readVec_vertex_comp]

/-- Reading `f` at bead `i`'s vertices factors through `cubeVtx` of bead `i`'s face. -/
theorem readVec_bead {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length)
    (v : ▫0 ⟶ ▫(a.get i : ℕ)) :
    readVec (f⟪0⟫ ((ιᵂ a i)⟪0⟫ v)) = cubeVtx (beadFace f i) (readVec v) :=
  (congrArg readVec (comp_app_cell (f := ιᵂ a i) (g := f) (h := ιᵂ a i ≫ f) rfl 0 v)).trans
    (readVec_app_zero (ιᵂ a i ≫ f) v)

/-- `readVec` of `□m`'s `ε`-extremal vertex is constant `ε`. -/
theorem readVec_endVertexMap (ε : Bool) (m : ℕ) (q : Fin m) :
    readVec (endVertexMap ε m) q = ε := cubeVtx_bot_getD (endVertexMap ε m) q

/-- A face fixed at `q` reads its fixed value there, whatever vertex it extends. -/
theorem cubeVtx_of_fixed {n m : ℕ} (g : ▫n ⟶ ▫m) (v : Fin n → Bool) {q : Fin m}
    (h : (Box.sign g).val q ≠ none) : cubeVtx g v q = ((Box.sign g).val q).getD false := by
  rw [cubeVtx_eq, cubeVtxOfCell_apply, dif_neg fun hq => h (mem_noneSet.mp hq)]

/-- A coordinate is in the range of a face's `faceEmb` iff the face is free there. -/
theorem mem_range_faceEmb {k m : ℕ} (g : ▫k ⟶ ▫m) (q : Fin m) :
    q ∈ Set.range (faceEmb g) ↔ (Box.sign g).val q = none := by
  unfold faceEmb Box.sign StdCube.nones
  rw [Finset.range_orderEmbOfFin, Finset.mem_coe, StdCube.mem_noneSet]

/-! ### The reading rises along the spine

Across a bead the `⊥`-vertex reading goes from `cubeVtx` of its face at `⊥` to `cubeVtx` at `⊤`,
and `cubeVtx` is monotone; the junctions glue consecutive beads, so reading a coordinate through
`f` cannot go from `true` to `false` as the wedge is traversed. -/

/-- Bead `s`'s `ε`-extremal vertex, as a `0`-cell of `⋁a`: `false` its bottom, `true` its top. -/
def beadEnd (ε : Bool) (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ (endVertexMap ε (a.get s : ℕ))

/-- **The wedge spine's junction**: bead `s`'s top is bead `t = s+1`'s bottom — the gluing of
`□c ∨ ⋁rest`, carried down the tail. -/
theorem junction_eq : ∀ (a : List ℕ+) (s t : Fin a.length), (t : ℕ) = (s : ℕ) + 1 →
    beadEnd true a s = beadEnd false a t
  | [], s, _, _ => s.elim0
  | [_], s, t, h => by
      have ht := t.isLt
      simp only [List.length_cons, List.length_nil] at ht
      omega
  | c :: c' :: rest, s, t, h => by
      induction s using Fin.cases with
      | zero =>
          obtain rfl : t = (0 : Fin (c' :: rest).length).succ := Fin.ext h
          exact wedge2_glue (□(c : ℕ)) (⋁(c' :: rest))
      | succ j =>
          have hj : (j : ℕ) + 1 < (c' :: rest).length := by
            have ht := t.isLt
            simp only [Fin.val_succ, List.length_cons] at h ht ⊢
            omega
          obtain rfl : t = (⟨(j : ℕ) + 1, hj⟩ : Fin (c' :: rest).length).succ :=
            Fin.ext (by simpa using h)
          exact congrArg ((Glue.inr (□(c : ℕ)).finalVertex (⋁(c' :: rest)).initVertex)⟪0⟫)
            (junction_eq (c' :: rest) j _ rfl)

/-- **Across a bead the reading rises**: bottom to top is `cubeVtx` of its face, monotone. -/
theorem readVec_beadEnd_le {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (s : Fin a.length) :
    readVec (f⟪0⟫ (beadEnd false a s)) ≤ readVec (f⟪0⟫ (beadEnd true a s)) := by
  rw [beadEnd, beadEnd, readVec_bead, readVec_bead]
  exact (cubeVtx (beadFace f s)).monotone fun q => by
    rw [readVec_endVertexMap, readVec_endVertexMap]; exact Bool.false_le true

/-- **Along the spine the reading rises**: bead bottoms read in bead order. -/
theorem readVec_beadBot_mono {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    Monotone fun s : Fin a.length => readVec (f⟪0⟫ (beadEnd false a s)) :=
  match a with
  | [] => fun s => s.elim0
  | c :: rest => Fin.monotone_iff_le_succ.mpr fun i => (readVec_beadEnd_le f i.castSucc).trans_eq
      (congrArg (fun v => readVec (f⟪0⟫ v)) (junction_eq (c :: rest) i.castSucc i.succ rfl))

/-- A bead's top reads below every later bead's bottom. -/
theorem readVec_beadTop_le_beadBot {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    {s t : Fin a.length} (h : (s : ℕ) < (t : ℕ)) :
    readVec (f⟪0⟫ (beadEnd true a s)) ≤ readVec (f⟪0⟫ (beadEnd false a t)) := by
  have hs : s.val + 1 < a.length := by have := t.isLt; omega
  rw [junction_eq a s ⟨s.val + 1, hs⟩ rfl]
  exact readVec_beadBot_mono f (Fin.le_def.mpr h)

/-- Bead `i` flips `q` ⟹ `q` reads `ε` at bead `i`'s `ε`-end (its free coords are all `ε`). -/
theorem readVec_beadEnd_flip (ε : Bool) {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) {q : Fin m} (hq : q ∈ Set.range (faceEmb (beadFace f i))) :
    readVec (f⟪0⟫ (beadEnd ε a i)) q = ε := by
  obtain ⟨k, rfl⟩ := hq
  rw [beadEnd, readVec_bead, cubeVtx_faceEmb]
  exact readVec_endVertexMap ε _ k

/-- An earlier and a later bead cannot both flip `q`: `q` is `true` at the earlier bead's top, which
reads below the later one's bottom, where flipping would read `q` as `false`. -/
theorem not_flip_of_fst_lt {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    {i i' : Fin a.length} (hlt : (i : ℕ) < (i' : ℕ)) {q : Fin m}
    (hi : q ∈ Set.range (faceEmb (beadFace f i)))
    (hi' : q ∈ Set.range (faceEmb (beadFace f i'))) : False := by
  have hle := readVec_beadTop_le_beadBot f hlt q
  rw [readVec_beadEnd_flip true f i hi, readVec_beadEnd_flip false f i' hi'] at hle
  exact Bool.noConfusion (le_antisymm hle (Bool.false_le true))

/-- **Cross-bead disjointness.**  Distinct beads flip disjoint coordinates — whichever of the two
comes first has its top reach the other's bottom. -/
theorem coord_beads_disjoint (a : List ℕ+) {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i i' : Fin a.length) (q : Fin m) (hi : q ∈ Set.range (faceEmb (beadFace f i)))
    (hi' : q ∈ Set.range (faceEmb (beadFace f i'))) : i = i' := by
  rcases lt_trichotomy (i : ℕ) (i' : ℕ) with h | h | h
  · exact (not_flip_of_fst_lt f h hi hi').elim
  · exact Fin.ext h
  · exact (not_flip_of_fst_lt f h hi' hi).elim

/-! ## Every coordinate is flipped exactly once

A chain climbs from `0ᵐ` to `1ᵐ`, and a cube fixed at `q` reads `q` alike at both of its ends — so
some cube of the chain is free at `q`, and by disjointness only one. -/

/-- **A chain of cubes that changes the reading at `q` has a cube free at `q`.** -/
theorem exists_free_of_isCubeChain {m : ℕ} (q : Fin m) :
    ∀ (cubes : List (Σ n : ℕ+, (□m).cells (n : ℕ))) {p r : (□m).cells 0},
      IsCubeChain p cubes r → readVec p q = false → readVec r q = true →
      ∃ c ∈ cubes, (Box.sign c.2).val q = none
  | [], p, r, h, hp, hr => by
      change p = r at h
      subst h
      exact absurd (hp.symm.trans hr) Bool.false_ne_true
  | ⟨n, c⟩ :: rest, p, r, h, hp, hr => by
      by_cases hc : (Box.sign c).val q = none
      · exact ⟨_, List.mem_cons_self .., hc⟩
      · have hend : ∀ ε, readVec ((□m).toPsh.vertexEnd ε c) q = ((Box.sign c).val q).getD false :=
          fun ε => by rw [vertexEnd_cube, readVec_vertex_comp]; exact cubeVtx_of_fixed c _ hc
        obtain ⟨c', hc', hfree⟩ := exists_free_of_isCubeChain q rest h.2
          ((hend true).trans ((hend false).symm.trans (h.1 ▸ hp))) hr
        exact ⟨c', List.mem_cons_of_mem _ hc', hfree⟩

/-- **A chain of the cube flips every coordinate.** -/
theorem exists_flip {d : List ℕ+} {m : ℕ} (χ : ⋁d ⟶ □m) (q : Fin m) :
    ∃ i, q ∈ Set.range (faceEmb (beadFace χ.hom i)) := by
  have hchain := beadCell_isCubeChain (K := □m) d χ.hom
  rw [χ.app_init, χ.app_final] at hchain
  obtain ⟨c, hc, hfree⟩ := exists_free_of_isCubeChain q _ hchain
    (readVec_endVertexMap false m q) (readVec_endVertexMap true m q)
  obtain ⟨k, rfl⟩ := List.get_of_mem hc
  rw [Beads.toList_get] at hfree
  exact ⟨_, (mem_range_faceEmb _ q).mpr hfree⟩

/-- **Every coordinate is flipped by exactly one bead** — injective by disjointness, surjective
because the chain climbs. -/
theorem coord_sigma_bijective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Bijective (fun p : beadEvent a => faceEmb (beadFace χ.hom p.1) p.2) :=
  ⟨fun ⟨i, k⟩ ⟨i', k'⟩ hp => by
    obtain rfl : i = i' := coord_beads_disjoint a χ.hom i i' _ ⟨k, rfl⟩ ⟨k', hp.symm⟩
    obtain rfl : k = k' := (faceEmb (beadFace χ.hom i)).injective hp
    rfl,
   fun q => let ⟨i, k, hk⟩ := exists_flip χ q; ⟨⟨i, k⟩, hk⟩⟩

/-- **The coordinate bijection** of a bipointed wedge map into a cube: `⟨i,k⟩ ↦` the coordinate of
`□m` that bead `i` flips — computable, its inverse a `Fintype.bijInv`. -/
def coordFlip {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) : beadEvent a ≃ Fin m where
  toFun p := faceEmb (beadFace χ.hom p.1) p.2
  invFun := Fintype.bijInv (coord_sigma_bijective χ)
  left_inv := Fintype.leftInverse_bijInv (coord_sigma_bijective χ)
  right_inv := Fintype.rightInverse_bijInv (coord_sigma_bijective χ)

/-- **Escape hatch to the concrete machinery**: `coordFlip χ ⟨i,k⟩` is the coordinate of `□m` that
bead `i` flips — `faceEmb` of bead `i`'s face at `k`. -/
@[simp] theorem coordFlip_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) (p : beadEvent a) :
    coordFlip χ p = faceEmb (beadFace χ.hom p.1) p.2 := rfl

/-- `dimSum` in the `Fin`-indexed shape a count of events produces. -/
theorem dimSum_eq_sum_get (a : List ℕ+) : ∑ i : Fin a.length, (a.get i : ℕ) = dimSum a :=
  (List.sum_map_eq_sum_get a (fun d : ℕ+ => (d : ℕ))).symm.trans (dimSum_sum a).symm

/-- **A chain of `□m` has `m` events** — `coordFlip` counts them. -/
theorem wedgeDimSum_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) : dimSum a = m := by
  simpa only [Fintype.card_sigma, Fintype.card_fin, dimSum_eq_sum_get] using
    Fintype.card_congr (coordFlip χ)

end CubeChains

/-- **A map of serial wedges keeps the event count**: read in the cube the target merges into,
both are chains of it. -/
theorem CubeChain.serialWedge_dimSum_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    BPSet.dimSum ad = BPSet.dimSum cd :=
  (CubeChains.nonempty_toCube cd).elim fun χ => CubeChains.wedgeDimSum_eq (φ ≫ χ)

namespace CubeChains

variable {n : ℕ}

/-! ## The ordered partition of a chain -/

/-- The **bead** a coordinate is flipped by — the first component of `coordFlip`'s inverse. -/
def beadOf (b : Ch (□n)) (q : Fin n) : Fin b.dims.length :=
  ((coordFlip b.map).symm q).1

@[simp]
theorem beadOf_eq (b : Ch (□n)) (q : Fin n) : beadOf b q = ((coordFlip b.map).symm q).1 := rfl

/-- **Geometric view of `beadOf`**: `q`'s bead is `i` iff `i`'s face is free at `q`. -/
theorem mem_range_iff_beadOf (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    q ∈ Set.range (faceEmb (beadFace b.map.hom i)) ↔ beadOf b q = i := by
  rw [beadOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    rw [← coordFlip_eq b.map ⟨i, k⟩] at hk
    rw [← hk, Equiv.symm_apply_apply]
  · rintro rfl
    exact ⟨((coordFlip b.map).symm q).2,
      (coordFlip_eq b.map ((coordFlip b.map).symm q)).symm.trans (Equiv.apply_symm_apply _ q)⟩

/-- **Sign-vector view of `beadOf`**: `i`'s face is free at `q` iff `q`'s bead is `i`. -/
theorem ev_beadFace_eq_none_iff (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    (Box.sign (beadFace b.map.hom i)).val q = none ↔ beadOf b q = i :=
  (mem_range_faceEmb (beadFace b.map.hom i) q).symm.trans (mem_range_iff_beadOf b i q)

/-- `beadOf b` is surjective: bead `i` flips its own `0`-th coordinate. -/
theorem beadOf_surjective (b : Ch (□n)) : Function.Surjective (beadOf b) := fun i =>
  ⟨coordFlip b.map ⟨i, ⟨0, (b.dims.get i).2⟩⟩, by rw [beadOf_eq, Equiv.symm_apply_apply]⟩

variable {L : ℕ}

/-- Bead `j`'s sign vector: free (`none`) on `β⁻¹{j}`, `1` below, `0` above. -/
def blockSign (β : Fin n → Fin L) (j : Fin L) : Fin n → Option Bool :=
  fun q => if β q = j then none else some (decide ((β q : ℕ) < (j : ℕ)))

/-- **The master lemma.**  Bead `i`'s face reads, at `q`, `none` iff `q` is in bead `i`, else
`1`/`0` by whether `q`'s bead precedes `i` — the reading of bead `i`'s bottom, pinned along the
spine. -/
theorem ev_beadFace_eq_blockSign (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    (Box.sign (beadFace b.map.hom i)).val q = blockSign (beadOf b) i q := by
  simp only [blockSign]
  by_cases h : beadOf b q = i
  · rw [if_pos h]
    exact (ev_beadFace_eq_none_iff b i q).mpr h
  · rw [if_neg h]
    have hne : (Box.sign (beadFace b.map.hom i)).val q ≠ none := fun hnone =>
      h ((ev_beadFace_eq_none_iff b i q).mp hnone)
    obtain ⟨ε, hε⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hε]
    have hqflip₀ : q ∈ Set.range (faceEmb (beadFace b.map.hom (beadOf b q))) :=
      (mem_range_iff_beadOf b (beadOf b q) q).mpr rfl
    have hεval : readVec (b.map.hom⟪0⟫ (beadEnd false b.dims i)) q = ε := by
      rw [beadEnd, readVec_bead, cubeVtx_of_fixed _ _ hne, hε]
      rfl
    congr 1
    rcases lt_trichotomy (beadOf b q : ℕ) (i : ℕ) with hlt | heq | hgt
    · have htop : readVec (b.map.hom⟪0⟫ (beadEnd true b.dims (beadOf b q))) q = true :=
        readVec_beadEnd_flip true b.map.hom (beadOf b q) hqflip₀
      have hmono := readVec_beadTop_le_beadBot b.map.hom hlt q
      rw [htop, hεval] at hmono
      rw [le_antisymm (Bool.le_true ε) hmono]
      exact (decide_eq_true hlt).symm
    · exact absurd (Fin.val_injective heq) h
    · have hbot : readVec (b.map.hom⟪0⟫ (beadEnd false b.dims (beadOf b q))) q = false :=
        readVec_beadEnd_flip false b.map.hom (beadOf b q) hqflip₀
      have hmono : readVec (b.map.hom⟪0⟫ (beadEnd false b.dims i)) q
          ≤ readVec (b.map.hom⟪0⟫ (beadEnd false b.dims (beadOf b q))) q :=
        readVec_beadBot_mono b.map.hom (Fin.le_def.mpr (le_of_lt hgt)) q
      rw [hbot, hεval] at hmono
      rw [le_antisymm hmono (Bool.false_le ε)]
      exact (decide_eq_false (by omega)).symm

/-! ## The reading separates the vertices of the wedge -/

/-- **A vertex of bead `s` reads `1` on earlier beads and `0` on later ones.** -/
theorem readVec_bead_of_ne (b : Ch (□n)) (s : Fin b.dims.length) (v : ▫0 ⟶ ▫(b.dims.get s : ℕ))
    {q : Fin n} (h : beadOf b q ≠ s) :
    readVec (b.map.hom⟪0⟫ ((ιᵂ b.dims s)⟪0⟫ v)) q = decide ((beadOf b q : ℕ) < s) := by
  rw [readVec_bead, cubeVtx_of_fixed _ _ fun hq => h ((ev_beadFace_eq_none_iff b s q).mp hq),
    ev_beadFace_eq_blockSign, blockSign, if_neg h]
  rfl

/-- …and on its own bead it reads the vertex. -/
theorem readVec_bead_faceEmb (b : Ch (□n)) (s : Fin b.dims.length)
    (v : ▫0 ⟶ ▫(b.dims.get s : ℕ)) (k : Fin (b.dims.get s : ℕ)) :
    readVec (b.map.hom⟪0⟫ ((ιᵂ b.dims s)⟪0⟫ v)) (faceEmb (beadFace b.map.hom s) k)
      = readVec v k := by
  rw [readVec_bead, cubeVtx_faceEmb]

/-- **Every vertex of a nonempty serial wedge lies in a bead.** -/
theorem exists_bead_vertex : ∀ {d : List ℕ+}, d ≠ [] → ∀ x : (⋁d).cells 0,
    ∃ (s : Fin d.length) (v : ▫0 ⟶ ▫(d.get s : ℕ)), (ιᵂ d s)⟪0⟫ v = x
  | [], hd, _ => absurd rfl hd
  | n :: rest, _, x => by
      rcases glue0_cell_cases (□(n : ℕ)).finalVertex (⋁rest).initVertex 0 x with ⟨v, hv⟩ | ⟨y, hy⟩
      · exact ⟨0, v, hv⟩
      · cases rest with
        | nil =>
            refine ⟨0, (□(n : ℕ)).final, ?_⟩
            rw [← hy, Subsingleton.elim (α := ▫0 ⟶ ▫0) y (⋁([] : List ℕ+)).init]
            exact wedge2_glue (□(n : ℕ)) (⋁[])
        | cons c rest' =>
            obtain ⟨s, v, hv⟩ := exists_bead_vertex (List.cons_ne_nil c rest') y
            exact ⟨s.succ, v, by rw [serialWedge_ι_succ_app, hv, hy]⟩

/-- Two vertices of beads `s ≤ t` reading alike are one vertex: the junction, if `s < t`. -/
private theorem bead_vertex_eq (b : Ch (□n)) {s t : Fin b.dims.length} (hst : s ≤ t)
    (v : ▫0 ⟶ ▫(b.dims.get s : ℕ)) (w : ▫0 ⟶ ▫(b.dims.get t : ℕ))
    (h : readVec (b.map.hom⟪0⟫ ((ιᵂ b.dims s)⟪0⟫ v))
      = readVec (b.map.hom⟪0⟫ ((ιᵂ b.dims t)⟪0⟫ w))) :
    (ιᵂ b.dims s)⟪0⟫ v = (ιᵂ b.dims t)⟪0⟫ w := by
  have hbead : ∀ (u : Fin b.dims.length) (k : Fin (b.dims.get u : ℕ)),
      beadOf b (faceEmb (beadFace b.map.hom u) k) = u :=
    fun u k => (mem_range_iff_beadOf b u _).mp ⟨k, rfl⟩
  rcases eq_or_lt_of_le hst with rfl | hlt
  · refine congrArg _ (readVec_injective (funext fun k => ?_))
    have hk := congrFun h (faceEmb (beadFace b.map.hom s) k)
    rwa [readVec_bead_faceEmb, readVec_bead_faceEmb] at hk
  have hv : v = endVertexMap true _ := readVec_injective (funext fun k => by
    have hk := congrFun h (faceEmb (beadFace b.map.hom s) k)
    rw [readVec_bead_faceEmb, readVec_bead_of_ne b t w (by rw [hbead]; exact ne_of_lt hlt),
      hbead] at hk
    rw [hk, readVec_endVertexMap]
    exact decide_eq_true (Fin.lt_def.mp hlt))
  have hw : w = endVertexMap false _ := readVec_injective (funext fun k => by
    have hk := congrFun h (faceEmb (beadFace b.map.hom t) k)
    rw [readVec_bead_faceEmb, readVec_bead_of_ne b s v (by rw [hbead]; exact ne_of_gt hlt),
      hbead] at hk
    rw [← hk, readVec_endVertexMap]
    exact decide_eq_false (not_lt.mpr (Fin.le_def.mp hst)))
  have hadj : (t : ℕ) = (s : ℕ) + 1 := by
    by_contra hne
    have hu : (s : ℕ) + 1 < b.dims.length := by have := t.isLt; omega
    set u : Fin b.dims.length := ⟨(s : ℕ) + 1, hu⟩
    have hq := congrFun h (faceEmb (beadFace b.map.hom u) ⟨0, (b.dims.get u).pos⟩)
    rw [readVec_bead_of_ne b s v (by rw [hbead]; exact fun he => by simp [u, Fin.ext_iff] at he),
      readVec_bead_of_ne b t w (by rw [hbead]; exact fun he => hne (by rw [← he])), hbead] at hq
    have h1 : ¬ ((u : ℕ) < s) := by simp [u]
    have h2 : (u : ℕ) < t := by simp only [u]; have := Fin.lt_def.mp hlt; omega
    simp [h1, h2] at hq
  rw [hv, hw]
  exact junction_eq b.dims s t hadj

/-- **A chain of the cube is injective on vertices** — a vertex of bead `s` reads `1` below `s` and
`0` above it, so two beads' vertices meet only at the junction between them. -/
theorem chain_vertex_injective (b : Ch (□n)) : Function.Injective (b.map.hom⟪0⟫) := by
  intro x y hxy
  obtain ⟨d, χ⟩ := b
  cases d with
  | nil => exact Subsingleton.elim (α := ▫0 ⟶ ▫0) x y
  | cons c rest =>
      obtain ⟨s, v, rfl⟩ := exists_bead_vertex (List.cons_ne_nil c rest) x
      obtain ⟨t, w, rfl⟩ := exists_bead_vertex (List.cons_ne_nil c rest) y
      rcases le_total s t with hst | hts
      · exact bead_vertex_eq ⟨_, χ⟩ hst v w (congrArg readVec hxy)
      · exact (bead_vertex_eq ⟨_, χ⟩ hts w v (congrArg readVec hxy.symm)).symm

end CubeChains

namespace CubeChains

open CubeChains

/-! ## A wedge map, read in a chain of its target

`φ : ⋁a ⟶ ⋁b` followed by a chain `χ` of `□N` is a chain on `a`'s shape, whose beads are `φ`'s
block faces followed by `χ`'s beads (`beadFace_comp`).  So the chain pins `φ` bead by bead, and the
reading orders its blocks. -/

/-- **A wedge map is pinned by the chain it induces** — each bead lands in the bead of the chain
that flips its coordinates, as a face that `Box` cancels. -/
theorem wedgeHom_ext_chain {a b : List ℕ+} {N : ℕ} {χ : ⋁b ⟶ □N} {φ ψ : ⋁a ⟶ ⋁b}
    (h : φ ≫ χ = ψ ≫ χ) : φ = ψ := by
  have key : ∀ {k : ℕ} (hk : 0 < k) {j j' : Fin b.length} (g : ▫k ⟶ ▫(b.get j : ℕ))
      (g' : ▫k ⟶ ▫(b.get j' : ℕ)) (_ : g ≫ beadFace χ.hom j = g' ≫ beadFace χ.hom j'),
      yoneda.map g ≫ ιᵂ b j = yoneda.map g' ≫ ιᵂ b j' := by
    intro k hk j j' g g' hgg
    obtain rfl : j = j' := coord_beads_disjoint b χ.hom j j' _
      ⟨faceEmb g ⟨0, hk⟩, (faceEmb_comp g _ _).symm⟩
      ⟨faceEmb g' ⟨0, hk⟩, (faceEmb_comp g' _ _).symm.trans (by rw [hgg])⟩
    rw [(cancel_mono (beadFace χ.hom j)).mp hgg]
  refine bpset_hom_ext_of_beadCell fun i => congrArg yonedaEquiv ?_
  refine (blockFace_spec φ.hom i).trans ((key (a.get i).pos _ _ ?_).trans
    (blockFace_spec ψ.hom i).symm)
  rw [← beadFace_comp, ← beadFace_comp]
  exact congrArg (fun t : ⋁a ⟶ □N => beadFace t.hom i) h

/-- **A wedge map sends beads monotonically into blocks** — in a chain of the target, an earlier
bead's coordinates read `1` on a later bead, while a later block would read them `0`. -/
theorem _root_.CubeChain.serialWedge_blockIdx_monotone {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    Monotone (blockIdx φ.hom) := by
  obtain ⟨χ⟩ := nonempty_toCube b
  intro i i' hii'
  by_contra hlt
  rw [not_le] at hlt
  have hne : (i : ℕ) < i' := lt_of_le_of_ne (Fin.le_def.mp hii') fun he =>
    lt_irrefl _ ((congrArg (blockIdx φ.hom) (Fin.ext he)) ▸ hlt)
  let A : Ch (□(dimSum b)) := ⟨a, φ ≫ χ⟩
  let B : Ch (□(dimSum b)) := ⟨b, χ⟩
  have hcomp : ∀ u, beadFace A.map.hom u = blockFace φ.hom u ≫ beadFace χ.hom (blockIdx φ.hom u) :=
    fun u => beadFace_comp φ.hom χ.hom u
  let q := faceEmb (beadFace A.map.hom i) ⟨0, (a.get i).pos⟩
  have hA : beadOf A q = i := (mem_range_iff_beadOf A i q).mp ⟨_, rfl⟩
  have hB : beadOf B q = blockIdx φ.hom i := (mem_range_iff_beadOf B _ q).mp
    ⟨faceEmb (blockFace φ.hom i) ⟨0, (a.get i).pos⟩, by rw [← faceEmb_comp, ← hcomp]⟩
  have hfix : (Box.sign (beadFace χ.hom (blockIdx φ.hom i'))).val q ≠ none := fun hq =>
    (ne_of_gt hlt) (hB.symm.trans ((ev_beadFace_eq_none_iff B _ q).mp hq))
  have key := ev_beadFace_eq_blockSign A i' q
  rw [hcomp, Box.sign_comp, subst_val, substFun_of_some _ _ hfix,
    show (Box.sign (beadFace χ.hom (blockIdx φ.hom i'))).val q = _ from
      ev_beadFace_eq_blockSign B _ q] at key
  simp only [blockSign, hA, hB] at key
  rw [if_neg (ne_of_gt hlt), if_neg (fun he => absurd (congrArg Fin.val he) (ne_of_lt hne))] at key
  simp only [Option.some.injEq, decide_eq_decide] at key
  exact absurd (key.mpr hne) (not_lt.mpr (le_of_lt hlt))

end CubeChains
