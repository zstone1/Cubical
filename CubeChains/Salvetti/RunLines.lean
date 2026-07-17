import CubeChains.Salvetti.Normalize
import CubeChains.Salvetti.ChamberPerm
import CubeChains.Salvetti.SalBraidTope
import CubeChains.Chains.Correspondence
import CubeChains.Chains.SegalSplit
import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.CubeNonSelfLinked

/-!
# Salvetti/RunLines — the run-map representation of `Lines`

A line as a **bi-pointed map out of the all-edges run** (`RunLine a = Runs a.dims`), rather than a
tuple of `Chamber` structures.

GOTCHA: `Lines` must stay **contravariant**. The contravariance is what creates the braid — both
orderings of a square restrict to the *same* run, gluing them; the covariant (post-compose) version
disconnects and kills `π₁`. So `Runs` is re-encoded as a presheaf, object side only.
-/

open CategoryTheory Opposite

namespace CubeChains

/-- The all-edges run `⋁[1,…,1]` (`n` ones): the finest chain shape, `n` edges in series. -/
def run (n : ℕ) : BPSet := ⋁ (List.replicate n (1 : ℕ+))

/-- The total dimension (event count) of a dimension sequence: `Σᵢ dimsᵢ`. -/
def dimSum (dims : List ℕ+) : ℕ := (dims.map (fun d => (d : ℕ))).sum

/-- **The runs of the serial wedge `⋁dims`**: bi-pointed maps from the all-edges run of the right
length — a monotone edge-path threading `dimSum dims` edges through `⋁dims`. -/
def Runs (dims : List ℕ+) : Type := run (dimSum dims) ⟶ ⋁ dims

/-- The proposed line representation of a chain: `Runs` of its serial wedge. -/
def RunLine {K : BPSet} (a : Ch K) : Type := Runs a.dims

/-! ## The fiber equivalence: a run-map is an all-edges cube chain

`run N ⟶ K` reads off (via `wedgeToCubes`) a chain of `N` edges of `K` (all dimension `1`),
and conversely `wedgeDesc` glues such a chain back into a run-map.  This is `equivWedgeHom`
restricted to the `dims = replicate N 1` fiber. -/

open CategoryTheory Opposite CubeChain StdCube BPSet

/-- An **edge chain** of `K` of length `N`: a cube chain from `init` to `final` all of whose
cubes are edges (dimension `1`). -/
def EdgeChain (K : BPSet) (N : ℕ) : Type :=
  { cs : List (Σ n : ℕ+, K.cells (n : ℕ)) //
      cs.map (·.1) = List.replicate N (1 : ℕ+) ∧ IsCubeChain K.init cs K.final }

/-- The run-map assembled from an edge chain (`wedgeDesc`, transported to domain `run N`). -/
def edgeChainMap {K : BPSet} {N : ℕ} (cs : EdgeChain K N) : run N ⟶ K :=
  (eqToHom (congrArg BPSet.serialWedge cs.2.1.symm) : run N ⟶ ⋁(cs.1.map (·.1)))
    ≫ wedgeDescHom cs.1 (wedgeDesc K.init K.final cs.1 cs.2.2)

theorem edgeChainMap_hom {K : BPSet} {N : ℕ} (cs : EdgeChain K N) :
    (edgeChainMap cs).hom
      = eqToHom (congrArg (fun l => (⋁l).toPsh) cs.2.1.symm)
        ≫ (wedgeDesc K.init K.final cs.1 cs.2.2).map := by
  rw [edgeChainMap, comp_hom, bpset_eqToHom_hom]
  rfl

/-- Reading the cubes back off an assembled edge-chain map recovers the edge chain. -/
theorem edgeChainMap_wedgeToCubes {K : BPSet} {N : ℕ} (cs : EdgeChain K N) :
    wedgeToCubes ⟨List.replicate N (1 : ℕ+), (edgeChainMap cs).hom⟩ = cs.1 := by
  rw [edgeChainMap_hom, wedgeToCubes_eqToHom cs.2.1.symm, wedgeToCubes_wedgeDesc]

/-- **The run-maps of `K` are exactly its length-`N` edge chains.** -/
def runEdgeEquiv (K : BPSet) (N : ℕ) : (run N ⟶ K) ≃ EdgeChain K N where
  toFun φ := ⟨wedgeToCubes ⟨List.replicate N (1 : ℕ+), φ.hom⟩,
    wedgeToCubes_dims _ _, by
      have h := wedgeToCubes_isCubeChain (K := K) (List.replicate N (1 : ℕ+)) φ.hom
      rw [← φ.app_init, ← φ.app_final]
      exact h⟩
  invFun := edgeChainMap
  left_inv φ := by
    apply bpset_hom_ext_of_wedgeToCubes
    change wedgeToCubes ⟨List.replicate N (1 : ℕ+), (edgeChainMap _).hom⟩
      = wedgeToCubes ⟨List.replicate N (1 : ℕ+), φ.hom⟩
    exact edgeChainMap_wedgeToCubes _
  right_inv cs := Subtype.ext (edgeChainMap_wedgeToCubes cs)

/-! ## Layer 1: a run of `□ᵈ` is a chamber

An edge chain of `□ᵈ` (`d` edges from `init` to `final`) has singleton blocks — each edge flips
exactly one axis — so its `blockIndex : Fin d → Fin d` is a bijection.  The chamber orders the axes
by their flip step (`covectorHeight`). -/

/-- The `RefineObj` of `□ᵈ` underlying an edge chain. -/
def edgeRefine {d : ℕ} (cs : EdgeChain (□d) d) : RefineObj (□d).init (□d).final :=
  ⟨cs.1, cs.2.2⟩

theorem edge_length {d : ℕ} (cs : EdgeChain (□d) d) : cs.1.length = d := by
  have h := congrArg List.length cs.2.1
  rwa [List.length_map, List.length_replicate] at h

/-- Every bead of an edge chain is an edge (dimension `1`). -/
theorem edge_dim {d : ℕ} (cs : EdgeChain (□d) d) (i : Fin (edgeRefine cs).cubes.length) :
    ((edgeRefine cs).cubes.get i).1 = (1 : ℕ+) := by
  have hmem : ((edgeRefine cs).cubes.get i).1 ∈ (edgeRefine cs).cubes.map (·.1) :=
    List.mem_map.mpr ⟨(edgeRefine cs).cubes.get i, List.get_mem _ _, rfl⟩
  have hrep : (edgeRefine cs).cubes.map (·.1) = List.replicate d (1 : ℕ+) := cs.2.1
  rw [hrep, List.mem_replicate] at hmem
  exact hmem.2

/-- Each block of an edge chain is a singleton (an edge flips one axis). -/
theorem edge_block_card {d : ℕ} (cs : EdgeChain (□d) d) (i : Fin (edgeRefine cs).cubes.length) :
    (blockOf (edgeRefine cs) i).card = 1 := by
  have hp : (blockOf (edgeRefine cs) i).card = ((edgeRefine cs).cubes.get i).1 :=
    (toStar ((edgeRefine cs).cubes.get i).2).prop
  rw [hp, edge_dim cs i]; rfl

/-- `covectorHeight` of an edge chain is injective (`blockIndex` is injective on singletons). -/
theorem edge_covectorHeight_inj {d : ℕ} (cs : EdgeChain (□d) d) :
    Function.Injective (covectorHeight (edgeRefine cs)) := by
  intro p q hpq
  have hbi : blockIndex (edgeRefine cs) p = blockIndex (edgeRefine cs) q := by
    have h := hpq; simp only [covectorHeight] at h
    exact Fin.ext (by exact_mod_cast h)
  have hp := blockIndex_mem (edgeRefine cs) p
  have hq : q ∈ blockOf (edgeRefine cs) (blockIndex (edgeRefine cs) p) :=
    (mem_block_iff (edgeRefine cs)).mpr hbi.symm
  exact Finset.card_le_one.mp (le_of_eq (edge_block_card cs _)) p hp q hq

/-- **Forward (layer 1): the chamber of a run of `□ᵈ`** — axes ordered by flip step. -/
def edgeToChamber {d : ℕ} (cs : EdgeChain (□d) d) : Chamber d :=
  chamberOfInj (covectorHeight (edgeRefine cs)) (edge_covectorHeight_inj cs)

/-! ### Layer 1 backward: the run of `□ᵈ` realising a chamber

Bead `k` flips the axis whose chamber rank is `k`; a coordinate `p` is held at `1` once its rank
`c.predCard p` has passed. -/

section Backward
variable {d : ℕ} (c : Chamber d)

/-- The `k`-th edge cell of the run realising `c`: free at the axis of rank `k`, `1` on the axes of
smaller rank, `0` on those of larger rank. -/
def bwdEdge (k : Fin d) : Cell d 1 :=
  ⟨fun p => if c.predCard p < (k : ℕ) then some true
      else if (k : ℕ) < c.predCard p then some false else none, by
    have hset : noneSet (fun p => if c.predCard p < (k : ℕ) then some true
        else if (k : ℕ) < c.predCard p then some false else none)
        = {c.toPerm.symm k} := by
      ext p
      rw [mem_noneSet, Finset.mem_singleton]
      constructor
      · intro h
        by_cases h1 : c.predCard p < (k : ℕ)
        · rw [if_pos h1] at h; exact absurd h (by simp)
        · by_cases h2 : (k : ℕ) < c.predCard p
          · rw [if_neg h1, if_pos h2] at h; exact absurd h (by simp)
          · have hpk : c.predCard p = (k : ℕ) := by omega
            have : c.toPerm p = k := Fin.ext hpk
            rw [← this, Equiv.symm_apply_apply]
      · intro h; subst h
        have hpk : c.predCard (c.toPerm.symm k) = (k : ℕ) := by
          have : (c.toPerm (c.toPerm.symm k) : Fin d).val = c.predCard (c.toPerm.symm k) := rfl
          rw [← this, Equiv.apply_symm_apply]
        rw [if_neg (by omega), if_neg (by omega)]
    rw [hset]; exact Finset.card_singleton _⟩

@[simp] theorem bwdEdge_val (k : Fin d) (p : Fin d) :
    (bwdEdge c k).val p = if c.predCard p < (k : ℕ) then some true
      else if (k : ℕ) < c.predCard p then some false else none := rfl

theorem bwdEdge_mem_none (k : Fin d) (p : Fin d) :
    p ∈ noneSet (bwdEdge c k).val ↔ c.predCard p = (k : ℕ) := by
  rw [mem_noneSet, bwdEdge_val]
  by_cases h1 : c.predCard p < (k : ℕ)
  · rw [if_pos h1]; simp only [reduceCtorEq, false_iff]; omega
  · by_cases h2 : (k : ℕ) < c.predCard p
    · rw [if_neg h1, if_pos h2]; simp only [reduceCtorEq, false_iff]; omega
    · rw [if_neg h1, if_neg h2]; simp only [true_iff]; omega

/-- The junction vertex before step `j`: axes of rank `< j` are `1`, the rest `0`. -/
def bwdVtx (j : ℕ) : Cell d 0 :=
  ⟨fun p => if c.predCard p < j then some true else some false, by
    simp only [noneSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _; split <;> simp⟩

@[simp] theorem bwdVtx_val (j : ℕ) (p : Fin d) :
    (bwdVtx c j).val p = if c.predCard p < j then some true else some false := rfl

theorem bwdVtx_zero : bwdVtx c 0 = constVertex d false := by
  apply Subtype.ext; funext p; simp [bwdVtx, constVertex]

theorem bwdVtx_top : bwdVtx c d = constVertex d true := by
  apply Subtype.ext; funext p
  simp only [bwdVtx_val, constVertex, if_pos (c.predCard_lt p)]

/-- Facing the `k`-th edge at `false` (the source vertex) is the junction before step `k`. -/
theorem bwdEdge_vertex₀ (k : Fin d) :
    act (K := stdPre d) (bwdEdge c k) (constVertex 1 false) = bwdVtx c (k : ℕ) := by
  apply Subtype.ext; funext p
  rw [app_constVertex_val, bwdVtx_val]
  by_cases hmem : p ∈ noneSet (bwdEdge c k).val
  · have hpk : c.predCard p = (k : ℕ) := (bwdEdge_mem_none c k p).mp hmem
    rw [if_pos hmem, if_neg (by omega : ¬ c.predCard p < (k : ℕ))]
  · have hne : c.predCard p ≠ (k : ℕ) := fun h => hmem ((bwdEdge_mem_none c k p).mpr h)
    rw [if_neg hmem, bwdEdge_val]
    by_cases h : c.predCard p < (k : ℕ)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_pos (by omega), if_neg h]

/-- Facing the `k`-th edge at `true` (the target vertex) is the junction after step `k`. -/
theorem bwdEdge_vertex₁ (k : Fin d) :
    act (K := stdPre d) (bwdEdge c k) (constVertex 1 true) = bwdVtx c ((k : ℕ) + 1) := by
  apply Subtype.ext; funext p
  rw [app_constVertex_val, bwdVtx_val]
  by_cases hmem : p ∈ noneSet (bwdEdge c k).val
  · have hpk : c.predCard p = (k : ℕ) := (bwdEdge_mem_none c k p).mp hmem
    rw [if_pos hmem, if_pos (by omega : c.predCard p < (k : ℕ) + 1)]
  · have hne : c.predCard p ≠ (k : ℕ) := fun h => hmem ((bwdEdge_mem_none c k p).mpr h)
    rw [if_neg hmem, bwdEdge_val]
    by_cases h : c.predCard p < (k : ℕ)
    · rw [if_pos h, if_pos (by omega : c.predCard p < (k : ℕ) + 1)]
    · rw [if_neg h, if_pos (by omega), if_neg (by omega : ¬ c.predCard p < (k : ℕ) + 1)]

/-- The source vertex of the `k`-th cube is the junction before step `k`. -/
theorem bwdCube_vertex₀ (k : Fin d) :
    (□d).toPsh.vertex₀ (canonicalMap (bwdEdge c k) : (□d).cells 1)
      = canonicalMap (bwdVtx c (k : ℕ)) := by
  apply toStar_injective
  rw [toStar_vertex₀, toStar_canonicalMap, toStar_canonicalMap, bwdEdge_vertex₀]

/-- The target vertex of the `k`-th cube is the junction after step `k`. -/
theorem bwdCube_vertex₁ (k : Fin d) :
    (□d).toPsh.vertex₁ (canonicalMap (bwdEdge c k) : (□d).cells 1)
      = canonicalMap (bwdVtx c ((k : ℕ) + 1)) := by
  apply toStar_injective
  rw [toStar_vertex₁, toStar_canonicalMap, toStar_canonicalMap, bwdEdge_vertex₁]

/-- The cube list of the run realising `c`. -/
def bwdCubes : List (Σ n : ℕ+, (□d).cells (n : ℕ)) :=
  List.ofFn (fun k : Fin d => ⟨(1 : ℕ+), canonicalMap (bwdEdge c k)⟩)

theorem bwdCubes_dims : (bwdCubes c).map (·.1) = List.replicate d (1 : ℕ+) := by
  rw [bwdCubes, List.map_ofFn]
  exact List.ofFn_const d (1 : ℕ+)

theorem bwdCubes_length : (bwdCubes c).length = d := by rw [bwdCubes, List.length_ofFn]

theorem bwdCubes_get (i : Fin (bwdCubes c).length) :
    (bwdCubes c).get i = ⟨(1 : ℕ+), canonicalMap (bwdEdge c (Fin.cast (bwdCubes_length c) i))⟩ := by
  change (List.ofFn (fun k : Fin d => (⟨(1 : ℕ+), canonicalMap (bwdEdge c k)⟩
      : Σ n : ℕ+, (□d).cells (n : ℕ)))).get i = _
  rw [List.get_ofFn]
  rfl

theorem bwdCubes_isChain :
    IsCubeChain (□d).init (bwdCubes c) (□d).final := by
  have hlen : (bwdCubes c).length = d := bwdCubes_length c
  have hchain := isCubeChain_aux (K := □d) (bwdCubes c)
    (fun j : Fin ((bwdCubes c).length + 1) => canonicalMap (bwdVtx c (j : ℕ)))
    (fun i => by rw [bwdCubes_get]; exact bwdCube_vertex₀ c (Fin.cast hlen i))
    (fun i => by rw [bwdCubes_get]; exact bwdCube_vertex₁ c (Fin.cast hlen i))
  rw [show (fun j : Fin ((bwdCubes c).length + 1) => canonicalMap (bwdVtx c (j : ℕ))) 0
        = (□d).init from by
      simp only [Fin.val_zero, bwdVtx_zero]; rfl,
    show (fun j : Fin ((bwdCubes c).length + 1) => canonicalMap (bwdVtx c (j : ℕ)))
        (Fin.last (bwdCubes c).length) = (□d).final from by
      simp only [Fin.val_last, hlen, bwdVtx_top]; rfl] at hchain
  exact hchain

/-- **Backward (layer 1): the run of `□ᵈ` realising a chamber.** -/
def chamberToEdge : EdgeChain (□d) d :=
  ⟨bwdCubes c, bwdCubes_dims c, bwdCubes_isChain c⟩

/-- The sign vector of the `i`-th cube of the constructed run is the `i`-th edge cell. -/
theorem chamberToEdge_toStar (i : Fin (edgeRefine (chamberToEdge c)).cubes.length) :
    (toStar ((edgeRefine (chamberToEdge c)).cubes.get i).2).val
      = (bwdEdge c (Fin.cast (bwdCubes_length c) i)).val := by
  have h := congrArg (fun X : Σ n : ℕ+, (□d).cells (n : ℕ) => (toStar X.2).val)
    (bwdCubes_get c i)
  simp only [toStar_canonicalMap] at h
  exact h

/-- In the constructed run, `covectorHeight` reads back the chamber rank. -/
theorem bwd_covectorHeight (p : Fin d) :
    covectorHeight (edgeRefine (chamberToEdge c)) p = (c.predCard p : ℤ) := by
  have hlen : (edgeRefine (chamberToEdge c)).cubes.length = d := bwdCubes_length c
  have hlt : c.predCard p < (edgeRefine (chamberToEdge c)).cubes.length := by
    rw [hlen]; exact c.predCard_lt p
  have hmem : p ∈ blockOf (edgeRefine (chamberToEdge c)) ⟨c.predCard p, hlt⟩ := by
    have hb : blockOf (edgeRefine (chamberToEdge c)) ⟨c.predCard p, hlt⟩
        = noneSet (toStar ((edgeRefine (chamberToEdge c)).cubes.get ⟨c.predCard p, hlt⟩).2).val :=
      rfl
    rw [hb, mem_noneSet, chamberToEdge_toStar, ← mem_noneSet, bwdEdge_mem_none, Fin.val_cast]
  rw [covectorHeight, blockIndex_unique (edgeRefine (chamberToEdge c)) hmem]

/-- **Easy round trip:** the chamber of the run realising `c` is `c`. -/
theorem edgeToChamber_chamberToEdge : edgeToChamber (chamberToEdge c) = c := by
  apply Chamber.ext; funext i j
  change (chamberOfInj (covectorHeight (edgeRefine (chamberToEdge c)))
      (edge_covectorHeight_inj (chamberToEdge c))).lt i j = c.lt i j
  rw [chamberOfInj_lt, bwd_covectorHeight, bwd_covectorHeight, eq_iff_iff, Nat.cast_lt]
  exact c.predCard_lt_iff i j

end Backward

/-! ### Layer 1 hard round trip: an edge chain is its chamber's run

`c.predCard` for the read-off chamber equals `covectorHeight` (`blockIndex`); a coordinate's
edge value is fixed by whether its block has passed (`Fval` monotonicity + junctions). -/

/-- For a bijection `g : Fin d → Fin d`, the number of coordinates with strictly smaller
`g`-value is `g`'s value. -/
theorem card_lt_of_bijective {d : ℕ} {g : Fin d → Fin d} (hg : Function.Bijective g) (p : Fin d) :
    (Finset.univ.filter (fun q => (g q).val < (g p).val)).card = (g p).val := by
  have himg : (Finset.univ.filter (fun q => (g q).val < (g p).val)).image g
      = Finset.univ.filter (fun m : Fin d => m.val < (g p).val) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hm
      obtain ⟨q, rfl⟩ := hg.2 m
      exact ⟨q, hm, rfl⟩
  rw [← Finset.card_image_of_injective _ hg.1, himg]
  have : Finset.univ.filter (fun m : Fin d => m.val < (g p).val) = Finset.Iio (g p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  rw [this, Fin.card_Iio]

/-- The read-off chamber's rank of an edge chain is exactly the flip step (`covectorHeight`). -/
theorem predCard_edgeToChamber {d : ℕ} (cs : EdgeChain (□d) d) (p : Fin d) :
    ((edgeToChamber cs).predCard p : ℤ) = covectorHeight (edgeRefine cs) p := by
  have hlen : (edgeRefine cs).cubes.length = d := edge_length cs
  let g : Fin d → Fin d := fun q => Fin.cast hlen (blockIndex (edgeRefine cs) q)
  have hgval : ∀ q, ((g q).val : ℤ) = covectorHeight (edgeRefine cs) q := fun _ => rfl
  have hginj : Function.Injective g := by
    intro a b hab
    have hbi : blockIndex (edgeRefine cs) a = blockIndex (edgeRefine cs) b := by
      apply Fin.ext
      have hv : (g a).val = (g b).val := congrArg Fin.val hab
      exact hv
    have hp := blockIndex_mem (edgeRefine cs) a
    have hq : b ∈ blockOf (edgeRefine cs) (blockIndex (edgeRefine cs) a) :=
      (mem_block_iff (edgeRefine cs)).mpr hbi.symm
    exact Finset.card_le_one.mp (le_of_eq (edge_block_card cs _)) a hp b hq
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
  have hcard : (edgeToChamber cs).predCard p
      = (Finset.univ.filter (fun q => (g q).val < (g p).val)).card := by
    simp only [edgeToChamber, Chamber.predCard, chamberOfInj_lt]
    congr 1
    apply Finset.filter_congr
    intro q _
    rw [← hgval q, ← hgval p, Nat.cast_lt]
  rw [hcard, card_lt_of_bijective hgbij p]
  exact hgval p

/-- The flip-indicator `Fval` records exactly whether the block has passed. -/
theorem Fval_eq {d : ℕ} (x : RefineObj (□d).init (□d).final) (p : Fin d)
    (j : Fin (x.cubes.length + 1)) :
    Fval x p j = decide ((blockIndex x p).val < j.val) := by
  have hcs : Fval x p (blockIndex x p).castSucc = false := by
    have hfe : Fval x p (blockIndex x p).castSucc
        = decide ((toStar (vtxCanon x.cubes (□d).final (blockIndex x p).castSucc)).val p
            = some true) := rfl
    have h := toStar_junc_castSucc x (blockIndex x p) p
    rw [if_pos (blockIndex_mem x p)] at h
    rw [hfe, h]; rfl
  have hsu : Fval x p (blockIndex x p).succ = true := by
    have hfe : Fval x p (blockIndex x p).succ
        = decide ((toStar (vtxCanon x.cubes (□d).final (blockIndex x p).succ)).val p
            = some true) := rfl
    have h := toStar_junc_succ x (blockIndex x p) p
    rw [if_pos (blockIndex_mem x p)] at h
    rw [hfe, h]; rfl
  rcases Nat.lt_or_ge (blockIndex x p).val j.val with hlt | hle
  · have hjge : (blockIndex x p).succ ≤ j := by rw [Fin.le_def, Fin.val_succ]; omega
    have hmono := Fval_mono x p hjge
    rw [hsu] at hmono
    have hf : Fval x p j = true := le_antisymm (Bool.le_true _) hmono
    rw [hf, decide_eq_true hlt]
  · have hjle : j ≤ (blockIndex x p).castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]; exact hle
    have hmono := Fval_mono x p hjle
    rw [hcs] at hmono
    have hf : Fval x p j = false := le_antisymm hmono (Bool.false_le _)
    rw [hf, decide_eq_false (by omega : ¬ (blockIndex x p).val < j.val)]

/-- A junction vertex holds coordinate `p` at `1` exactly once its block has passed. -/
theorem junction_val {d : ℕ} (x : RefineObj (□d).init (□d).final) (p : Fin d)
    (j : Fin (x.cubes.length + 1)) :
    (toStar (vtxCanon x.cubes (□d).final j)).val p
      = some (decide ((blockIndex x p).val < j.val)) := by
  have hne : (toStar (vtxCanon x.cubes (□d).final j)).val p ≠ none := by
    have hcard : (noneSet (toStar (vtxCanon x.cubes (□d).final j)).val).card = 0 :=
      (toStar (vtxCanon x.cubes (□d).final j)).prop
    rw [Finset.card_eq_zero] at hcard
    intro hp
    have hmem : p ∈ noneSet (toStar (vtxCanon x.cubes (□d).final j)).val := mem_noneSet.mpr hp
    rw [hcard] at hmem
    exact absurd hmem (by simp)
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
  have hfval : Fval x p j = b := by
    have hfe : Fval x p j
        = decide ((toStar (vtxCanon x.cubes (□d).final j)).val p = some true) := rfl
    rw [hfe, hb]; cases b <;> rfl
  rw [hb, ← hfval, Fval_eq]

/-- The sign vector of the `i`-th cube of an edge chain is fixed by the block partition. -/
theorem edge_val_eq {d : ℕ} (x : RefineObj (□d).init (□d).final) (i : Fin x.cubes.length)
    (p : Fin d) (hne : blockIndex x p ≠ i) :
    (toStar (x.cubes.get i).2).val p = some (decide ((blockIndex x p).val < i.val)) := by
  have hp_notin : p ∉ blockOf x i := fun h => hne (blockIndex_unique x h)
  have h1 := toStar_junc_castSucc x i p
  rw [if_neg hp_notin] at h1
  rw [← h1, junction_val, Fin.val_castSucc]

/-- A cube of `□ᵈ` is determined by its dimension and sign vector. -/
theorem cube_ext_of_toStar_val {d : ℕ} {X Y : Σ n : ℕ+, (□d).cells (n : ℕ)}
    (h1 : X.1 = Y.1) (h2 : (toStar X.2).val = (toStar Y.2).val) : X = Y := by
  obtain ⟨nx, x⟩ := X
  obtain ⟨ny, y⟩ := Y
  obtain rfl : nx = ny := h1
  exact congrArg (Sigma.mk nx) (toStar_injective (Subtype.ext h2))

/-- **The crux of the hard round trip:** the reconstructed edge equals the actual edge. -/
theorem bwdEdge_edgeToChamber_val {d : ℕ} (cs : EdgeChain (□d) d)
    (i : Fin (edgeRefine cs).cubes.length) (p : Fin d) :
    (bwdEdge (edgeToChamber cs) (Fin.cast (edge_length cs) i)).val p
      = (toStar ((edgeRefine cs).cubes.get i).2).val p := by
  have hpred : (edgeToChamber cs).predCard p = (blockIndex (edgeRefine cs) p).val := by
    have h := predCard_edgeToChamber cs p
    simp only [covectorHeight] at h
    exact_mod_cast h
  rw [bwdEdge_val, hpred, Fin.val_cast]
  by_cases hbi : (blockIndex (edgeRefine cs) p).val = i.val
  · have hb : blockIndex (edgeRefine cs) p = i := Fin.ext hbi
    have hmem : p ∈ blockOf (edgeRefine cs) i := (mem_block_iff (edgeRefine cs)).mpr hb
    rw [if_neg (by omega), if_neg (by omega)]
    exact (mem_noneSet.mp hmem).symm
  · have hbne : blockIndex (edgeRefine cs) p ≠ i := fun h => hbi (congrArg Fin.val h)
    rw [edge_val_eq (edgeRefine cs) i p hbne]
    rcases lt_or_gt_of_ne hbi with h | h
    · rw [if_pos h, decide_eq_true h]
    · rw [if_neg (by omega), if_pos h, decide_eq_false (by omega)]

/-- **Hard round trip:** an edge chain is the run realising its chamber. -/
theorem chamberToEdge_edgeToChamber {d : ℕ} (cs : EdgeChain (□d) d) :
    chamberToEdge (edgeToChamber cs) = cs := by
  apply Subtype.ext
  change bwdCubes (edgeToChamber cs) = cs.1
  apply List.ext_get
  · rw [bwdCubes_length, edge_length]
  · intro k hk1 hk2
    apply cube_ext_of_toStar_val
    · rw [bwdCubes_get]; exact (edge_dim cs ⟨k, hk2⟩).symm
    · rw [bwdCubes_get]
      change (toStar (canonicalMap (bwdEdge (edgeToChamber cs)
          (Fin.cast (bwdCubes_length (edgeToChamber cs)) ⟨k, hk1⟩)))).val = _
      rw [toStar_canonicalMap]
      funext p
      exact bwdEdge_edgeToChamber_val cs ⟨k, hk2⟩ p

/-- **Layer 1: a run of `□ᵈ` is a chamber.** -/
def runCubeEquiv (d : ℕ) : (run d ⟶ □d) ≃ Chamber d :=
  (runEdgeEquiv (□d) d).trans
    { toFun := edgeToChamber
      invFun := chamberToEdge
      left_inv := chamberToEdge_edgeToChamber
      right_inv := edgeToChamber_chamberToEdge }

/-! ## Layer 2: Segal assembly

The serial wedge has cut vertices, so a run splits per block; assembling `runCubeEquiv` over the
blocks (`Fin.consEquiv` on the chamber side) gives `RunLine a ≃ LinesObj a`. -/

theorem dimSum_cons (d : ℕ+) (rest : List ℕ+) :
    dimSum (d :: rest) = (d : ℕ) + dimSum rest := rfl

/-- The head/tail split of a chamber tuple over `d :: rest`. -/
def consChamberEquiv (d : ℕ+) (rest : List ℕ+) :
    (∀ i : Fin (d :: rest).length, Chamber ((d :: rest).get i : ℕ))
      ≃ Chamber (d : ℕ) × (∀ j : Fin rest.length, Chamber (rest.get j : ℕ)) :=
  (Fin.consEquiv (fun i : Fin (rest.length + 1) => Chamber ((d :: rest).get i : ℕ))).symm

/-- Pushing an edge chain into a wedge is injective (`inl` is a mono). -/
theorem inlPush_injective (X Y : BPSet) : Function.Injective (ChainCat.inlPush X Y) := by
  rintro ⟨n, c⟩ ⟨n', c'⟩ h
  have hn : n = n' := congrArg Sigma.fst h
  subst hn
  simp only [ChainCat.inlPush, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact congrArg (Sigma.mk n) (wedge2_inl_app_injective X Y h)

theorem inrPush_injective (X Y : BPSet) : Function.Injective (ChainCat.inrPush X Y) := by
  rintro ⟨n, c⟩ ⟨n', c'⟩ h
  have hn : n = n' := congrArg Sigma.fst h
  subst hn
  simp only [ChainCat.inrPush, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact congrArg (Sigma.mk n) (wedge2_inr_app_injective X Y h)

/-- A list of edges (all dimension `1`) of the right length has `dims = replicate _ 1`. -/
theorem list_all_one_dims {K : BPSet} (l : List (Σ n : ℕ+, K.cells (n : ℕ))) (m : ℕ)
    (hlen : l.length = m) (hall : ∀ c ∈ l, c.1 = (1 : ℕ+)) :
    l.map (·.1) = List.replicate m 1 := by
  rw [List.eq_replicate_iff]
  exact ⟨by rw [List.length_map, hlen], fun b hb => by
    rw [List.mem_map] at hb; obtain ⟨c, hc, rfl⟩ := hb; exact hall c hc⟩

/-- An edge chain of `□ⁿ` from `init` to `final` has dimension sequence `replicate n 1`
(each edge flips one axis, and the altitude jump is `n`). -/
theorem cubeEdge_dims {nd : ℕ} (xc : List (Σ n : ℕ+, (□nd).cells (n : ℕ)))
    (h : IsCubeChain (□nd).init xc (□nd).final) (hall : ∀ c ∈ xc, c.1 = (1 : ℕ+)) :
    xc.map (·.1) = List.replicate nd (1 : ℕ+) := by
  have hmapnat : xc.map (fun c => (c.1 : ℕ)) = List.replicate xc.length 1 := by
    rw [List.eq_replicate_iff]
    refine ⟨List.length_map _, fun b hb => ?_⟩
    rw [List.mem_map] at hb; obtain ⟨c, hc, rfl⟩ := hb; rw [hall c hc]; rfl
  have hlen : xc.length = nd := by
    have hsum := cubes_dims_sum (⟨xc, h⟩ : RefineObj (□nd).init (□nd).final)
    rw [hmapnat, List.sum_replicate, smul_eq_mul, mul_one] at hsum
    exact hsum
  rw [List.eq_replicate_iff]
  exact ⟨by rw [List.length_map, hlen], fun b hb => by
    rw [List.mem_map] at hb; obtain ⟨c, hc, rfl⟩ := hb; exact hall c hc⟩

/-- The concatenation of two runs into the wedge `⋁(d :: rest)`. -/
def concatRun (d : ℕ+) (rest : List ℕ+)
    (fg : (run (d : ℕ) ⟶ □(d : ℕ)) × (run (dimSum rest) ⟶ ⋁rest)) :
    run (dimSum (d :: rest)) ⟶ ⋁(d :: rest) :=
  eqToHom (congrArg BPSet.serialWedge
      (by rw [dimSum_cons]; exact List.replicate_add (d : ℕ) (dimSum rest) 1))
    ≫ ChainCat.concatChainMap (□(d : ℕ)) (⋁rest)
        ⟨List.replicate (d : ℕ) 1, fg.1⟩ ⟨List.replicate (dimSum rest) 1, fg.2⟩

theorem concatRun_wedgeToCubes (d : ℕ+) (rest : List ℕ+)
    (fg : (run (d : ℕ) ⟶ □(d : ℕ)) × (run (dimSum rest) ⟶ ⋁rest)) :
    wedgeToCubes ⟨List.replicate (dimSum (d :: rest)) 1, (concatRun d rest fg).hom⟩
      = (wedgeToCubes ⟨List.replicate (d : ℕ) 1, fg.1.hom⟩).map
          (ChainCat.inlPush (□(d : ℕ)) (⋁rest))
        ++ (wedgeToCubes ⟨List.replicate (dimSum rest) 1, fg.2.hom⟩).map
          (ChainCat.inrPush (□(d : ℕ)) (⋁rest)) := by
  have hlist : List.replicate (dimSum (d :: rest)) (1 : ℕ+)
      = List.replicate (d : ℕ) 1 ++ List.replicate (dimSum rest) 1 := by
    rw [dimSum_cons]; exact List.replicate_add (d : ℕ) (dimSum rest) 1
  have hhom : (concatRun d rest fg).hom
      = eqToHom (congrArg (fun l => (⋁l).toPsh) hlist)
        ≫ (ChainCat.concatChainMap (□(d : ℕ)) (⋁rest)
            ⟨List.replicate (d : ℕ) 1, fg.1⟩ ⟨List.replicate (dimSum rest) 1, fg.2⟩).hom := by
    rw [concatRun, comp_hom, bpset_eqToHom_hom]; rfl
  rw [hhom]
  erw [wedgeToCubes_eqToHom hlist]
  erw [ChainCat.wedgeToCubes_concatChainMap (□(d : ℕ)) (⋁rest)
    ⟨List.replicate (d : ℕ) 1, fg.1⟩ ⟨List.replicate (dimSum rest) 1, fg.2⟩]

/-- **The Segal split of a run.** -/
noncomputable def runConsSplit (d : ℕ+) (rest : List ℕ+) :
    (run (dimSum (d :: rest)) ⟶ ⋁(d :: rest))
      ≃ (run (d : ℕ) ⟶ □(d : ℕ)) × (run (dimSum rest) ⟶ ⋁rest) := by
  have haltW : (wedge2 (□(d : ℕ)) (⋁rest)).AdmitsAltitude :=
    wedge2_admitsAltitude (cube_admitsAltitude (d : ℕ)) (serialWedge_admitsAltitude rest)
  refine (Equiv.ofBijective (concatRun d rest) ⟨?_, ?_⟩).symm
  · -- injective
    rintro fg fg' hfg
    have hcubes : wedgeToCubes ⟨List.replicate (dimSum (d :: rest)) 1, (concatRun d rest fg).hom⟩
        = wedgeToCubes ⟨List.replicate (dimSum (d :: rest)) 1, (concatRun d rest fg').hom⟩ := by
      rw [hfg]
    rw [concatRun_wedgeToCubes, concatRun_wedgeToCubes] at hcubes
    have hlenL : ((wedgeToCubes ⟨List.replicate (d : ℕ) 1, fg.1.hom⟩).map
        (ChainCat.inlPush (□(d : ℕ)) (⋁rest))).length
        = ((wedgeToCubes ⟨List.replicate (d : ℕ) 1, fg'.1.hom⟩).map
          (ChainCat.inlPush (□(d : ℕ)) (⋁rest))).length := by
      rw [List.length_map, List.length_map, wedgeToCubes_length, wedgeToCubes_length]
    obtain ⟨hL, hR⟩ := List.append_inj hcubes hlenL
    have h1 : fg.1 = fg'.1 := by
      apply bpset_hom_ext_of_wedgeToCubes
      exact (List.map_injective_iff.mpr (inlPush_injective (□(d : ℕ)) (⋁rest))) hL
    have h2 : fg.2 = fg'.2 := by
      apply bpset_hom_ext_of_wedgeToCubes
      exact (List.map_injective_iff.mpr (inrPush_injective (□(d : ℕ)) (⋁rest))) hR
    exact Prod.ext h1 h2
  · -- surjective
    intro φ
    obtain ⟨xc, yc, hchx, hchy, hsplit⟩ :=
      ChainCat.chain_split (□(d : ℕ)) (⋁rest) haltW
        (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1
        (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).2.2
    have hcsdims : (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1.map (·.1)
        = List.replicate (dimSum (d :: rest)) 1 :=
      (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).2.1
    have hxc1 : ∀ c ∈ xc, c.1 = (1 : ℕ+) := fun c hc => by
      have hmem : ChainCat.inlPush (□(d : ℕ)) (⋁rest) c
          ∈ (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1 := by
        rw [hsplit]; exact List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
      have hmem1 : (ChainCat.inlPush (□(d : ℕ)) (⋁rest) c).1
          ∈ (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1.map (·.1) :=
        List.mem_map.mpr ⟨_, hmem, rfl⟩
      rw [hcsdims] at hmem1
      exact (List.mem_replicate.mp hmem1).2
    have hyc1 : ∀ c ∈ yc, c.1 = (1 : ℕ+) := fun c hc => by
      have hmem : ChainCat.inrPush (□(d : ℕ)) (⋁rest) c
          ∈ (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1 := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
      have hmem1 : (ChainCat.inrPush (□(d : ℕ)) (⋁rest) c).1
          ∈ (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1.map (·.1) :=
        List.mem_map.mpr ⟨_, hmem, rfl⟩
      rw [hcsdims] at hmem1
      exact (List.mem_replicate.mp hmem1).2
    have hxcdims : xc.map (·.1) = List.replicate (d : ℕ) 1 := cubeEdge_dims xc hchx hxc1
    have hcslen : (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1.length
        = dimSum (d :: rest) := by
      have h := congrArg List.length hcsdims
      rwa [List.length_map, List.length_replicate] at h
    have hxclen : xc.length = (d : ℕ) := by
      have h := congrArg List.length hxcdims
      rwa [List.length_map, List.length_replicate] at h
    have hyclen : yc.length = dimSum rest := by
      have hlm1 : (xc.map (ChainCat.inlPush (□(d : ℕ)) (⋁rest))).length = xc.length :=
        List.length_map ..
      have hlm2 : (yc.map (ChainCat.inrPush (□(d : ℕ)) (⋁rest))).length = yc.length :=
        List.length_map ..
      have hla : (xc.map (ChainCat.inlPush (□(d : ℕ)) (⋁rest))
          ++ yc.map (ChainCat.inrPush (□(d : ℕ)) (⋁rest))).length = xc.length + yc.length := by
        have hlen : (xc.map (ChainCat.inlPush (□(d : ℕ)) (⋁rest))
            ++ yc.map (ChainCat.inrPush (□(d : ℕ)) (⋁rest))).length
            = (xc.map (ChainCat.inlPush (□(d : ℕ)) (⋁rest))).length
              + (yc.map (ChainCat.inrPush (□(d : ℕ)) (⋁rest))).length := List.length_append ..
        rw [hlm1, hlm2] at hlen; exact hlen
      have hcs : (runEdgeEquiv (⋁(d :: rest)) (dimSum (d :: rest)) φ).1.length
          = xc.length + yc.length := by rw [hsplit]; exact hla
      rw [hcslen, dimSum_cons, hxclen] at hcs
      omega
    have hycdims : yc.map (·.1) = List.replicate (dimSum rest) 1 :=
      list_all_one_dims yc (dimSum rest) hyclen hyc1
    refine ⟨((runEdgeEquiv (□(d : ℕ)) (d : ℕ)).symm ⟨xc, hxcdims, hchx⟩,
      (runEdgeEquiv (⋁rest) (dimSum rest)).symm ⟨yc, hycdims, hchy⟩), ?_⟩
    apply bpset_hom_ext_of_wedgeToCubes
    rw [concatRun_wedgeToCubes]
    have hxcm : wedgeToCubes ⟨List.replicate (d : ℕ) 1,
        ((runEdgeEquiv (□(d : ℕ)) (d : ℕ)).symm ⟨xc, hxcdims, hchx⟩).hom⟩ = xc :=
      congrArg Subtype.val ((runEdgeEquiv (□(d : ℕ)) (d : ℕ)).apply_symm_apply ⟨xc, hxcdims, hchx⟩)
    have hycm : wedgeToCubes ⟨List.replicate (dimSum rest) 1,
        ((runEdgeEquiv (⋁rest) (dimSum rest)).symm ⟨yc, hycdims, hchy⟩).hom⟩ = yc :=
      congrArg Subtype.val
        ((runEdgeEquiv (⋁rest) (dimSum rest)).apply_symm_apply ⟨yc, hycdims, hchy⟩)
    rw [hxcm, hycm]
    exact hsplit.symm

/-- The run-map representation of `Lines`, by dimension sequence. -/
noncomputable def runLineEquivAux : (dims : List ℕ+) →
    (run (dimSum dims) ⟶ ⋁dims) ≃ (∀ i : Fin dims.length, Chamber (dims.get i : ℕ))
  | [] =>
      haveI hsub : Subsingleton (run (dimSum ([] : List ℕ+)) ⟶ ⋁([] : List ℕ+)) :=
        ⟨fun f g => by
          apply BPSet.hom_ext
          exact serialWedge_hom_ext [] f.hom g.hom (fun i => i.elim0)
            (f.app_init.trans g.app_init.symm)⟩
      { toFun := fun _ i => i.elim0
        invFun := fun _ => 𝟙 _
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => funext fun i => i.elim0 }
  | d :: rest =>
      (runConsSplit d rest).trans
        (((runCubeEquiv (d : ℕ)).prodCongr (runLineEquivAux rest)).trans
          (consChamberEquiv d rest).symm)

/-- **The run-map representation of `Lines`.**  A line of a chain `a` is a bi-pointed map out of the
all-edges run of `⋁a.dims` — the linchpin bijection `Runs a.dims ≃ ∏ᵢ Chamber (a.dims.get i)`. -/
noncomputable def runLineEquiv {K : BPSet} (a : Ch K) : RunLine a ≃ LinesObj a :=
  runLineEquivAux a.dims

end CubeChains
