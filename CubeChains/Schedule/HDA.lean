import CubeChains.Schedule.EventLocalSystem

/-!
# Schedule/HDA — the higher-dimensional-automaton (edge-labelling) layer

The event-naming lemma `NonSelfLinked ∧ AdmitsAltitude ⟹ HasGlobalEventNaming` is **false**
(`Testing/EventNamingCounterexample.lean`, the "trinity"): a self-crossing hyperplane can fold a
line's two events.  The fix implemented here is to make the labelling **input data** — an HDA — so
there is *no monodromy to reconstruct*.

An **HDA** (higher-dimensional automaton) is a bi-pointed precubical set together with an
**action-labelling** of its edges satisfying the *concurrency* (opposite-equal) axiom: the two
parallel edges of every square carry the same label.  Given such a labelling `ℓ`:

* **`evLabel`** names each event `(bead i, direction δ)` of a chain by the label of the
  direction-`δ` edge of bead `i` (its cube cell), read off canonically (`axisEdge`).
* **Coherence is FREE** (`evLabel_coherent`): a global edge-labelling has no monodromy, so events
  matched by a refinement automatically share a name.  The geometry is `parInvariance`: two
  parallel edges of one cube (same axis, different fixed coordinates) get equal labels, because
  every single-coordinate flip is one square's opposite-equal axiom (`flipLemma`), and the general
  case is the flip induction (`edgeLabelC_mkEdge_const`).
* Consequently the **only** remaining hypothesis is fibre-injectivity, `RunInjective`: no cube
  chain uses a label twice.  `hasGlobalEventNaming_of_labelling` then gives `HasGlobalEventNaming`.

As a sanity check the standard cube `□ⁿ` carries the **coordinate labelling** (`cubeLabelling`,
alphabet `Fin n`), which is `RunInjective`, giving a second, HDA-native proof of
`cube_hasGlobalEventNaming`.

-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

variable {K : BPSet} {A : Type}

/-! ## The edge labelling (the HDA structure)

An `EdgeLabelling K A` labels every edge (1-cell) of `K` by a letter of `A`, subject to the
*opposite-equal* / concurrency axiom: for each direction `i ∈ {0,1}` the two parallel `i`-faces of
every square share a label.  (`faceMap false i s` and `faceMap true i s` fix the *same* direction
`i`, hence run along the *same* remaining axis of `s`.) -/

/-- **An edge labelling of `K` over the alphabet `A` (the HDA data).**  Assigns a letter to every
edge, with the concurrency axiom `opp_eq`: parallel edges of any square are equally labelled. -/
structure EdgeLabelling (K : BPSet) (A : Type) where
  /-- The action label of each edge (1-cell). -/
  label : K.cells 1 → A
  /-- **Opposite-equal / concurrency axiom.**  For every square `s` and direction `i ∈ {0,1}`, the
  two parallel `i`-faces of `s` carry the same label. -/
  opp_eq : ∀ (s : K.cells 2) (i : Fin 2),
    label (K.toPsh.faceMap false i s) = label (K.toPsh.faceMap true i s)

namespace HDA

/-! ## Concrete edges and squares of the standard cube

An **edge** of `□ᵏ` in direction `j` with the other coordinates fixed by `v` is `mkEdgeCell j v`;
a **square** of `□ᵏ` with free coordinates `{i, j}` and other coordinates fixed by `v` is
`squareCell i j v`.  These are the standard-cube cells whose canonical maps pull a cube cell of `K`
back to a specific edge / square, on which we run the flip induction. -/

/-- The edge of `□ᵏ` free in direction `j`, with every other coordinate `x` fixed to `v x`. -/
def mkEdgeCell {k : ℕ} (j : Fin k) (v : Fin k → Bool) : Cell k 1 :=
  ⟨fun x => if x = j then none else some (v x), by
    have h : noneSet (fun x => if x = j then none else some (v x)) = {j} := by
      ext x
      rw [mem_noneSet, Finset.mem_singleton]
      by_cases hx : x = j
      · rw [if_pos hx]; exact iff_of_true rfl hx
      · rw [if_neg hx]; exact iff_of_false (Option.some_ne_none _) hx
    rw [h]; exact Finset.card_singleton j⟩

/-- The `none`-set of `mkEdgeCell j v` is `{j}`. -/
theorem noneSet_mkEdgeCell {k : ℕ} (j : Fin k) (v : Fin k → Bool) :
    noneSet (mkEdgeCell j v).val = {j} := by
  ext x
  rw [mem_noneSet, Finset.mem_singleton]
  change (if x = j then none else some (v x)) = none ↔ x = j
  by_cases hx : x = j
  · rw [if_pos hx]; exact iff_of_true rfl hx
  · rw [if_neg hx]; exact iff_of_false (Option.some_ne_none _) hx

/-- The (only) free coordinate of `mkEdgeCell j v` is `j`. -/
theorem nones_mkEdgeCell_zero {k : ℕ} (j : Fin k) (v : Fin k → Bool) :
    nones (mkEdgeCell j v) 0 = j := by
  have hmem : nones (mkEdgeCell j v) 0 ∈ noneSet (mkEdgeCell j v).val :=
    Finset.orderEmbOfFin_mem _ (mkEdgeCell j v).prop 0
  rw [noneSet_mkEdgeCell] at hmem
  exact Finset.mem_singleton.mp hmem

/-- The square of `□ᵏ` free in directions `{i, j}` (`i ≠ j`), with the other coordinates fixed by
`v`. -/
def squareCell {k : ℕ} (i j : Fin k) (v : Fin k → Bool) (hij : i ≠ j) : Cell k 2 :=
  ⟨fun x => if x = i ∨ x = j then none else some (v x), by
    have h : noneSet (fun x => if x = i ∨ x = j then none else some (v x)) = {i, j} := by
      ext x
      rw [mem_noneSet, Finset.mem_insert, Finset.mem_singleton]
      by_cases hx : x = i ∨ x = j
      · rw [if_pos hx]; exact iff_of_true rfl hx
      · rw [if_neg hx]; exact iff_of_false (Option.some_ne_none _) hx
    rw [h, Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hij),
      Finset.card_singleton]⟩

/-- The `none`-set of `squareCell i j v hij` is `{i, j}`. -/
theorem noneSet_squareCell {k : ℕ} (i j : Fin k) (v : Fin k → Bool) (hij : i ≠ j) :
    noneSet (squareCell i j v hij).val = {i, j} := by
  ext x
  rw [mem_noneSet, Finset.mem_insert, Finset.mem_singleton]
  change (if x = i ∨ x = j then none else some (v x)) = none ↔ x = i ∨ x = j
  by_cases hx : x = i ∨ x = j
  · rw [if_pos hx]; exact iff_of_true rfl hx
  · rw [if_neg hx]; exact iff_of_false (Option.some_ne_none _) hx

/-- The direction-`ε` `ii`-face of `squareCell i j v hij` (where `ii` is the position of `i`) is the
edge free in direction `j` with coordinate `i` fixed to `ε`: `mkEdgeCell j (update v i ε)`. -/
theorem face_squareCell {k : ℕ} (i j : Fin k) (v : Fin k → Bool) (hij : i ≠ j) (ε : Bool)
    (ii : Fin 2) (hii : nones (squareCell i j v hij) ii = i) :
    faceCell ε ii (squareCell i j v hij) = mkEdgeCell j (Function.update v i ε) := by
  apply Subtype.ext
  funext x
  change Function.update (squareCell i j v hij).val (nones (squareCell i j v hij) ii)
      (some ε) x = (if x = j then none else some (Function.update v i ε x))
  rw [hii]
  by_cases hxi : x = i
  · subst hxi
    rw [Function.update_self, if_neg hij, Function.update_self]
  · rw [Function.update_of_ne hxi]
    change (if x = i ∨ x = j then none else some (v x))
       = (if x = j then none else some (Function.update v i ε x))
    rw [Function.update_of_ne hxi]
    by_cases hxj : x = j
    · rw [if_pos (Or.inr hxj), if_pos hxj]
    · rw [if_neg (not_or.mpr ⟨hxi, hxj⟩), if_neg hxj]

/-! ## Reading a cube cell as an edge through its canonical map

`edgeLabelC c e` is the label of the edge `K.toPsh.map (canonicalMap e).op c` — the `e`-edge of the
cube cell `c`.  `axisEdge δ` is the canonical direction-`δ` edge (all other coordinates `false`). -/

/-- The canonical direction-`δ` edge `□¹ ⟶ □ᵏ` (all other coordinates fixed to `false`). -/
noncomputable def axisEdge {k : ℕ} (δ : Fin k) : ▫1 ⟶ ▫k :=
  canonicalMap (K := stdPre k) (mkEdgeCell δ (fun _ => false))

/-- `ev` of the canonical axis edge is the concrete edge cell. -/
theorem ev_axisEdge {k : ℕ} (δ : Fin k) :
    ev (axisEdge δ : ▫1 ⟶ ▫k) = mkEdgeCell δ (fun _ => false) :=
  ev_canonicalMap (K := stdPre k) (mkEdgeCell δ (fun _ => false))

/-- The free coordinate of the axis edge `axisEdge δ` is `δ`. -/
theorem nones_axisEdge_zero {k : ℕ} (δ : Fin k) :
    nones (ev (axisEdge δ : ▫1 ⟶ ▫k)) 0 = δ := by
  rw [ev_axisEdge]; exact nones_mkEdgeCell_zero δ (fun _ => false)

/-- **The edge-through-a-cube label.**  For a cube cell `c : K_k` and an edge `e` of `□ᵏ`, the label
of the `e`-edge of `c` (i.e. of `K.toPsh.map (canonicalMap e).op c`). -/
noncomputable def edgeLabelC (ℓ : EdgeLabelling K A) {k : ℕ} (c : K.cells k)
    (e : Cell k 1) : A :=
  ℓ.label (K.toPsh.map (canonicalMap (K := stdPre k) e : ▫1 ⟶ ▫k).op c)

/-- **Canonical map of a face factors through the coface.**  `canonicalMap (faceCell ε i c) =
coface ε i ≫ canonicalMap c`.  Both classify `faceCell ε i c` (cube Yoneda). -/
theorem canonicalMap_face {N k' : ℕ} (c : Cell N (k' + 1)) (ε : Bool) (i : Fin (k' + 1)) :
    (canonicalMap (K := stdPre N) (faceCell ε i c) : ▫k' ⟶ ▫N)
      = (PrecubicalSet.coface ε i ≫ canonicalMap (K := stdPre N) c
          : ▫k' ⟶ ▫N) := by
  have hev : ev (PrecubicalSet.coface ε i
        ≫ canonicalMap (K := stdPre N) c : ▫k' ⟶ ▫N)
      = faceCell ε i c := by
    erw [ev_comp_app, ev_canonicalMap, ev_coface, app_face,
      app_topCell]
    rfl
  symm
  apply PrecubicalConstructions.hom_ext
  intro m a
  rw [canonicalMap_app]
  exact app_unique _ hev a

/-! ## The flip lemma — one square's opposite-equal axiom

Flipping one fixed coordinate of an edge changes it by a single square's parallel-edge pair, so its
label is unchanged.  This is the *only* place the `opp_eq` axiom is consumed. -/

/-- **Flip one fixed coordinate.**  For a cube cell `c`, the `mkEdgeCell j v`-edge and the
`mkEdgeCell j (update v i (! v i))`-edge (differing only at coordinate `i ≠ j`) have equal labels:
they are the two parallel `ii`-faces of one square, so `opp_eq` applies. -/
theorem flipLemma (ℓ : EdgeLabelling K A) {k : ℕ} (c : K.cells k) (j : Fin k)
    (v : Fin k → Bool) (i : Fin k) (hij : i ≠ j) :
    edgeLabelC ℓ c (mkEdgeCell j v)
      = edgeLabelC ℓ c (mkEdgeCell j (Function.update v i (! v i))) := by
  have hi_mem : i ∈ noneSet (squareCell i j v hij).val := by
    rw [noneSet_squareCell]; exact Finset.mem_insert_self i {j}
  set ii : Fin 2 := nonesIdx (squareCell i j v hij) i hi_mem with hiidef
  have hii : nones (squareCell i j v hij) ii = i :=
    nones_nonesIdx (squareCell i j v hij) i hi_mem
  have hface1 : faceCell (v i) ii (squareCell i j v hij) = mkEdgeCell j v := by
    rw [face_squareCell i j v hij (v i) ii hii, Function.update_eq_self]
  have hface2 : faceCell (! v i) ii (squareCell i j v hij)
      = mkEdgeCell j (Function.update v i (! v i)) :=
    face_squareCell i j v hij (! v i) ii hii
  have hconn : ∀ ε : Bool,
      edgeLabelC ℓ c (faceCell ε ii (squareCell i j v hij))
        = ℓ.label (K.toPsh.faceMap ε ii
            (K.toPsh.map (canonicalMap (K := stdPre k) (squareCell i j v hij)
              : ▫2 ⟶ ▫k).op c)) := by
    intro ε
    simp only [edgeLabelC, PrecubicalSet.faceMap]
    rw [canonicalMap_face]
    erw [op_comp, Functor.map_comp_apply]
    rfl
  rw [← hface1, ← hface2, hconn (v i), hconn (! v i)]
  by_cases hb : v i = true
  · rw [hb]; simp only [Bool.not_true]
    exact (ℓ.opp_eq (K.toPsh.map (canonicalMap (K := stdPre k)
      (squareCell i j v hij) : ▫2 ⟶ ▫k).op c) ii).symm
  · rw [Bool.not_eq_true] at hb
    rw [hb]; simp only [Bool.not_false]
    exact ℓ.opp_eq (K.toPsh.map (canonicalMap (K := stdPre k)
      (squareCell i j v hij) : ▫2 ⟶ ▫k).op c) ii

/-! ## Parallel invariance — the label depends only on the axis

Iterating the flip lemma drives every edge of a cube to the canonical all-`false` axis edge, so two
parallel edges (same free coordinate) of one cube always get equal labels. -/

/-- The set of off-axis coordinates that `v` fixes to `true`. -/
def trueOff {k : ℕ} (j : Fin k) (v : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun x => x ≠ j ∧ v x = true)

/-- **All fixed coordinates may be set to `false`.**  For a cube cell `c`, the `mkEdgeCell j v`-edge
and the canonical `mkEdgeCell j (fun _ => false)`-edge have equal labels — flip every `true` fixed
coordinate to `false` one at a time (`flipLemma`), inducting on `trueOff`. -/
theorem edgeLabelC_mkEdge_const (ℓ : EdgeLabelling K A) {k : ℕ} (c : K.cells k) (j : Fin k)
    (v : Fin k → Bool) :
    edgeLabelC ℓ c (mkEdgeCell j v) = edgeLabelC ℓ c (mkEdgeCell j (fun _ => false)) := by
  have H : ∀ (m : ℕ) (v : Fin k → Bool), (trueOff j v).card = m →
      edgeLabelC ℓ c (mkEdgeCell j v) = edgeLabelC ℓ c (mkEdgeCell j (fun _ => false)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro v hm
      rcases Finset.eq_empty_or_nonempty (trueOff j v) with hempty | hne
      · have hval : mkEdgeCell j v = mkEdgeCell j (fun _ => false) := by
          apply Subtype.ext
          funext x
          change (if x = j then none else some (v x)) = (if x = j then none else some false)
          by_cases hx : x = j
          · rw [if_pos hx, if_pos hx]
          · rw [if_neg hx, if_neg hx]
            have hvx : v x = false := by
              rcases Bool.dichotomy (v x) with hv | hv
              · exact hv
              · exfalso
                have hxmem : x ∈ trueOff j v :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hv⟩
                rw [hempty] at hxmem
                exact absurd hxmem (Finset.notMem_empty x)
            rw [hvx]
        rw [hval]
      · obtain ⟨i, hi⟩ := hne
        have hmem := Finset.mem_filter.mp hi
        have hij : i ≠ j := hmem.2.1
        have hvi : v i = true := hmem.2.2
        have hflip := flipLemma ℓ c j v i hij
        rw [hvi] at hflip
        simp only [Bool.not_true] at hflip
        rw [hflip]
        have herase : trueOff j (Function.update v i false) = (trueOff j v).erase i := by
          ext y
          simp only [trueOff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨hyj, hyv⟩
            have hyi : y ≠ i := by
              rintro rfl
              rw [Function.update_self] at hyv
              exact absurd hyv (by simp)
            exact ⟨hyi, hyj, by rwa [Function.update_of_ne hyi] at hyv⟩
          · rintro ⟨hyi, hyj, hyv⟩
            exact ⟨hyj, by rw [Function.update_of_ne hyi]; exact hyv⟩
        refine IH (trueOff j (Function.update v i false)).card ?_ (Function.update v i false) rfl
        rw [herase, ← hm]
        exact Finset.card_erase_lt_of_mem hi
  exact H (trueOff j v).card v rfl

/-- **Any edge equals its canonical axis edge (up to label).**  `edgeLabelC c e` depends only on the
free coordinate `nones e 0` of `e`. -/
theorem edgeLabelC_axis (ℓ : EdgeLabelling K A) {k : ℕ} (c : K.cells k)
    (e : Cell k 1) :
    edgeLabelC ℓ c e = edgeLabelC ℓ c (mkEdgeCell (nones e 0) (fun _ => false)) := by
  have he : e = mkEdgeCell (nones e 0) (fun x => (e.val x).getD false) := by
    apply Subtype.ext
    funext x
    change e.val x = (if x = nones e 0 then none else some ((e.val x).getD false))
    have hns : noneSet e.val = {nones e 0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.orderEmbOfFin_mem _ e.prop 0, fun y hy => ?_⟩
      exact Finset.card_le_one.mp (le_of_eq e.prop) y hy (nones e 0)
        (Finset.orderEmbOfFin_mem _ e.prop 0)
    by_cases hx : x = nones e 0
    · rw [if_pos hx, hx]
      have hmem : nones e 0 ∈ noneSet e.val :=
        Finset.orderEmbOfFin_mem _ e.prop 0
      rw [mem_noneSet] at hmem
      exact hmem
    · rw [if_neg hx]
      have hxns : x ∉ noneSet e.val := by
        rw [hns, Finset.mem_singleton]; exact hx
      rw [mem_noneSet] at hxns
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hxns
      simp [hb]
  calc edgeLabelC ℓ c e
      = edgeLabelC ℓ c (mkEdgeCell (nones e 0) (fun x => (e.val x).getD false)) :=
        congrArg (edgeLabelC ℓ c) he
    _ = edgeLabelC ℓ c (mkEdgeCell (nones e 0) (fun _ => false)) :=
        edgeLabelC_mkEdge_const ℓ c (nones e 0) (fun x => (e.val x).getD false)

/-- **Parallel invariance (the geometric core).**  Two edges `p, q : □¹ ⟶ □ᵏ` of one cube cell `c`
with the *same* free coordinate (`nones (ev p) 0 = nones (ev q) 0`) have equal labels. -/
theorem parInvariance (ℓ : EdgeLabelling K A) {k : ℕ} (c : K.cells k)
    (p q : ▫1 ⟶ ▫k)
    (h : nones (ev p) 0 = nones (ev q) 0) :
    ℓ.label (K.toPsh.map p.op c) = ℓ.label (K.toPsh.map q.op c) := by
  have hconv : ∀ (r : ▫1 ⟶ ▫k),
      ℓ.label (K.toPsh.map r.op c) = edgeLabelC ℓ c (ev r) := by
    intro r
    have hr : (canonicalMap (K := stdPre k) (ev r) : ▫1 ⟶ ▫k)
        = r := (cubeRepr (stdPre k) 1).left_inv r
    exact congrArg (fun z : ▫1 ⟶ ▫k => ℓ.label (K.toPsh.map z.op c)) hr.symm
  rw [hconv p, hconv q, edgeLabelC_axis ℓ c (ev p), edgeLabelC_axis ℓ c (ev q), h]

/-! ## The induced event-label and the free naming theorem

`beadCell a i` is the cube cell of bead `i` of chain `a` (as a `K`-cell), and `beadCell_factor` is
the bead-face compatibility along a refinement.  `evLabel` labels an event by the direction-`δ` edge
of its bead; coherence is `parInvariance`. -/

/-- **Bead-face compatibility.**  Along a refinement `f : a ⟶ b`, bead `i` of `a` is the
`blockFace f i`-face of bead `blockIdx f i` of `b`. -/
theorem beadCell_factor {a b : Ch K} (f : a ⟶ b) (i : ChainCat.Bead a) :
    beadCell a i
      = K.toPsh.map (blockFace fᵂ i).op (beadCell b (blockIdx fᵂ i)) := by
  have hw : fᵂ ≫ b.map.hom = a.map.hom := congrArg (fun m => m.hom) f.w
  have hmor : ιᵂ a.dims i ≫ a.map.hom
      = yoneda.map (blockFace fᵂ i)
        ≫ (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom) :=
    calc ιᵂ a.dims i ≫ a.map.hom
        = ιᵂ a.dims i ≫ (fᵂ ≫ b.map.hom) := by rw [hw]
      _ = (ιᵂ a.dims i ≫ fᵂ) ≫ b.map.hom := (Category.assoc _ _ _).symm
      _ = (yoneda.map (blockFace fᵂ i)
            ≫ ιᵂ b.dims (blockIdx fᵂ i)) ≫ b.map.hom :=
          congrArg (· ≫ b.map.hom) (blockFace_spec fᵂ i)
      _ = yoneda.map (blockFace fᵂ i)
            ≫ (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom) := Category.assoc _ _ _
  change yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)
      = K.toPsh.map (blockFace fᵂ i).op
          (yonedaEquiv (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom))
  rw [yonedaEquiv_naturality]
  exact congrArg yonedaEquiv hmor

/-- **The induced event-label.**  An event `(bead i, direction δ)` of a chain `a` is named by the
label of the direction-`δ` edge of bead `i` (its cube cell `beadCell a i`). -/
noncomputable def evLabel (ℓ : EdgeLabelling K A) (p : Σ a : Ch K, EventObj a) : A :=
  ℓ.label (K.toPsh.map (axisEdge p.2.2).op (beadCell p.1 p.2.1))

/-- **Coherence is free.**  Events matched by a refinement `f : a ⟶ b` share a name.  The two edges
— direction `δ` of bead `i` (a face of bead `blockIdx f i` of `b`) and direction
`faceEmb (blockFace f i) δ` of that same bead — are parallel edges of one cube of `b`, so
`parInvariance` (i.e. the opposite-equal axiom) equates their labels. -/
theorem evLabel_coherent (ℓ : EdgeLabelling K A) {a b : Ch K} (f : a ⟶ b)
    (e : EventObj a) :
    evLabel ℓ ⟨b, eventMap f e⟩ = evLabel ℓ ⟨a, e⟩ := by
  obtain ⟨i, δ⟩ := e
  change ℓ.label (K.toPsh.map (axisEdge (faceEmb (blockFace fᵂ i) δ)).op
        (beadCell b (blockIdx fᵂ i)))
     = ℓ.label (K.toPsh.map (axisEdge δ).op (beadCell a i))
  rw [beadCell_factor f i]
  simp only [← Functor.map_comp_apply, ← op_comp]
  refine parInvariance ℓ (beadCell b (blockIdx fᵂ i))
    (axisEdge (faceEmb (blockFace fᵂ i) δ)) (axisEdge δ ≫ blockFace fᵂ i) ?_
  rw [nones_axisEdge_zero]
  erw [ev_comp_app]
  rw [nones_app, nones_axisEdge_zero]
  rfl

/-- **No cube chain uses a label twice** (the sole remaining hypothesis). -/
def RunInjective (ℓ : EdgeLabelling K A) : Prop :=
  ∀ a : Ch K, Function.Injective (fun e : EventObj a => evLabel ℓ ⟨a, e⟩)

/-- **The free naming theorem.**  An HDA whose runs are label-injective has a globally coherent
event naming.  Coherence is `evLabel_coherent` (free, from the concurrency axiom); fibre-injectivity
is exactly `RunInjective` (no monodromy left to control). -/
theorem hasGlobalEventNaming_of_labelling (ℓ : EdgeLabelling K A) (h : RunInjective ℓ) :
    HasGlobalEventNaming K :=
  ⟨A, fun p => evLabel ℓ p, fun {_ _} f e => evLabel_coherent ℓ f e, fun a => h a⟩

/-! ## Sanity: the standard cube is an HDA (coordinate labelling)

`□ⁿ` carries the coordinate labelling `ℓ e = nones (toStar e) 0` (the axis an edge flips), over the
alphabet `Fin n`.  Its `evLabel` recovers the coordinate naming `cubeName`, which is `RunInjective`
(`cubeName_faithful`), giving a second, HDA-native proof of `cube_hasGlobalEventNaming`. -/

/-- **The coordinate labelling of `□ⁿ`.**  An edge is labelled by the `□ⁿ`-coordinate it flips; the
concurrency axiom holds because both `i`-faces of a square flip the same ambient coordinate. -/
noncomputable def cubeLabelling (n : ℕ) : EdgeLabelling (□n) (Fin n) where
  label e := nones (toStar e) 0
  opp_eq s i := by
    have key : ∀ ε : Bool, nones (toStar ((□n).toPsh.faceMap ε i s)) 0
        = nones (toStar s) (i.succAbove 0) := by
      intro ε
      have h1 : (□n).toPsh.faceMap ε i s
          = ((□n).toPsh.cubeMap s)⟪1⟫ (PrecubicalSet.coface ε i) := by
        rw [PrecubicalSet.faceMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
      rw [h1, toStar_cubeMap_app, nones_app]
      congr 1
      rw [toStar_eq, ev_coface, face_nones, nones_topCell]
    rw [key false, key true]

/-- **The cube's HDA label recovers the coordinate naming.**  `evLabel (cubeLabelling n) = cubeName`
on every event. -/
theorem cube_evLabel_eq {n : ℕ} (a : Ch (□n)) (e : EventObj a) :
    evLabel (cubeLabelling n) ⟨a, e⟩ = cubeName a e := by
  obtain ⟨i, δ⟩ := e
  change nones (toStar ((□n).toPsh.map (axisEdge δ).op (beadCell a i))) 0
     = cubeName a ⟨i, δ⟩
  have hmap : (□n).toPsh.map (axisEdge δ).op (beadCell a i)
      = ((□n).toPsh.cubeMap (beadCell a i))⟪1⟫ (axisEdge δ) := by
    rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  rw [hmap, toStar_cubeMap_app, nones_app]
  have hδ : nones (toStar (axisEdge δ)) 0 = δ := by
    rw [toStar_eq]; exact nones_axisEdge_zero δ
  rw [hδ]
  rfl

/-- **The cube's coordinate labelling is `RunInjective`** — a chain's distinct events flip distinct
coordinates (`cubeName_faithful`). -/
theorem cube_runInjective (n : ℕ) : RunInjective (cubeLabelling n) := by
  intro a e e' h
  apply cubeName_faithful a
  change cubeName a e = cubeName a e'
  rw [← cube_evLabel_eq a e, ← cube_evLabel_eq a e']
  exact h

/-- **HDA-native recovery.**  The standard cube has a globally coherent event naming, via its
coordinate labelling and the free naming theorem. -/
theorem cube_hasGlobalEventNaming_hda (n : ℕ) : HasGlobalEventNaming (□n) :=
  hasGlobalEventNaming_of_labelling (cubeLabelling n) (cube_runInjective n)

end HDA

end CubeChains
