import CubeChains.Machinery.Graded
import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Monoid

/-!
# Concurrency/Presentation/BasePresentation — the graded braid monoid as a single polygraph

A `BraidPresentation` is a monoid presentation of `PosBraid N` for every `N`, read as one polygraph
— the **coproduct of one-object polygraphs**, one per strand count — so there is no vertex to
declare unique.  It presents `FullPosBraid` (`braids`), and that is *all* it does: no chain, no
localization, nothing about `Zbp`.  Reading it on `Ch Zbp[W⁻¹]` is a corollary of the paper
polygraph (`fullBaseEquiv`, in `Concurrency/Presentation/PaperArtin`).

`pt` names the 0-cell at a strand count, bijectively, and computes, so a generator names its braid
with no transport (`braids_arrow`).

At strand count `N` the germ 1-cells are `Perm (Fin N)` and the 2-cells are `PosGermRel N`: two
simples compose when their crossing lengths add.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- The germ presentation of `PosBraid n`; the ascription is the point, `PosBraid` being a `def`. -/
def germPresentation (n : ℕ) : Presents (monoidPoly (PosGermRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (PosGermRel n)

/-- The Artin presentation of `ArtinPosBraid n`. -/
def artinPresentation (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (ArtinPosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (ArtinRel n)

/-- **…read on the positive braids**, along Artin-from-Garside — the Artin spelling of the same
component, in the shape the lift consumes. -/
noncomputable def artinComponent (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  (artinPresentation n).transport ((MulEquiv.toSingleObjEquiv (posBraid_equiv_artinPos n)).op).symm

/-! ## The input, bundled

The 0-cells are named by the strand counts and the 1-cells at one of them are the generators there,
so braid data is generators and relations at each strand count (`BraidData`), and a
`BraidPresentation` adds that they present each braid monoid.  Everything downstream is a lift of
that. -/

/-- The braid a generator of a one-object presentation performs; the 0-cells are explicit because
there is exactly one and the generator does not name it. -/
def loopBraid {A R : Type} {sr tr : R → Quiver.Path (Polygraph.loopPt A) (Polygraph.loopPt A)}
    {N : ℕ} (q : Presents (Polygraph.loopPoly A R sr tr) ((SingleObj (PosBraid N))ᵒᵖ)) (s : A) :
    PosBraid N :=
  (q.arrow (x := Polygraph.loopPt A) (y := Polygraph.loopPt A) s).unop

/-- A braid, as a loop of the graded braid monoid read backwards. -/
def braidLoop (N : ℕ) (β : PosBraid N) : (op N : FullPosBraidᵒᵖ) ⟶ op N :=
  Quiver.Hom.op (⟨rfl, β⟩ : @Quiver.Hom FullPosBraid _ N N)

/-- The one-object polygraph a braid presentation carries at one strand count. -/
abbrev strandFibre (Gen Rel : ℕ → Type)
    (src tgt : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N)))
    (N : ℕ) : Polygraph.{0, 0, 0} :=
  Polygraph.loopPoly (Gen N) (Rel N) (src N) (tgt N)

/-- **Generators and relations at each strand count**, read as a single polygraph — the coproduct
over the strand counts. -/
structure BraidData where
  /-- the generators at each strand count -/
  Gen : ℕ → Type
  /-- the relations there -/
  Rel : ℕ → Type
  /-- a relation's source word -/
  src : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N))
  /-- …and its target -/
  tgt : ∀ N : ℕ, Rel N → Quiver.Path (Polygraph.loopPt (Gen N)) (Polygraph.loopPt (Gen N))

namespace BraidData

variable (p : BraidData)

/-- The polygraph at one strand count: `p`'s generators and relations there, at a single 0-cell. -/
abbrev P (N : ℕ) : Polygraph.{0, 0, 0} := strandFibre p.Gen p.Rel p.src p.tgt N

/-- The 0-cell at strand count `N`; there is exactly one, by construction. -/
def v (N : ℕ) : (p.P N).V := ()

/-- The generators at strand count `N`: the 1-cells at its 0-cell. -/
def S (N : ℕ) : Type := (p.P N).Gen (p.v N) (p.v N)


/-- **The polygraph**: one copy of `p`'s one-object polygraph per strand count. -/
def poly : Polygraph.{0, 0, 0} := Polygraph.coprod p.P

/-- The strand-`N` polygraph, included in the whole. -/
def incl (N : ℕ) : p.P N ⟶ p.poly := Polygraph.coprodι p.P N

/-- …on the generating quivers. -/
def pre (N : ℕ) : GenObj (p.P N).Gen ⥤q GenObj p.poly.Gen := (p.incl N).pre

instance pre_faithful (N : ℕ) : (p.pre N).pathsFunctor.Faithful :=
  Polygraph.coprod_pathsFunctor_faithful p.P N

/-- The 0-cell at strand count `N`.  A leg has exactly one, so `Unit`'s eta makes every 0-cell of
the strand-`N` copy this one. -/
noncomputable def pt (N : ℕ) : GenObj p.poly.Gen := (p.pre N).obj (Polygraph.loopPt (p.Gen N))

/-- A generator, as a 1-cell. -/
noncomputable def gen {N : ℕ} (s : p.S N) : p.pt N ⟶ p.pt N := (p.pre N).map s

/-- **Every 0-cell of `p.poly` is a strand count's.** -/
theorem exists_pt (x : GenObj p.poly.Gen) : ∃ N : ℕ, p.pt N = x := by
  obtain ⟨N, y, rfl⟩ := Polygraph.exists_coprod_obj p.P x
  exact ⟨N, rfl⟩

theorem pt_injective : Function.Injective p.pt := fun _ _ h =>
  Polygraph.coprod_index_eq p.P h

/-- **The data of a monoid presentation at every strand count.** -/
def ofRels {S : ℕ → Type} (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop) :
    BraidData where
  Gen := S
  Rel := fun N => monoidRel (rels N) (monoidPt (rels N)) (monoidPt (rels N))
  src := fun _ α => α.1.1
  tgt := fun _ α => α.1.2

end BraidData

/-- **A presentation of the graded positive braid monoid**: braid data presenting the braid monoid on
every number of strands. -/
structure BraidPresentation extends BraidData where
  /-- …presenting the braid monoid on that many strands -/
  part : ∀ N : ℕ, Presents (toBraidData.P N) ((SingleObj (PosBraid N))ᵒᵖ)

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **…presenting the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands. -/
noncomputable def braids : Presents p.poly (FullPosBraid)ᵒᵖ :=
  (Presents.coproduct p.part).transport Graded.sigmaEquiv

/-- The braid a generator names — the strand count has one 0-cell, so its loops *are* the
braids. -/
def braid {N : ℕ} (s : p.S N) : PosBraid N := loopBraid (p.part N) s

/-- …and its permutation. -/
def perm {N : ℕ} (s : p.S N) : Equiv.Perm (Fin N) := posPermHom N (p.braid s)

def BySimples : Prop := ∀ (N : ℕ) (s : p.S N), p.braid s = posPerm (p.perm s)

/-- **The 0-cell at strand count `N` names the strand count** — a leg of `coprod` is definitional
and `Graded.sigmaEquiv` is the identity on degrees, so there is nothing between the two
spellings. -/
theorem braids_at' (N : ℕ) : p.braids.at' (p.pt N) = op N := rfl

/-- **A generator names the loop its braid is**, at its own strand count — the strand-`N`
component, included. -/
theorem braids_arrow {N : ℕ} (s : p.S N) :
    p.braids.arrow (p.gen s) = braidLoop N (p.braid s) :=
  congrArg Graded.sigmaDesc.map
    (Presents.lift_coproductEval_mapPath p.part N (Quiver.Hom.toPath s))

/-- **A monoid presentation of every braid monoid is one** — the constructor the two spellings
below use, and the only place `PresentedMonoid` enters. -/
noncomputable def ofMonoids {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) :
    BraidPresentation where
  toBraidData := BraidData.ofRels rels
  part := fun N =>
    (presentedMonoidPresentation (rels N)).transport (MulEquiv.toSingleObjEquiv (e N)).op

end BraidPresentation

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose. -/
noncomputable def germBP : BraidPresentation :=
  BraidPresentation.ofMonoids PosGermRel (fun _ => MulEquiv.refl _)

/-- **Artin's generators and relations**: `N−1` generators at `N` strands, and the commutation and
braid relations between them. -/
def artinBP : BraidData := BraidData.ofRels ArtinRel

/-- **…presenting the braids**: the same input as the germ, handed Artin-from-Garside instead of the
identity. -/
noncomputable def artinBraids : BraidPresentation :=
  BraidPresentation.ofMonoids ArtinRel (fun N => (posBraid_equiv_artinPos N).symm)

/-- **A germ generator is its own simple, hence its own permutation.** -/
theorem germBP_bySimples : germBP.BySimples := fun _ _ => rfl

/-- **An Artin generator is the simple of its adjacent transposition** — `posOfArtinPos` is the
inverse's underlying map, and it sends a generator to its atom on the nose. -/
@[simp] theorem artinBraids_braid {N : ℕ} (k : artinBraids.S N) :
    artinBraids.braid k = posPerm (adjT k) := rfl

@[simp] theorem artinBraids_perm {N : ℕ} (k : artinBraids.S N) :
    artinBraids.perm k = adjT k := by
  rw [BraidPresentation.perm, artinBraids_braid, posPermHom_posPerm]

theorem artinBraids_bySimples : artinBraids.BySimples := fun _ k => by
  rw [artinBraids_braid k, artinBraids_perm k]

/-- **The `k`-th Artin generator names the `k`-th atom's braid.** -/
theorem artinBraids_arrow (N : ℕ) (k : Fin (N - 1)) :
    artinBraids.braids.arrow (artinBraids.gen k) = braidLoop N (posPerm (adjT k)) :=
  artinBraids.braids_arrow k

end ChainCat
