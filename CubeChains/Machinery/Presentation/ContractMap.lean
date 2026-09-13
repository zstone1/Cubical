import CubeChains.Machinery.Presentation.Contract

/-!
# Machinery/Presentation/ContractMap — a collapse carries its 1-cells along a map of polygraphs

A map of polygraphs *reflecting* the collapsed family and commuting with the representative carries
the conjugated generators of one collapse to those of another: same generator, read at the
pushed-forward representatives.  The two ways a representative is pushed forward differ, and
`gen_eq_homOfEq` is what carries that — nothing else here does.
-/

universe w u' w₂ v u

namespace CategoryTheory

open Polygraph

namespace Collapse

variable {P Q : Polygraph.{w, u', w₂}} {S : ∀ {a b : P.V}, P.Gen a b → Prop}
  {T : ∀ {a b : Q.V}, Q.Gen a b → Prop} {c : Collapse P S} {c' : Collapse Q T}

/-- Renaming a 1-cell's endpoints is `Quiver.homOfEq` and nothing more — `Gen.ext`, the endpoints
entering only through proofs. -/
theorem gen_eq_homOfEq {x y x' y' : c.V} (h₁ : x = x') (h₂ : y = y')
    (e : (⟨x⟩ : GenObj c.Gen) ⟶ ⟨y⟩) (e' : (⟨x'⟩ : GenObj c.Gen) ⟶ ⟨y'⟩)
    (hd : e.dom = e'.dom) (hc : e.cod = e'.cod) (hg : e.gen ≍ e'.gen) :
    e' = Quiver.homOfEq e (congrArg GenObj.mk h₁) (congrArg GenObj.mk h₂) := by
  subst h₁; subst h₂
  change e' = e
  exact (Collapse.Gen.ext c e e' hd hc hg).symm

/-- **Data carrying one collapse's 1-cells to another's**: a map of polygraphs that reflects the
collapsed family and commutes with the representative. -/
structure Map (c : Collapse P S) (c' : Collapse Q T) where
  /-- the map of polygraphs -/
  hom : P ⟶ Q
  /-- …which reflects the collapsed family -/
  mem_iff {a b : P.V} (g : P.Gen a b) : T (hom.pre.map (Polygraph.cell g)) ↔ S g
  /-- …and commutes with the representative -/
  rep_hom (x : P.V) : c'.rep (hom.pre.obj (P.pt x)).as = (hom.pre.obj (P.pt (c.rep x))).as

namespace Map

variable (m : Map c c')

/-- The 0-cell a 0-cell is carried to. -/
def obj (x : P.V) : Q.V := (m.hom.pre.obj (P.pt x)).as

/-- **…a representative to a representative.** -/
def vtx (x : c.V) : c'.V := ⟨m.obj x.1, (m.rep_hom x.1).trans (congrArg m.obj x.2)⟩

/-- **The conjugated generators, carried along** — the same generator, read at the pushed-forward
representatives. -/
def pre : GenObj c.Gen ⥤q GenObj c'.Gen where
  obj X := ⟨m.vtx X.as⟩
  map {_ _} e :=
    { dom := m.obj e.dom
      cod := m.obj e.cod
      gen := m.hom.pre.map (Polygraph.cell e.gen)
      not_mem := fun h => e.not_mem ((m.mem_iff e.gen).mp h)
      rep_dom := (m.rep_hom e.dom).trans (congrArg m.obj e.rep_dom)
      rep_cod := (m.rep_hom e.cod).trans (congrArg m.obj e.rep_cod) }

end Map

end Collapse

end CategoryTheory
