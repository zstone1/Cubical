import CubeChains.Machinery.Cube.Box

/-!
# Precubical/Basic/Representable

The **cube Yoneda lemma**, on the nose: a cube map `▫n ⟶ ▫N` *is* a sign vector `Cell N n`,
because that is how `Box` is defined.  So `ev`/`Box.sign` read a map as a cell,
`canonicalMap`/`Box.ofSign` read a cell as a map, `cubeRepr` is `Equiv.refl`, and composition
is substitution (`ev_comp_subst`).

What is left to prove here is only what *refers to* the composition: cofaces
(`ev_coface_comp` faces the sign vector), rigidity of the cube (`Box.endo_eq_id`), monicity of
every cube map (`Box.mono`, from `subst_injective`).  Cube Yoneda for an arbitrary *concrete*
precubical set is the model bridge and lives in `Nerve.lean`.
-/

open CategoryTheory

namespace StdCube

/-- The sign vector of a cube map: the value on the free top cell. -/
def ev {X Y : Box} (f : X ⟶ Y) : Cell Y.dim X.dim := f

/-- The cube map classified by a sign vector. -/
def canonicalMap {N n : ℕ} (c : Cell N n) : ▫n ⟶ ▫N := c

@[simp] theorem ev_canonicalMap {N n : ℕ} (c : Cell N n) : ev (canonicalMap c) = c := rfl

/-- **Representability of the standard cube** (cube Yoneda). -/
def cubeRepr (N n : ℕ) : (▫n ⟶ ▫N) ≃ Cell N n where
  toFun := ev
  invFun := canonicalMap
  left_inv _ := rfl
  right_inv _ := rfl

/-- A cube map is *the* canonical map of its sign vector. -/
theorem eq_canonicalMap {N n : ℕ} {g : ▫n ⟶ ▫N} {c : Cell N n} (h : ev g = c) :
    g = canonicalMap c := h

/-- **Composition of cube maps is substitution** — the dictionary entry that makes every
`ev`-level computation downstream a `subst` computation. -/
theorem ev_comp_subst {X Y Z : Box} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ev (f ≫ g) = subst (ev g) (ev f) := rfl

end StdCube

namespace PrecubicalSet

open StdCube

/-- The coface `□ⁿ ⟶ □ⁿ⁺¹` selecting the `(ε, i)`-face of the top cell. -/
def coface (ε : Bool) {n : ℕ} (i : Fin (n + 1)) : ▫n ⟶ ▫(n + 1) :=
  canonicalMap (faceCell ε i (topCell (n + 1)))

end PrecubicalSet

namespace StdCube

/-- `ev` of a coface is the corresponding face of the top cell. -/
@[simp] theorem ev_coface {k : ℕ} (ε : Bool) (i : Fin (k + 1)) :
    ev (PrecubicalSet.coface ε i) = faceCell ε i (topCell (k + 1)) := rfl

/-- **Precomposing with a coface faces the sign vector.**  The one law every face-level
computation on cubes reduces to. -/
theorem ev_coface_comp {N m : ℕ} (ε : Bool) (i : Fin (m + 1)) (x : ▫(m + 1) ⟶ ▫N) :
    ev (PrecubicalSet.coface ε i ≫ x) = faceCell ε i (ev x) := by
  rw [ev_comp_subst, ev_coface, subst_faceCell, subst_topCell]

/-- **Coface peeling of a canonical map.**  A non-top cell `c'` of `□ᴺ` factors its
canonical map through the smallest-fixed-coordinate coface. -/
theorem canonicalMap_peel {N k : ℕ} (c' : Cell N k) (h : k < N) :
    canonicalMap c' = PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
      ≫ canonicalMap (freeMin c' h) :=
  (eq_canonicalMap ((ev_coface_comp _ _ _).trans
    (by rw [ev_canonicalMap, face_freeMin]))).symm

end StdCube

/-! ### The dictionary in `Box` spelling

`sign`/`ofSign` are `ev`/`canonicalMap` with the dimensions carried by the `Box` objects rather
than by `ℕ`s, which is the form every hom-level caller produces. -/

namespace Box

open StdCube

/-- The sign vector of a `Box` morphism (cube Yoneda: `(X ⟶ Y) ≃ Cell Y.dim X.dim`). -/
def sign {X Y : Box} (f : X ⟶ Y) : Cell Y.dim X.dim := ev f

/-- The `Box` morphism classified by a sign vector. -/
def ofSign {X Y : Box} (c : Cell Y.dim X.dim) : X ⟶ Y := canonicalMap c

@[simp] theorem sign_ofSign {X Y : Box} (c : Cell Y.dim X.dim) : sign (ofSign c) = c := rfl

@[simp] theorem ofSign_sign {X Y : Box} (f : X ⟶ Y) : ofSign (sign f) = f := rfl

theorem hom_ext {X Y : Box} {f g : X ⟶ Y} (h : sign f = sign g) : f = g := h

@[simp] theorem sign_id (X : Box) : sign (𝟙 X) = topCell X.dim := rfl

theorem sign_comp {X Y Z : Box} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sign (f ≫ g) = subst (sign g) (sign f) := rfl

/-- **Every cube map is monic**: a substituted cell remembers what was substituted, so the
cube is non-self-linked. -/
instance mono {X Y : Box} (f : X ⟶ Y) : Mono f where
  right_cancellation _ _ e := subst_injective (sign f) e

/-- **Cubes are rigid.**  `Box` is symmetry-free, so `▫n` has no endomorphism but the identity —
the convention that makes `(BPSet, ⊗)` unbraided and forces the braiding to be *created* by
the passage to executions. -/
theorem endo_eq_id {n : ℕ} (g : ▫n ⟶ ▫n) : g = 𝟙 ▫n := eq_topCell (sign g)

end Box

/-- **A `Box` morphism only lowers dimension**: `▫a ⟶ ▫b` forces `a ≤ b`, since a `b`-cube has no
cell of dimension above `b`. -/
theorem boxHom_dim_le {a b : ℕ} (f : ▫a ⟶ ▫b) : a ≤ b :=
  StdCube.cells_card_le (StdCube.ev f)
