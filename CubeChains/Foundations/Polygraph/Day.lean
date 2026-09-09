import CubeChains.Foundations.Polygraph.Presheaf

/-!
# Foundations/Polygraph/Day — the promonoidal structure on `PolyShape`

`PolyShape` is not monoidal — `cell m n ⊗ cell m' n'` would be a 3-cell — but it is *promonoidal*,
and that is all a convolution needs.  A `Split` of a shape says which of two factors carries each
of its directions, and the profunctor `Pro c a b = Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)` is a
coproduct of representables, so the coend collapses by co-Yoneda to

  `(F ⊛ G) c = Σ s : Split c, F s.fst × G s.snd`.

`Split.square`, the one splitting that puts an edge in each factor, exists only at `cell 2 2`.
-/

universe u

namespace CategoryTheory

open Opposite

namespace PolyShape

/-! ## Splittings

A splitting of a shape into a left and a right factor.  The `cell`/`edge` cases put the whole
shape in one factor; `square` is the genuine 2-dimensional splitting, and there is exactly one. -/

/-- **A splitting of a shape** into a left factor and a right factor. -/
inductive Split : PolyShape → Type
  /-- the point -/
  | pt : Split .pt
  /-- the edge, on the left -/
  | edgeL : Split .edge
  /-- the edge, on the right -/
  | edgeR : Split .edge
  /-- the bigon, on the left -/
  | cellL (m n : ℕ) : Split (.cell m n)
  /-- the bigon, on the right -/
  | cellR (m n : ℕ) : Split (.cell m n)
  /-- an edge in each factor: the interchange square -/
  | square : Split (.cell 2 2)

namespace Split

/-- The left factor of a splitting. -/
def fst : {c : PolyShape} → Split c → PolyShape
  | _, .pt => .pt
  | _, .edgeL => .edge
  | _, .edgeR => .pt
  | _, .cellL m n => .cell m n
  | _, .cellR _ _ => .pt
  | _, .square => .edge

/-- The right factor of a splitting. -/
def snd : {c : PolyShape} → Split c → PolyShape
  | _, .pt => .pt
  | _, .edgeL => .pt
  | _, .edgeR => .edge
  | _, .cellL _ _ => .pt
  | _, .cellR m n => .cell m n
  | _, .square => .edge

end Split

/-! ## The promonoidal profunctor

A splitting with a leg out of each factor.  It is a coproduct of representables, which is why the
convolution's coend collapses; `pull` and `push` are its two actions. -/

/-- **The promonoidal profunctor's cells**: a splitting of `c`, with a leg out of each factor. -/
abbrev Pro (c a b : PolyShape) : Type := Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)

namespace Pro

variable {c a a' a'' b b' b'' : PolyShape}

/-- Post-compose the legs: the covariant action. -/
def push (f : a ⟶ a') (g : b ⟶ b') (T : Pro c a b) : Pro c a' b' :=
  ⟨T.1, T.2.1 ≫ f, T.2.2 ≫ g⟩

@[simp] theorem push_id (T : Pro c a b) : push (𝟙 a) (𝟙 b) T = T := by simp [push]

@[simp] theorem push_push (f : a ⟶ a') (g : b ⟶ b') (f' : a' ⟶ a'') (g' : b' ⟶ b'')
    (T : Pro c a b) : push f' g' (push f g T) = push (f ≫ f') (g ≫ g') T := by simp [push]

end Pro

namespace Split

/-- Which endpoint of each factor a corner of the interchange square is: the corner `(i, j)` of
`□¹ × □¹`, read off the bigon `B 2 2`. -/
def sqVtxAux : Fin 3 ⊕ Fin 3 → Bool × Bool
  | .inl ⟨0, _⟩ => (false, false)
  | .inl ⟨1, _⟩ => (true, false)
  | .inl ⟨_ + 2, _⟩ => (true, true)
  | .inr ⟨0, _⟩ => (false, false)
  | .inr ⟨1, _⟩ => (false, true)
  | .inr ⟨_ + 2, _⟩ => (true, true)

/-- A corner of the interchange square, as a pair of endpoints. -/
def sqVtx : BigonVtx 2 2 → Bool × Bool :=
  BigonVtx.lift sqVtxAux <| by rintro _ _ (_ | _) <;> rfl

/-- A side of the interchange square: which factor carries it, and where the other factor sits. -/
def sqEdge : BigonEdge 2 2 → Pro .edge .edge .edge
  | .inl ⟨0, _⟩ => ⟨.edgeL, 𝟙 _, .end_ false⟩
  | .inl ⟨_ + 1, _⟩ => ⟨.edgeR, .end_ true, 𝟙 _⟩
  | .inr ⟨0, _⟩ => ⟨.edgeR, .end_ false, 𝟙 _⟩
  | .inr ⟨_ + 1, _⟩ => ⟨.edgeL, 𝟙 _, .end_ true⟩

/-- **A splitting, restricted along a face of the site**, with the two comparison legs.  This is
the whole promonoidal structure: `Pro` and the convolution are both read off it. -/
def res : {c' c : PolyShape} → (c' ⟶ c) → (s : Split c) → Pro c' s.fst s.snd
  | _, _, .id _, s => ⟨s, 𝟙 _, 𝟙 _⟩
  | _, _, .end_ b, .edgeL => ⟨.pt, .end_ b, 𝟙 _⟩
  | _, _, .end_ b, .edgeR => ⟨.pt, 𝟙 _, .end_ b⟩
  | _, _, .vtx v, .cellL _ _ => ⟨.pt, .vtx v, 𝟙 _⟩
  | _, _, .vtx v, .cellR _ _ => ⟨.pt, 𝟙 _, .vtx v⟩
  | _, _, .vtx v, .square => ⟨.pt, .end_ (sqVtx v).1, .end_ (sqVtx v).2⟩
  | _, _, .edg e, .cellL _ _ => ⟨.edgeL, .edg e, 𝟙 _⟩
  | _, _, .edg e, .cellR _ _ => ⟨.edgeR, 𝟙 _, .edg e⟩
  | _, _, .edg e, .square => sqEdge e

@[simp] theorem res_id {c : PolyShape} (s : Split c) : res (𝟙 c) s = ⟨s, 𝟙 _, 𝟙 _⟩ := rfl

/-- **Restriction is functorial** — the only composite the site has is `end_ b ≫ edg e =
vtx (bigonEnd b e)`, and this is what it says about splittings. -/
theorem res_comp {c'' c' c : PolyShape} (u : c'' ⟶ c') (v : c' ⟶ c) (s : Split c) :
    res (u ≫ v) s = Pro.push (res v s).2.1 (res v s).2.2 (res u (res v s).1) := by
  cases u with
  | id _ => rfl
  | end_ b =>
      cases v with
      | id _ => cases s <;> rfl
      | edg e =>
          cases s with
          | cellL _ _ => rfl
          | cellR _ _ => rfl
          | square =>
              obtain ⟨_ | _ | i, hi⟩ | ⟨_ | _ | j, hj⟩ := e <;>
                first | omega | (cases b <;> rfl)
  | vtx w => cases v with | id _ => cases s <;> rfl
  | edg e =>
      cases v with
      | id _ =>
          cases s with
          | cellL _ _ => rfl
          | cellR _ _ => rfl
          | square => obtain ⟨_ | _ | i, hi⟩ | ⟨_ | _ | j, hj⟩ := e <;> first | omega | rfl

end Split

namespace Pro

variable {c'' c' c a a' b b' : PolyShape}

/-- Restrict the splitting along a face and absorb the comparison legs: the contravariant
action.  `Split.res`'s value is taken as one argument, so the motive stays non-dependent. -/
def pull (w : c' ⟶ c) (T : Pro c a b) : Pro c' a b := push T.2.1 T.2.2 (Split.res w T.1)

@[simp] theorem pull_id (T : Pro c a b) : pull (𝟙 c) T = T := by simp [pull, push]

theorem pull_pull (u : c'' ⟶ c') (v : c' ⟶ c) (T : Pro c a b) :
    pull (u ≫ v) T = pull u (pull v T) := by
  rw [pull, Split.res_comp]; simp [pull, push]

theorem pull_push (w : c' ⟶ c) (f : a ⟶ a') (g : b ⟶ b') (T : Pro c a b) :
    pull w (push f g T) = push f g (pull w T) := by simp [pull, push]

end Pro

end PolyShape

namespace Polygraph

open PolyShape

/-! ## The convolution

`(F ⊛ G) c = Σ s : Split c, F s.fst × G s.snd`, functorial in `c` by `Split.res` and manifestly
functorial in `F` and `G`. -/

/-- The cells of a convolution at a shape. -/
abbrev DayCells (F G : PolyShapeᵒᵖ ⥤ Type u) (c : PolyShape) : Type u :=
  Σ s : Split c, F.obj (op s.fst) × G.obj (op s.snd)

/-- A pair of cells pulled back along a splitting with legs.  Taking the legs as *one* argument is
what lets `Split.res_comp` be rewritten under it: the motive never mentions the splitting. -/
def dayPull (F G : PolyShapeᵒᵖ ⥤ Type u) {c' A B : PolyShape} (T : Pro c' A B)
    (a : F.obj (op A)) (b : G.obj (op B)) : DayCells F G c' :=
  ⟨T.1, F.map T.2.1.op a, G.map T.2.2.op b⟩

/-- **Dinaturality**: absorbing a pair of legs into the cells is post-composing them onto the
splitting. -/
theorem dayPull_push (F G : PolyShapeᵒᵖ ⥤ Type u) {c' A A' B B' : PolyShape} (T : Pro c' A B)
    (l : A ⟶ A') (r : B ⟶ B') (a : F.obj (op A')) (b : G.obj (op B')) :
    dayPull F G (Pro.push l r T) a b = dayPull F G T (F.map l.op a) (G.map r.op b) := by
  simp only [dayPull, Pro.push, op_comp, Functor.map_comp]; rfl

/-- The face of a convolution cell named by a face of the site: restrict the splitting, and take
the named face in each factor. -/
def dayCellsMap (F G : PolyShapeᵒᵖ ⥤ Type u) {c' c : PolyShape} (w : c' ⟶ c)
    (x : DayCells F G c) : DayCells F G c' :=
  dayPull F G (Split.res w x.1) x.2.1 x.2.2

theorem dayCellsMap_id (F G : PolyShapeᵒᵖ ⥤ Type u) (c : PolyShape) :
    dayCellsMap F G (𝟙 c) = _root_.id := by
  funext x
  obtain ⟨s, a, b⟩ := x
  simp only [dayCellsMap, dayPull, Split.res_id, op_id, Functor.map_id, id_eq]
  rfl

theorem dayCellsMap_comp (F G : PolyShapeᵒᵖ ⥤ Type u) {c'' c' c : PolyShape} (u : c'' ⟶ c')
    (v : c' ⟶ c) : dayCellsMap F G (u ≫ v) = dayCellsMap F G u ∘ dayCellsMap F G v := by
  funext x
  obtain ⟨s, a, b⟩ := x
  change dayPull F G (Split.res (u ≫ v) s) a b = _
  rw [Split.res_comp]
  exact dayPull_push F G (Split.res u (Split.res v s).1) _ _ a b

/-- **The Day convolution of two presheaves on `PolyShape`.** -/
def dayObj (F G : PolyShapeᵒᵖ ⥤ Type u) : PolyShapeᵒᵖ ⥤ Type u where
  obj c := DayCells F G c.unop
  map w := ↾(dayCellsMap F G w.unop)
  map_id c := congrArg TypeCat.ofHom (dayCellsMap_id F G c.unop)
  map_comp w w' := congrArg TypeCat.ofHom (dayCellsMap_comp F G w'.unop w.unop)

@[simp] theorem dayObj_map {F G : PolyShapeᵒᵖ ⥤ Type u} {c c' : PolyShapeᵒᵖ} (w : c ⟶ c')
    (x : DayCells F G c.unop) : (dayObj F G).map w x = dayCellsMap F G w.unop x := rfl

/-- **A map out of a convolution is its components.** -/
theorem dayHom_ext {F G H : PolyShapeᵒᵖ ⥤ Type u} {α β : dayObj F G ⟶ H}
    (h : ∀ (c : PolyShapeᵒᵖ) (x : DayCells F G c.unop), α.app c x = β.app c x) : α = β :=
  NatTrans.ext (funext fun c => TypeCat.homEquiv.injective (funext fun x => h c x))

/-- A pair of maps of presheaves, on convolution cells. -/
def dayMapCells {F F' G G' : PolyShapeᵒᵖ ⥤ Type u} (φ : F ⟶ F') (ψ : G ⟶ G') (c : PolyShape)
    (x : DayCells F G c) : DayCells F' G' c :=
  ⟨x.1, φ.app _ x.2.1, ψ.app _ x.2.2⟩

theorem dayMapCells_naturality {F F' G G' : PolyShapeᵒᵖ ⥤ Type u} (φ : F ⟶ F') (ψ : G ⟶ G')
    {c' c : PolyShape} (w : c' ⟶ c) :
    dayMapCells φ ψ c' ∘ dayCellsMap F G w = dayCellsMap F' G' w ∘ dayMapCells φ ψ c := by
  funext x
  obtain ⟨s, a, b⟩ := x
  exact congrArg₂ (fun a b => (⟨_, a, b⟩ : DayCells F' G' _))
    (ConcreteCategory.congr_hom (φ.naturality _) a)
    (ConcreteCategory.congr_hom (ψ.naturality _) b)

/-- A pair of maps of presheaves, convolved. -/
def dayMap {F F' G G' : PolyShapeᵒᵖ ⥤ Type u} (φ : F ⟶ F') (ψ : G ⟶ G') :
    dayObj F G ⟶ dayObj F' G' where
  app c := ↾(dayMapCells φ ψ c.unop)
  naturality _ _ w := congrArg TypeCat.ofHom (dayMapCells_naturality φ ψ w.unop)

@[simp] theorem dayMap_app {F F' G G' : PolyShapeᵒᵖ ⥤ Type u} (φ : F ⟶ F') (ψ : G ⟶ G')
    (c : PolyShapeᵒᵖ) (x : DayCells F G c.unop) :
    (dayMap φ ψ).app c x = ⟨x.1, φ.app _ x.2.1, ψ.app _ x.2.2⟩ := rfl

/-- **The convolution, as a functor of two presheaves** — functoriality of the tensor is not a
theorem about words, it is the shape of the formula. -/
def dayFunctor : (PolyShapeᵒᵖ ⥤ Type u) ⥤ (PolyShapeᵒᵖ ⥤ Type u) ⥤ (PolyShapeᵒᵖ ⥤ Type u) where
  obj F :=
    { obj := dayObj F
      map := dayMap (𝟙 F)
      map_id _ := dayHom_ext fun _ x => by obtain ⟨s, a, b⟩ := x; rfl
      map_comp _ _ := dayHom_ext fun _ x => by obtain ⟨s, a, b⟩ := x; rfl }
  map φ :=
    { app G := dayMap φ (𝟙 G)
      naturality _ _ _ := dayHom_ext fun _ x => by obtain ⟨s, a, b⟩ := x; rfl }
  map_id _ := NatTrans.ext (funext fun _ =>
    dayHom_ext fun _ x => by obtain ⟨s, a, b⟩ := x; rfl)
  map_comp _ _ := NatTrans.ext (funext fun _ =>
    dayHom_ext fun _ x => by obtain ⟨s, a, b⟩ := x; rfl)

end Polygraph

end CategoryTheory
