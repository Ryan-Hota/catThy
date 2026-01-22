namespace Category

  structure Category.{u, v} where
    mk ::
      Object : Type u
      hom : Object -> Object -> Type v
      seq {x y z : Object} : hom x y -> hom y z -> hom x z
      assoc {w x y z : Object} {f : hom w x} {g : hom x y} {h: hom y z}
        : seq (seq f g) h = seq f (seq g h)
      id {x : Object} : hom x x
      id_left  {x y : Object} (f : hom x y) : seq id f  = f
      id_right {x y : Object} (f : hom x y) : seq f  id = f

  infixr : 60 " ⟶ " => Category.hom _
  infixl : 70 " ▷ " => Category.seq _

  -----------------------------------------------------------------------

  variable {C : Category}

  def object := C.Object

  -- Isomorphism of objs
  structure Isomorphic (x y : object) where
    mk::
      fwd : x ⟶ y
      bck : y ⟶ x
      proof : fwd ▷ bck = C.id ∧ bck ▷ fwd = C.id

  structure Initial where
    mk ::
      obj : object
      get_morphism (x : object) : C.hom obj x
      proof (x : object) : ∀ (f : C.hom obj x), f = get_morphism x

  structure Terminal where
    mk ::
      obj : object
      get_morphism (x : object) : C.hom x obj
      proof (x : object) : ∀ (f : C.hom x obj), f = get_morphism x

  structure Product (a b : object) where
    mk ::
      obj : object
      fst : C.hom obj a
      snd : C.hom obj b
      pair {x : object} : C.hom x a -> C.hom x b -> C.hom x obj
      proof_exists (x : object) :
        ∀ (fa : C.hom x a), ∀ fb,
          pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
      proof_unique (x : object) : ∀ (g : C.hom x obj),
          pair (g ▷ fst) (g ▷ snd) = g

  def cross
    {d1 d2 c1 c2 : object}
    {d1Xd2 : Product d1 d2}
    {c1Xc2 : Product c1 c2}
    (f : C.hom d1 c1) (g : C.hom d2 c2)
    : C.hom d1Xd2.obj c1Xc2.obj :=
      c1Xc2.pair (d1Xd2.fst ▷ f) (d1Xd2.snd ▷ g)

  structure Coproduct (a b : object) where
    mk ::
      obj : object
      inl : C.hom a obj
      inr : C.hom b obj
      either {x : object} : C.hom a x -> C.hom b x-> C.hom obj x
      -- TODO: Split into exists and unique
      proof (x : object) : (
        ∀ (fa : C.hom a x),
          ∀ fb,
            inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
      ) ∧ (
        ∀ (g : C.hom obj x),
          either (inl ▷ g) (inr ▷ g) = g
      )

  structure Exponential (a b : object) where
    mk ::
      obj : object
      all_products (x : object) : Product x a
      curry {x : object} : C.hom (all_products x).obj b -> C.hom x obj
      eval : C.hom (all_products obj).obj b
      proof (x : object) : (
        ∀ (f : C.hom (all_products x).obj b) ,
          (cross (curry f) C.id) ▷ eval = f
      ) ∧ (
        ∀ (g : C.hom x obj) ,
          curry (cross g C.id ▷ eval) = g
      )

  theorem eq_id_left {x : object}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : x ⟶ y), e ▷ f = f)
    : e = C.id :=
      (C.id_right _).symm.trans (h x C.id)

  theorem eq_id_right {x : object}
    {e : x ⟶ x} (h : ∀ y, ∀ (f : y ⟶ x), f ▷ e = f)
    : e = C.id :=
      (C.id_left _).symm.trans (h x C.id)

  def inits_iso (i1 i2 : @Initial C)
    : Isomorphic i1.obj i2.obj :=
        have fwd := i1.get_morphism i2.obj
        have bck := i2.get_morphism i1.obj
        have proof_1 :=
          (i1.proof i1.obj (fwd ▷ bck)).trans
          (i1.proof i1.obj C.id).symm
        have proof_2 :=
          (i2.proof i2.obj (bck ▷ fwd)).trans
          (i2.proof i2.obj C.id).symm
        Isomorphic.mk fwd bck ⟨proof_1, proof_2⟩

  def products_iso {a b : object} (p1 p2 : @Product C a b)
    : Isomorphic p1.obj p2.obj :=
      let fwd := p2.pair p1.fst p1.snd
      let bck := p1.pair p2.fst p2.snd
      have proof_1 := by
        rw [←p1.proof_unique _ (fwd ▷ bck)]
        repeat rw [C.assoc]
        dsimp [bck]
        have h1 := p1.proof_exists _ p2.fst p2.snd
        rw [h1.left, h1.right]
        dsimp [fwd]
        have h2 := p2.proof_exists _ p1.fst p1.snd
        rw [h2.left, h2.right]
        rw [←C.id_left p1.fst, ←C.id_left p1.snd]
        exact p1.proof_unique _ C.id
      have proof_2 := by
        rw [←p2.proof_unique _ (bck ▷ fwd)]
        repeat rw [C.assoc]
        dsimp [fwd]
        have h1 := p2.proof_exists _ p1.fst p1.snd
        rw [h1.left, h1.right]
        dsimp [bck]
        have h2 := p1.proof_exists _ p2.fst p2.snd
        rw [h2.left, h2.right]
        rw [←C.id_left p2.fst, ←C.id_left p2.snd]
        exact p2.proof_unique _ C.id
      Isomorphic.mk fwd bck ⟨proof_1, proof_2⟩

end Category
