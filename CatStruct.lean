namespace Category

  structure Category.{u, v} where
    mk ::
      Obj : Type u
      Hom : Obj -> Obj -> Type v
      seq {x y z : Obj} : Hom x y -> Hom y z -> Hom x z
      assoc {w x y z : Obj} {f : Hom w x} {g : Hom x y} {h: Hom y z}
        : seq (seq f g) h = seq f (seq g h)
      id {x : Obj} : Hom x x
      id_left  {x y : Obj} (f : Hom x y) : seq id f  = f
      id_right {x y : Obj} (f : Hom x y) : seq f  id = f

  infixr : 60 " ⟶ " => Category.Hom _
  infixl : 70 " ▷ " => Category.seq _

  -----------------------------------------------------------------------

  variable {ℂ : Category}
  def Obj := ℂ.Obj

  structure Isomorphic (A B : Obj) where
    mk::
      fwd : A ⟶ B
      bck : B ⟶ A
      proof : fwd ▷ bck = ℂ.id ∧ bck ▷ fwd = ℂ.id

  structure Initial where
    mk ::
      obj : Obj
      unique_to (X : Obj) : obj ⟶ X
      proof_unique (X : Obj) : ∀ f : ℂ.Hom obj X, f = unique_to X

  structure Terminal where
    mk ::
      obj : Obj
      unique_from (X : Obj) : X ⟶ obj
      proof_unique (X : Obj) : ∀ f : ℂ.Hom X obj, f = unique_from X

  structure Product (A B : Obj) where
    mk ::
      obj : Obj
      fst : ℂ.Hom obj A
      snd : obj ⟶ B
      pair {x : Obj} : x ⟶ A -> x ⟶ B -> x ⟶ obj
      proof_exists (X : Obj) :
        ∀ fa : X ⟶ A, ∀ fb,
          pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
      proof_unique (X : Obj) : ∀ g : X ⟶ obj,
          pair (g ▷ fst) (g ▷ snd) = g

  def cross
    {D D' C C' : Obj}
    {Prod_of_Ds : Product D D'}
    {Prod_of_Cs : Product C C'}
    (f : D ⟶ C) (f' : D' ⟶ C')
    : ℂ.Hom Prod_of_Ds.obj Prod_of_Cs.obj :=
      Prod_of_Cs.pair (Prod_of_Ds.fst ▷ f) (Prod_of_Ds.snd ▷ f')

  structure Coproduct (A B : Obj) where
    mk ::
      obj : Obj
      inl : A ⟶ obj
      inr : B ⟶ obj
      either {X : Obj} : A ⟶ X -> B ⟶ X -> obj ⟶ X
      proof_exists (X : Obj) :
        ∀ fa : A ⟶ X,
          ∀ fb,
            inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
      proof_unique (X : Obj) :
        ∀ g : ℂ.Hom obj X,
          either (inl ▷ g) (inr ▷ g) = g

  structure Exponential (A B : Obj) where
    mk ::
      obj : Obj
      all_products (X : Obj) : Product X A
      curry {X : Obj} : (all_products X).obj ⟶ B -> X ⟶ obj
      eval : (all_products obj).obj ⟶ B
      proof_exists (X : Obj) :
        ∀ f : (all_products X).obj ⟶ B ,
          (cross (curry f) ℂ.id) ▷ eval = f
      proof_unique (X : Obj) :
        ∀ g : X ⟶ obj ,
          curry (cross g ℂ.id ▷ eval) = g

-----------------------------------------------------------------------

  theorem eq_id_left {X : Obj}
    {e : X ⟶ X} (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f)
    : e = ℂ.id :=
      (ℂ.id_right _).symm.trans (h X ℂ.id)

  theorem eq_id_right {X : Obj}
    {e : X ⟶ X} (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f)
    : e = ℂ.id :=
      (ℂ.id_left _).symm.trans (h X ℂ.id)

  def inits_iso (i1 i2 : @Initial ℂ)
    : Isomorphic i1.obj i2.obj :=
      have f (i1 i2 : Initial) := i1.unique_to i2.obj
      have proof (i1 i2 : Initial) :=
        let fwd := f i1 i2 ; let bck := f i2 i1
        (i1.proof_unique i1.obj (fwd ▷ bck)).trans
        (i1.proof_unique i1.obj ℂ.id).symm
      Isomorphic.mk (f i1 _) (f i2 _) ⟨proof i1 _, proof i2 _⟩

  def products_iso {A B : Obj} (P P' : @Product ℂ A B)
    : Isomorphic P.obj P'.obj :=
      let f (P P' : Product A B) := P'.pair P.fst P.snd
      have proof (P P' : Product A B) : (f P P' ▷ f P' P) = ℂ.id := by
        let fwd := f P P' ; let bck := f P' P
        rw [← P.proof_unique _ (fwd ▷ bck)]
        repeat rw [ℂ.assoc]
        dsimp [bck]; have h :=  P.proof_exists _ P'.fst P'.snd; rw[h.left, h.right]
        dsimp [fwd]; have h := P'.proof_exists _  P.fst  P.snd; rw[h.left, h.right]
        rw [← ℂ.id_left P.fst, ← ℂ.id_left P.snd]
        exact P.proof_unique _ _
      Isomorphic.mk (f P _) (f P' _) ⟨proof P _, proof P' _⟩

end Category
