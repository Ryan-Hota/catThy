-- TODO set operator precedences

namespace Category

  structure Category.{u, v} where
    mk ::
      Obj : Sort u
      Hom : Obj -> Obj -> Sort v
      seq {X Y Z : Obj} : Hom X Y -> Hom Y Z -> Hom X Z
      assoc {W X Y Z : Obj} {f : Hom W X} {g : Hom X Y} {h: Hom Y Z}
        : seq (seq f g) h = seq f (seq g h)
      id {X : Obj} : Hom X X
      id_left  {X Y : Obj} (f : Hom X Y) : f = seq id f
      id_right {X Y : Obj} (f : Hom X Y) : f = seq f  id

  notation "Obj" => Category.Obj _
  infixr : 60 " ⟶ " => Category.Hom _
  infixl : 70 " ▷ " => Category.seq _
  notation "▷assoc" => Category.assoc _
  -- TODO notation "▷(▷)=(▷)▷" => (Category.assoc _).symm
  notation "𝟙" => Category.id _
  notation "𝟙▷" => Category.id_left _
  notation "▷𝟙" => Category.id_right _

  -----------------------------------------------------------------------

  variable {ℂ : Category}

  structure Isomorphic (A B : ℂ.Obj) where
    mk::
      fwd : A ⟶ B
      bck : B ⟶ A
      proof : fwd ▷ bck = 𝟙 ∧ bck ▷ fwd = 𝟙

  infixr : 70 " ≅ " => Isomorphic

  structure Initial where
    mk ::
      obj : ℂ.Obj
      unique_to (X : Obj) : obj ⟶ X
      proof_unique {X : Obj} : ∀ f : obj ⟶ X, f = unique_to X

  notation "⊥" => Initial
  notation "∃!(⊥⟶)" => Initial.proof_unique _

  structure Terminal where
    mk ::
      obj : ℂ.Obj
      unique_from (X : Obj) : X ⟶ obj
      proof_unique {X : Obj} : ∀ f : X ⟶ obj, f = unique_from X

  infixr : 100 " ⊤ " => Terminal

  structure Product (A B : ℂ.Obj) where
    mk ::
      obj : Obj
      fst : obj ⟶ A
      snd : obj ⟶ B
      pair {X : Obj} : X ⟶ A -> X ⟶ B -> X ⟶ obj
      proof_exists {X : Obj} :
        ∀ fa : X ⟶ A, ∀ fb,
          pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
      proof_unique {X : Obj} : ∀ g : X ⟶ obj,
          pair (g ▷ fst) (g ▷ snd) = g

  infixr : 80 " × " => Product
  notation "fst" => Product.fst _
  notation "snd" => Product.snd _
  notation "⟨"f","g"⟩"  => Product.pair _ f g
  notation "∃(⟶×)" => Product.proof_exists _
  notation "∃!(⟶×)" => Product.proof_unique _

  def times
    {D D' C C' : ℂ.Obj}
    {Prod_of_Ds : D × D'}
    {Prod_of_Cs : C × C'}
    (f : D ⟶ C) (f' : D' ⟶ C')
    : Prod_of_Ds.obj ⟶ Prod_of_Cs.obj :=
      ⟨fst ▷ f, snd ▷ f'⟩

  infixl : 80 " × " => times

  structure Coproduct (A B : ℂ.Obj) where
    mk ::
      obj : Obj
      inl : A ⟶ obj
      inr : B ⟶ obj
      either {X : Obj} : A ⟶ X -> B ⟶ X -> obj ⟶ X
      proof_exists {X : Obj} :
        ∀ fa : A ⟶ X,
          ∀ fb : B ⟶ X,
            inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
      proof_unique {X : Obj} :
        ∀ g : obj ⟶ X,
          either (inl ▷ g) (inr ▷ g) = g

  infixr : 75 " + " => Coproduct
  notation "inl" => Coproduct.inl _
  notation "inr" => Coproduct.inr _
  notation "["f","g"]"  => Coproduct.either _ f g

  structure Exponential (A B : ℂ.Obj) where
    mk ::
      obj : Obj
      any_product (X : Obj) : X × A
      curry {X : Obj} : (any_product X).obj ⟶ B -> X ⟶ obj
      eval : (any_product obj).obj ⟶ B
      proof_exists {X : Obj} :
        ∀ f : (any_product X).obj ⟶ B ,
          (curry f × 𝟙) ▷ eval = f
      proof_unique {X : Obj} :
        ∀ g : X ⟶ obj ,
          curry ((g × 𝟙) ▷ eval) = g

  infixl : 80 " ⟹ " => Exponential
  notation "_×" => Exponential.any_product _
  notation "curry" => Exponential.curry _
  notation "∃(⟶⟹)" => Exponential.proof_exists _
  notation "∃!(⟶⟹)" => Exponential.proof_unique _
  notation "ε" => Exponential.eval _

-----------------------------------------------------------------------

  theorem eq_id_left {X : ℂ.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝟙 :=
      (▷𝟙 _).trans (h X 𝟙)

  theorem eq_id_right {X : ℂ.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
      (𝟙▷ _).trans (h X 𝟙)

  def inits_iso (I I' : @Initial ℂ) : I.obj ≅ I'.obj :=
    let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
    have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
      let fwd := f I I'; let bck := f I' I
      rw [∃!(⊥⟶) (fwd ▷ bck)]
      rw [∃!(⊥⟶) 𝟙]
    Isomorphic.mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

  def products_iso {A B : ℂ.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
    let f (P P' : A × B) : P.obj ⟶ P'.obj := ⟨fst,snd⟩
    have proof (P P' : A × B) : f P P' ▷ f P' P = 𝟙 := by
      let fwd := f P P'; let bck := f P' P
      rw [← ∃!(⟶×) (fwd ▷ bck)]
      repeat rw [▷assoc]
      dsimp [bck]; rw [(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      dsimp [fwd]; rw [(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      rw [𝟙▷ fst, 𝟙▷ snd]
      exact ∃!(⟶×) 𝟙
    Isomorphic.mk (f P P') (f P' P) ⟨proof P P', proof P' P⟩

  -- (ab)^c == (a^c)(b^c)
  def exp_dist_prod {A B C : ℂ.Obj}
    (AxB : A × B) (AxBeC : C ⟹ AxB.obj)
    (AeC : C ⟹ A) (BeC : C ⟹ B) (AeCxBeC : AeC.obj × BeC.obj)
    : AxBeC.obj ≅ AeCxBeC.obj :=

    let iso_A := products_iso _ _
    let iso_B := products_iso _ _
    let fwd := ⟨ curry (iso_A.fwd ▷ ε ▷ fst)
                ,curry (iso_B.fwd ▷ ε ▷ snd) ⟩

    let bck := curry ⟨(fst × 𝟙) ▷ ε, (snd × 𝟙) ▷ ε⟩

    have proof : fwd ▷ bck = 𝟙 := by
      --
      sorry

    have proof' : bck ▷ fwd = 𝟙  := by
      --
      sorry

    Isomorphic.mk fwd bck ⟨proof, proof'⟩

end Category
