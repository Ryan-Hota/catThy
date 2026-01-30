-- TODO set operator precedences

namespace CategoryTheory

  structure Category.{u, v} where
    mk ::
      Obj : Sort u
      Hom : Obj -> Obj -> Sort v
      seq {X Y Z : Obj} : Hom X Y -> Hom Y Z -> Hom X Z
      assoc {W X Y Z : Obj} {f : Hom W X} {g : Hom X Y} {h: Hom Y Z}
        : seq (seq f g) h = seq f (seq g h)
      id {X : Obj} : Hom X X
      id_left  {X Y : Obj} (f : Hom X Y) : seq id f  = f
      id_right {X Y : Obj} (f : Hom X Y) : seq f  id = f

  notation "Obj" => Category.Obj _
  infixr : 60 " ⟶ " => Category.Hom _
  infixl : 70 " ▷ " => Category.seq _
  notation "(▷)▷=▷(▷)" => Category.assoc _
  -- notation "▷(▷)=(▷)▷" => (Category.assoc _).symm
  notation "𝟙" => Category.id _
  notation "𝟙▷" => Category.id_left _
  notation "▷𝟙" => Category.id_right _

  -----------------------------------------------------------------------

  variable {𝓒 : Category}

  structure Isomorphic (A B : 𝓒.Obj) where
    mk::
      fwd : A ⟶ B
      bck : B ⟶ A
      proof : fwd ▷ bck = 𝟙 ∧ bck ▷ fwd = 𝟙

  infixr : 70 " ≅ " => Isomorphic

  structure Initial where
    mk ::
      obj : 𝓒.Obj
      unique_to (X : Obj) : obj ⟶ X
      proof_unique {X : Obj} : ∀ f : obj ⟶ X, f = unique_to X

  notation " ⊥ " => Initial
  notation " ∃!(⊥⟶) " => Initial.proof_unique _

  structure Terminal where
    mk ::
      obj : 𝓒.Obj
      unique_from (X : Obj) : X ⟶ obj
      proof_unique {X : Obj} : ∀ f : X ⟶ obj, f = unique_from X

  infixr : 100 " ⊤ " => Terminal

  structure Product (A B : 𝓒.Obj) where
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
  notation "⟨" f ", " g "⟩"  => Product.pair _ f g
  notation " ∃(⟶×) " => Product.proof_exists _
  notation " ∃!(⟶×) " => Product.proof_unique _

  def times {D D' C C' : 𝓒.Obj} {Prod_Ds : D × D'} {Prod_Cs : C × C'}
    (f : D ⟶ C) (f' : D' ⟶ C') : Prod_Ds.obj ⟶ Prod_Cs.obj := ⟨fst ▷ f, snd ▷ f'⟩

  infixl : 80 " × " => times

  structure Coproduct (A B : 𝓒.Obj) where
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
  notation "[" f ", " g "]"  => Coproduct.either _ f g

  structure Exponential (A B : 𝓒.Obj) where
    mk ::
      obj : Obj
      all_products (X : Obj) : X × A
      curry {X : Obj} : (all_products X).obj ⟶ B -> X ⟶ obj
      eval : (all_products obj).obj ⟶ B
      proof_exists {X : Obj} :
        ∀ f : (all_products X).obj ⟶ B ,
          (curry f × 𝟙) ▷ eval = f
      proof_unique {X : Obj} :
        ∀ g : X ⟶ obj ,
          g = curry ((g × 𝟙) ▷ eval)

  infixl : 80 " ⟹ " => Exponential
  notation "∀obj,∃×" => Exponential.all_products _
  notation "ε" => Exponential.eval _
  notation "curry" => Exponential.curry _
-----------------------------------------------------------------------

  theorem eq_id_left  {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝟙 :=
      (▷𝟙 _).symm.trans (h X 𝟙)

  theorem eq_id_right {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
      (𝟙▷ _).symm.trans (h X 𝟙)

  def inits_iso (I I' : @Initial 𝓒) : I.obj ≅ I'.obj :=
    let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
    have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
      let fwd := f I I' ; let bck := f I' I
      rw[∃!(⊥⟶) (fwd ▷ bck)]
      rw[∃!(⊥⟶) 𝟙]
    Isomorphic.mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

  def products_iso {A B : 𝓒.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
    let f (P P' : A × B) : P.obj ⟶ P'.obj := ⟨fst,snd⟩
    have proof (P P' : A × B) : f P P' ▷ f P' P = 𝟙 := by
      let fwd := f P P' ; let bck := f P' P
      rw [← ∃!(⟶×) (fwd ▷ bck)]
      repeat rw [(▷)▷=▷(▷)]
      dsimp [bck]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      dsimp [fwd]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      rw [← 𝟙▷ fst, ← 𝟙▷ snd]
      exact ∃!(⟶×) 𝟙
    Isomorphic.mk (f P P') (f P' P) ⟨proof P P', proof P' P⟩

  theorem pair_seq {A B C1 C2 : 𝓒.Obj} {P : C1 × C2}
  : ∀ f (g : B ⟶ _) h, f▷⟨g,h⟩ = (⟨f▷g,f▷h⟩ : A ⟶ P.obj) := by
    intro f g h
    rw[← ∃!(⟶×) (f▷⟨g,h⟩)]
    repeat rw[𝓒.assoc]
    rw[(∃(⟶×) g h).left, (∃(⟶×) g h).right]

  theorem times_seq {X0 X1 X2 Y0 Y1 Y2 : 𝓒.Obj}
    {P0 : X0 × Y0} {P1 : X1 × Y1} {P2 : X2 × Y2}
    : ∀ (a : X0 ⟶ X1) (b : Y0 ⟶ Y1) (c : X1 ⟶ X2) (d : Y1 ⟶ Y2),
    ((a×b : _ ⟶ P1.obj)▷(c×d)) = ((a▷c)×(b▷d) : P0.obj ⟶ P2.obj) := by
    intro a b c d
    dsimp[times]
    rw[pair_seq]
    repeat rw[← 𝓒.assoc]
    rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]

  def exps_iso {A B : 𝓒.Obj} (E E' : B ⟹ A) : E.obj ≅ E'.obj :=
    let f (E E' : B ⟹ A) : E.obj ⟶ E'.obj := curry ( ( 𝟙 × 𝟙 ) ▷ ε )
    have proof (E E' : B ⟹ A) : f E E' ▷ f E' E = 𝟙 := by
      rw[Exponential.proof_unique _ (f E E' ▷ f E' E)]
      rw[← 𝟙▷ 𝟙]
      rw[← times_seq _ _ _ _]
      rw[𝓒.assoc]
      dsimp[f]
      rw[Exponential.proof_exists _ _]
      rw[← 𝓒.assoc]
      rw[times_seq _ _ _ _]
      rw[▷𝟙]
      rw[← 𝟙▷ (curry ( ( 𝟙 × 𝟙 ) ▷ ε ))]
      rw[← times_seq _ _ _ _]
      rw[𝓒.assoc]
      rw[E'.proof_exists _]
      rw[← 𝓒.assoc]
      rw[times_seq _ _ _ _]
      repeat rw[▷𝟙]
      rw[← E.proof_unique 𝟙]
    .mk (f E E') (f E' E) ⟨proof E E', proof E' E⟩

  def anon {A B C : 𝓒.Obj}
  (AxB : A × B) (AxBeC : C ⟹ AxB.obj)
  (AeC : C ⟹ A) (BeC : C ⟹ B) (AeCxBeC : AeC.obj × BeC.obj)
  : AxBeC.obj ≅ AeCxBeC.obj :=
    let curry' {X : Obj} f : X ⟶ _ :=
      ⟨curry ((𝟙×𝟙)▷f▷fst), curry ((𝟙×𝟙)▷f▷snd)⟩
    let eval' := ⟨(fst × 𝟙)▷ε, (snd × 𝟙)▷ε⟩
    have proof_exists' := by
      intro X f
      dsimp[curry', eval']
      rw[pair_seq]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq _ _ _ _]
      repeat rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]
      rw[← 𝟙▷ (curry ((𝟙×𝟙)▷f▷fst))]
      rw[← 𝟙▷ (curry ((𝟙×𝟙)▷f▷snd))]
      repeat rw[← times_seq _ _ _ _]
      repeat rw[𝓒.assoc]
      repeat rw[Exponential.proof_exists _ _]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq _ _ _ _]
      repeat rw[𝟙▷ 𝟙]
      repeat rw[∃!(⟶×) _]
      dsimp[times]
      repeat rw[▷𝟙]
      rw[← 𝟙▷ fst, ← 𝟙▷ snd]
      rw[∃!(⟶×) _]
      rw[𝟙▷]
    have proof_unique' := by
      intro X g
      dsimp[curry', eval']
      repeat rw[𝓒.assoc]
      rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq _ _ _ _]
      repeat rw[𝟙▷]
      repeat rw[← Exponential.proof_unique _ _]
      rw[∃!(⟶×)]
    exps_iso AxBeC (.mk AeCxBeC.obj AxBeC.all_products curry' eval' proof_exists' proof_unique')

end CategoryTheory

-------------------------------------------------------------------------------------------

--# We shall now try implementing some categories.

--# Category Template

-- namespace CategoryName

--   open CategoryTheory

--   def 𝓒 : Category :=
--     let Object : Sort _ := sorry
--     let hom : Object -> Object -> Sort _ := sorry
--     let seq {x y z : Object} : hom x y -> hom y z -> hom x z := sorry
--     have assoc {w x y z : Object} {f : hom w x} {g : hom x y} {h: hom y z}
--       : seq (seq f g) h = seq f (seq g h) := sorry
--     let id {x : Object} : hom x x := sorry
--     have id_left  {x y : Object} (f : hom x y) : seq id f  = f := sorry
--     have id_right {x y : Object} (f : hom x y) : seq f  id = f := sorry
--     Category.mk Object hom seq @assoc id id_left id_right

-- end categoryName

-------------------------------------------------------------------------------------------

namespace DivCategory

  open CategoryTheory

  def Divides (a b : Nat) := ∃ c, a * c = b

  def C : Category :=
    let Object := Nat
    let hom : Object -> Object -> Prop := Divides
    have seq {x y z : Object} : hom x y -> hom y z -> hom x z := by
      intro h1 h2
      dsimp [hom, Divides] at *
      cases h1; rename_i c1 h3
      cases h2; rename_i c2 h4
      rw [← h3] at h4
      exists c1 * c2
      rw [← h4]
      rw [Nat.mul_assoc]
    have assoc {w x y z : Object} {f : hom w x} {g : hom x y} {h: hom y z}
      : seq (seq f g) h = seq f (seq g h) := rfl
    have id {x : Object} : hom x x := ⟨1, Nat.mul_one x⟩
    have id_left  {x y : Object} (f : hom x y) : seq id f  = f := rfl
    have id_right {x y : Object} (f : hom x y) : seq f  id = f := rfl
    Category.mk.{1,0} Object hom seq @assoc id id_left id_right


end DivCategory

-------------------------------------------------------------------------------------------

namespace CategoryOfCategories

  open CategoryTheory

  structure Func (𝔸 : Category) (𝔹 : Category) where
    mk ::
      map_obj : 𝔸.Obj -> 𝔹.Obj
      map_mor {X Y : 𝔸.Obj} : X ⟶ Y -> map_obj X ⟶ map_obj Y
      proof {X Y Z : 𝔸.Obj}
        : ∀ (f : X ⟶ Y) (g : Y ⟶ Z), map_mor (f ▷ g) = map_mor f ▷ map_mor g

  def Cat : Category :=

    let seq {𝕏 𝕐 ℤ : Category} : Func 𝕏 𝕐 -> Func 𝕐 ℤ -> Func 𝕏 ℤ := fun F G =>
      let map_obj : 𝕏.Obj -> ℤ.Obj := G.map_obj ∘ F.map_obj
      let map_mor {A B : 𝕏.Obj}
        : A ⟶ B -> map_obj A ⟶ map_obj B := G.map_mor ∘ F.map_mor
      have proof {P Q R : 𝕏.Obj}
        : ∀ (f : P ⟶ Q) (g : Q ⟶ R), map_mor (f ▷ g) = map_mor f ▷ map_mor g := by
          intro f g
          dsimp [map_mor]
          have h2 := G.proof (F.map_mor f) (F.map_mor g)
          rw [← (F.proof f g)] at h2
          exact h2
      Func.mk map_obj map_mor proof
    have assoc := by simp ; exact ⟨rfl, rfl⟩

    let id {𝕏 : Category} : Func 𝕏 𝕏 := Func.mk id id (fun _ _ => rfl)
    have id_left  := by simp
    have id_right := by simp

    Category.mk Category Func seq assoc id id_left id_right

end CategoryOfCategories

-- -- TODO set operator precedences

-- namespace Category

--   structure Category.{u, v} where
--     mk ::
--       Obj : Sort u
--       Hom : Obj -> Obj -> Sort v
--       seq {X Y Z : Obj} : Hom X Y -> Hom Y Z -> Hom X Z
--       assoc {W X Y Z : Obj} {f : Hom W X} {g : Hom X Y} {h: Hom Y Z}
--         : seq (seq f g) h = seq f (seq g h)
--       id {X : Obj} : Hom X X
--       id_left  {X Y : Obj} (f : Hom X Y) : seq id f  = f
--       id_right {X Y : Obj} (f : Hom X Y) : seq f  id = f

--   notation "Obj" => Category.Obj _
--   infixr : 60 " ⟶ " => Category.Hom _
--   infixl : 70 " ▷ " => Category.seq _
--   notation "(▷)▷=▷(▷)" => Category.assoc _
--   -- TODO notation "▷(▷)=(▷)▷" => (Category.assoc _).symm
--   notation "𝟙" => Category.id _
--   notation "𝟙▷" => Category.id_left _
--   notation "▷𝟙" => Category.id_right _

--   -----------------------------------------------------------------------

--   variable {𝓒 : Category}

--   structure Isomorphic (A B : 𝓒.Obj) where
--     mk::
--       fwd : A ⟶ B
--       bck : B ⟶ A
--       proof : fwd ▷ bck = 𝟙 ∧ bck ▷ fwd = 𝟙

--   infixr : 70 " ≅ " => Isomorphic

--   structure Initial where
--     mk ::
--       obj : 𝓒.Obj
--       unique_to (X : Obj) : obj ⟶ X
--       proof_unique {X : Obj} : ∀ f : obj ⟶ X, f = unique_to X

--   notation " ⊥ " => Initial
--   notation " ∃!(⊥⟶) " => Initial.proof_unique _

--   structure Terminal where
--     mk ::
--       obj : 𝓒.Obj
--       unique_from (X : Obj) : X ⟶ obj
--       proof_unique {X : Obj} : ∀ f : X ⟶ obj, f = unique_from X

--   infixr : 100 " ⊤ " => Terminal

--   structure Product (A B : 𝓒.Obj) where
--     mk ::
--       obj : Obj
--       fst : obj ⟶ A
--       snd : obj ⟶ B
--       pair {X : Obj} : X ⟶ A -> X ⟶ B -> X ⟶ obj
--       proof_exists {X : Obj} :
--         ∀ fa : X ⟶ A, ∀ fb,
--           pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
--       proof_unique {X : Obj} : ∀ g : X ⟶ obj,
--           pair (g ▷ fst) (g ▷ snd) = g

--   infixr : 80 " × " => Product
--   notation "fst" => Product.fst _
--   notation "snd" => Product.snd _
--   notation "⟨" f ", " g "⟩"  => Product.pair _ f g
--   notation " ∃(⟶×) " => Product.proof_exists _
--   notation " ∃!(⟶×) " => Product.proof_unique _

--   def times
--     {D D' C C' : 𝓒.Obj}
--     {Prod_of_Ds : D × D'}
--     {Prod_of_Cs : C × C'}
--     (f : D ⟶ C) (f' : D' ⟶ C')
--     : Prod_of_Ds.obj ⟶ Prod_of_Cs.obj :=
--       ⟨fst ▷ f, snd ▷ f'⟩

--   infixl : 80 " × " => times

--   structure Coproduct (A B : 𝓒.Obj) where
--     mk ::
--       obj : Obj
--       inl : A ⟶ obj
--       inr : B ⟶ obj
--       either {X : Obj} : A ⟶ X -> B ⟶ X -> obj ⟶ X
--       proof_exists {X : Obj} :
--         ∀ fa : A ⟶ X,
--           ∀ fb : B ⟶ X,
--             inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
--       proof_unique {X : Obj} :
--         ∀ g : obj ⟶ X,
--           either (inl ▷ g) (inr ▷ g) = g

--   infixr : 75 " + " => Coproduct
--   notation "[" f ", " g "]"  => Coproduct.either _ f g

--   structure Exponential (A B : 𝓒.Obj) where
--     mk ::
--       obj : Obj
--       all_products (X : Obj) : X × A
--       curry {X : Obj} : (all_products X).obj ⟶ B -> X ⟶ obj
--       eval : (all_products obj).obj ⟶ B
--       proof_exists {X : Obj} :
--         ∀ f : (all_products X).obj ⟶ B ,
--           (curry f × 𝟙) ▷ eval = f
--       proof_unique {X : Obj} :
--         ∀ g : X ⟶ obj ,
--           curry ((g × 𝟙) ▷ eval) = g

--   infixl : 80 " ⟹ " => Exponential
--   notation "∀obj,∃×" => Exponential.all_products _
--   notation "ε" => Exponential.eval _

-- -----------------------------------------------------------------------

--   theorem eq_id_left (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝓒.id :=
--     (▷𝟙 _).symm.trans (h X 𝟙)

--   theorem eq_id_right {X : 𝓒.Obj} {e : X ⟶ X}
--     (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
--       (𝟙▷ _).symm.trans (h X 𝟙)

--   def inits_iso (I I' : @Initial 𝓒) : I.obj ≅ I'.obj :=
--     let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
--     have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
--       let fwd := f I I' ; let bck := f I' I
--       rw[∃!(⊥⟶) (fwd ▷ bck)]
--       rw[∃!(⊥⟶) 𝟙]
--     Isomorphic.mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

--   def products_iso {A B : 𝓒.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
--     let f (P P' : A × B) : P.obj ⟶ P'.obj := ⟨fst,snd⟩
--     have proof (P P' : A × B) : f P P' ▷ f P' P = 𝟙 := by
--       let fwd := f P P' ; let bck := f P' P
--       rw [← ∃!(⟶×) (fwd ▷ bck)]
--       repeat rw [(▷)▷=▷(▷)]
--       dsimp [bck]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
--       dsimp [fwd]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
--       rw [← 𝟙▷ fst, ← 𝟙▷ snd]
--       exact ∃!(⟶×) 𝟙
--     Isomorphic.mk (f P P') (f P' P) ⟨proof P P', proof P' P⟩

-- end Category
