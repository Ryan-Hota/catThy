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

  notation " ⊥ " => Initial
  notation " ∃!(⊥⟶) " => Initial.proof_unique _

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
  notation "⟨" f ", " g "⟩"  => Product.pair _ f g
  notation " ∃(⟶×) " => Product.proof_exists _
  notation " ∃!(⟶×) " => Product.proof_unique _

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
  notation "[" f ", " g "]"  => Coproduct.either _ f g

  structure Exponential (A B : ℂ.Obj) where
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
          curry ((g × 𝟙) ▷ eval) = g

  infixl : 80 " ⟹ " => Exponential
  notation "∀obj,∃×" => Exponential.all_products _
  notation "ε" => Exponential.eval _

-----------------------------------------------------------------------

  theorem eq_id_left  {X : ℂ.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝟙 :=
      (▷𝟙 _).symm.trans (h X 𝟙)

  theorem eq_id_right {X : ℂ.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
      (𝟙▷ _).symm.trans (h X 𝟙)

  def inits_iso (I I' : @Initial ℂ) : I.obj ≅ I'.obj :=
    let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
    have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
      let fwd := f I I' ; let bck := f I' I
      rw[∃!(⊥⟶) (fwd ▷ bck)]
      rw[∃!(⊥⟶) 𝟙]
    Isomorphic.mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

  def products_iso {A B : ℂ.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
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

end CategoryTheory

-------------------------------------------------------------------------------------------

--# We shall now try implementing some categories.

--# Category Template

-- namespace CategoryName

--   open CategoryTheory

--   def ℂ : Category :=
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
    let Object : Sort _ := Nat
    let hom : Object -> Object -> Sort _ := Divides
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
    Category.mk Object hom seq @assoc id id_left id_right


end DivCategory

-------------------------------------------------------------------------------------------

namespace CategoryOfCategories

  open CategoryTheory

  structure Functor.{u} (A B : Category.{u}) where
    mk ::
      map_obj : A.Obj -> B.Obj
      map_mor {x y : A.Obj} : x ⟶ y -> map_obj x ⟶ map_obj y
      proof {x y z : A.Obj}
        : ∀ (f : x ⟶ y) (g : y ⟶ z), map_mor (f ▷ g) = map_mor f ▷ map_mor g


  def ℂ : Category :=
    let Object : Sort _ := Category.{0}
    let hom : Object -> Object -> Sort _ := Functor
    let seq {x y z : Object} : hom x y -> hom y z -> hom x z := fun f1 f2 =>
      have map_obj := f2.map_obj ∘ f1.map_obj
      let map_mor {p q : x.Obj} := f2.map_mor ∘ (@f1.map_mor p q)
      have proof {p q r : x.Obj}
        : ∀ (f : p ⟶ q) (g : q ⟶ r), map_mor (f ▷ g) = map_mor f ▷ map_mor g := by
          intro f g
          dsimp [map_mor]
          have h2 := f2.proof (f1.map_mor f) (f1.map_mor g)
          rw [← (f1.proof f g)] at h2
          exact h2
      Functor.mk map_obj map_mor proof
    have assoc {w x y z : Object} {f : hom w x} {g : hom x y} {h: hom y z}
      : seq (seq f g) h = seq f (seq g h) := by simp [seq, hom]; rfl
    let id {x : Object} : hom x x := Functor.mk id id (fun f g => rfl)
    have id_left  {x y : Object} (f : hom x y) : seq id f = f := by simp [id, seq, hom]
    have id_right {x y : Object} (f : hom x y) : seq f  id = f := by simp [id, seq, hom]
    Category.mk Object hom seq @assoc id id_left id_right

end CategoryOfCategories
