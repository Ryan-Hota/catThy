-- TODO set operator precedences

namespace CategoryTheory

  structure Category.{u, v} where
    Obj : Sort u
    Hom : Obj → Obj → Sort v
    seq {X Y Z : Obj} : Hom X Y → Hom Y Z → Hom X Z
    assoc {W X Y Z : Obj} {f : Hom W X} {g : Hom X Y} {h: Hom Y Z}
      : seq (seq f g) h = seq f (seq g h)
    id {X : Obj} : Hom X X
    id_left  {X Y : Obj} (f : Hom X Y) : f = seq id f
    id_right {X Y : Obj} (f : Hom X Y) : f = seq f  id

  notation "Obj" => Category.Obj _
  infixr : 60 " ⟶ " => Category.Hom _
  infixl : 70 " ▷ " => Category.seq _
  -- notation "▷assoc" => Category.assoc _
  -- TODO notation "▷(▷)=(▷)▷" => (Category.assoc _).symm
  notation "𝟙" => Category.id _
  notation "𝟙▷" => Category.id_left _
  notation "▷𝟙" => Category.id_right _

  -----------------------------------------------------------------------

  variable {𝓒 : Category}

  structure Isomorphic (A B : 𝓒.Obj) where
    fwd : A ⟶ B
    bck : B ⟶ A
    proof : fwd ▷ bck = 𝟙 ∧ bck ▷ fwd = 𝟙

  infixr : 70 " ≅ " => Isomorphic

  structure Initial where
    obj : 𝓒.Obj
    unique_to (X : Obj) : obj ⟶ X
    proof_unique {X : Obj} : ∀ f : obj ⟶ X, f = unique_to X

  notation "⊥" => Initial
  notation "∃!(⊥⟶)" => Initial.proof_unique _

  structure Terminal where
    obj : 𝓒.Obj
    unique_from (X : Obj) : X ⟶ obj
    proof_unique {X : Obj} : ∀ f : X ⟶ obj, f = unique_from X

  infixr : 100 " ⊤ " => Terminal

  structure Product (A B : 𝓒.Obj) where
    obj : Obj
    fst : obj ⟶ A
    snd : obj ⟶ B
    pair {X : Obj} : X ⟶ A → X ⟶ B → X ⟶ obj
    proof_exists {X : Obj} :
      ∀ fa : X ⟶ A, ∀ fb,
        pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
    proof_unique {X : Obj} : ∀ g : X ⟶ obj,
        g = pair (g ▷ fst) (g ▷ snd)

  infixr : 80 " × " => Product
  notation "fst" => Product.fst _
  notation "snd" => Product.snd _
  notation "⟨"f","g"⟩"  => Product.pair _ f g
  notation "∃(⟶×)" => Product.proof_exists _
  notation "∃!(⟶×)" => Product.proof_unique _

  def times
    {D D' C C' : 𝓒.Obj}
    {Prod_of_Ds : D × D'}
    {Prod_of_Cs : C × C'}
    (f : D ⟶ C) (f' : D' ⟶ C')
    : Prod_of_Ds.obj ⟶ Prod_of_Cs.obj :=
      ⟨fst ▷ f, snd ▷ f'⟩

  infixl : 80 " × " => times

  structure Coproduct (A B : 𝓒.Obj) where
    obj : Obj
    inl : A ⟶ obj
    inr : B ⟶ obj
    either {X : Obj} : A ⟶ X → B ⟶ X → obj ⟶ X
    proof_exists {X : Obj} :
      ∀ fa : A ⟶ X,
        ∀ fb : B ⟶ X,
          inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
    proof_unique {X : Obj} :
      ∀ g : obj ⟶ X,
        g = either (inl ▷ g) (inr ▷ g)

  infixr : 75 " + " => Coproduct
  notation "inl" => Coproduct.inl _
  notation "inr" => Coproduct.inr _
  notation "["f","g"]"  => Coproduct.either _ f g

   structure Func (𝓐 𝓑 : Category) where
    _Obj : 𝓐.Obj → 𝓑.Obj
    _Mor {X Y : 𝓐.Obj} : X ⟶ Y → _Obj X ⟶ _Obj Y
    proof {X Y Z : 𝓐.Obj} :
      ∀ (f : X ⟶ Y) (g : Y ⟶ Z), _Mor (f ▷ g) = _Mor f ▷ _Mor g

  structure NatTransform {𝓐 𝓑 : Category} (F G : Func 𝓐 𝓑) where
    component : (a : 𝓐.Obj) → F._Obj a ⟶ G._Obj a
    proof {X Y : 𝓐.Obj} :
      ∀ f : X ⟶ Y, F._Mor f ▷ component Y = component X ▷ G._Mor f

  structure Exponential (A B : 𝓒.Obj) where
    obj : Obj
    any_product (X : Obj) : X × A
    curry {X : Obj} : (any_product X).obj ⟶ B → X ⟶ obj
    eval : (any_product obj).obj ⟶ B
    proof_exists {X : Obj} :
      ∀ f : (any_product X).obj ⟶ B ,
        (curry f × 𝟙) ▷ eval = f
    proof_unique {X : Obj} :
      ∀ g : X ⟶ obj ,
        g = curry ((g × 𝟙) ▷ eval)

  infixl : 80 " ⟹ " => Exponential
  notation "_×" => Exponential.any_product _
  notation "curry" => Exponential.curry _
  notation "∃(⟶⟹)" => Exponential.proof_exists _
  notation "∃!(⟶⟹)" => Exponential.proof_unique _
  notation "ε" => Exponential.eval _

  structure CartesianClosedCategory (Cat : Category) where
    mk ::
      terminal : @Terminal Cat
      prod (A B : Cat.Obj) : Product A B
      exp  (A B : Cat.Obj) : Exponential A B

-----------------------------------------------------------------------

  theorem eq_id_left  {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝟙 :=
      (▷𝟙 _).trans (h X 𝟙)

  theorem eq_id_right {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
      (𝟙▷ _).trans (h X 𝟙)

  def inits_iso (I I' : @Initial 𝓒) : I.obj ≅ I'.obj :=
    let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
    have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
      let fwd := f I I' ; let bck := f I' I
      rw[∃!(⊥⟶) (fwd ▷ bck)]
      rw[∃!(⊥⟶) 𝟙]
    .mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

  def products_iso {A B : 𝓒.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
    let f (P P' : A × B) : P.obj ⟶ P'.obj := ⟨fst,snd⟩
    have proof (P P' : A × B) : f P P' ▷ f P' P = 𝟙 := by
      let fwd := f P P' ; let bck := f P' P
      rw [∃!(⟶×) (fwd ▷ bck)]
      repeat rw [𝓒.assoc]
      dsimp [bck]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      dsimp [fwd]; rw[(∃(⟶×) fst snd).left, (∃(⟶×) fst snd).right]
      rw [𝟙▷ fst, 𝟙▷ snd]
      exact (∃!(⟶×) 𝟙).symm
    .mk (f P P') (f P' P) ⟨proof P P', proof P' P⟩

  theorem pair_seq {A B C1 C2 : 𝓒.Obj} {P : C1 × C2}
  : ∀ f (g : B ⟶ _) h, f▷⟨g,h⟩ = (⟨f▷g,f▷h⟩ : A ⟶ P.obj) := by
    intro f g h
    rw[∃!(⟶×) (f▷⟨g,h⟩)]
    repeat rw[𝓒.assoc]
    rw[(∃(⟶×) g h).left, (∃(⟶×) g h).right]

  theorem times_seq {X0 X1 X2 Y0 Y1 Y2 : 𝓒.Obj}
    {P0 : X0 × Y0} {P1 : X1 × Y1} {P2 : X2 × Y2}
    : ∀ {a : X0 ⟶ X1} {b : Y0 ⟶ Y1} {c : X1 ⟶ X2} {d : Y1 ⟶ Y2},
    ((a×b : _ ⟶ P1.obj)▷(c×d)) = ((a▷c)×(b▷d) : P0.obj ⟶ P2.obj) := by
    intro a b c d
    dsimp[times]
    rw[pair_seq]
    repeat rw[← 𝓒.assoc]
    rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]

  def exps_iso {A B : 𝓒.Obj} (E E' : B ⟹ A) : E.obj ≅ E'.obj :=
    let f (E E' : B ⟹ A) : E.obj ⟶ E'.obj := curry ( ( 𝟙 × 𝟙 ) ▷ ε )
    have proof (E E' : B ⟹ A) : f E E' ▷ f E' E = 𝟙 := by
      rw[∃!(⟶⟹) (f E E' ▷ f E' E)]
      rw[𝟙▷ 𝟙]
      rw[← times_seq]
      rw[𝓒.assoc]
      dsimp[f]
      rw[∃(⟶⟹) _]
      rw[← 𝓒.assoc]
      rw[times_seq]
      rw[← ▷𝟙]
      rw[𝟙▷ (curry ( ( 𝟙 × 𝟙 ) ▷ ε ))]
      rw[← times_seq]
      rw[𝓒.assoc]
      rw[∃(⟶⟹) _]
      rw[← 𝓒.assoc]
      rw[times_seq]
      repeat rw[← ▷𝟙]
      rw[← ∃!(⟶⟹) 𝟙]
    .mk (f E E') (f E' E) ⟨proof E E', proof E' E⟩

  def exp_dist_prod {A B C : 𝓒.Obj}
  (AxB : A × B) (AxBeC : C ⟹ AxB.obj)
  (AeC : C ⟹ A) (BeC : C ⟹ B) (AeCxBeC : AeC.obj × BeC.obj)
  : AxBeC.obj ≅ AeCxBeC.obj :=
    let curry' {X : Obj} : _ → X ⟶ _ := fun f =>
      ⟨curry ((𝟙×𝟙)▷f▷fst), curry ((𝟙×𝟙)▷f▷snd)⟩
    let eval' := ⟨(fst × 𝟙)▷ε, (snd × 𝟙)▷ε⟩
    have proof_exists' := by
      intro X f
      dsimp[curry', eval']
      rw[pair_seq]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq]
      repeat rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]
      rw[𝟙▷ (curry ((𝟙×𝟙)▷f▷fst))]
      rw[𝟙▷ (curry ((𝟙×𝟙)▷f▷snd))]
      repeat rw[← times_seq]
      repeat rw[𝓒.assoc]
      repeat rw[∃(⟶⟹) _]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq]
      repeat rw[← 𝟙▷ 𝟙]
      repeat rw[← ∃!(⟶×) _]
      dsimp[times]
      repeat rw[← ▷𝟙]
      rw[𝟙▷ fst, 𝟙▷ snd]
      rw[← ∃!(⟶×) _]
      rw[← 𝟙▷]
    have proof_unique' := by
      intro X g
      dsimp[curry', eval']
      repeat rw[𝓒.assoc]
      rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq]
      repeat rw[← 𝟙▷]
      repeat rw[← ∃!(⟶⟹) _]
      rw[← ∃!(⟶×)]
    exps_iso AxBeC (.mk AeCxBeC.obj AxBeC.any_product curry' eval' proof_exists' proof_unique')

end CategoryTheory

-------------------------------------------------------------------------------------------

--# We shall now try implementing some categories.

--# Category Template

-- namespace CategoryName

--   open CategoryTheory

--   def ℂ : Category :=
--     let Object : Sort _ := sorry
--     let hom : Object → Object → Sort _ := sorry
--     let seq {x y z : Object} : hom x y → hom y z → hom x z := sorry
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

  def DividesPoset : Category :=
    let Object : Sort _ := Nat
    let hom : Object → Object → Sort _ := Divides
    have seq {x y z : Object} : hom x y → hom y z → hom x z := by
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
    .mk Object hom seq @assoc id id_left id_right

end DivCategory

-------------------------------------------------------------------------------------------

namespace CategoryOfCategories

  open CategoryTheory

  def Cat : Category :=
    let seq {𝓧 𝓨 𝓩 : Category} : Func 𝓧 𝓨 → Func 𝓨 𝓩 → Func 𝓧 𝓩 := fun F G =>
      let FG_Obj : 𝓧.Obj → 𝓩.Obj := G._Obj ∘ F._Obj
      let FG_Mor {A B : 𝓧.Obj}
        : A ⟶ B → FG_Obj A ⟶ FG_Obj B := G._Mor ∘ F._Mor
      have proof {P Q R : 𝓧.Obj}
        : ∀ (f : P ⟶ Q) (g : Q ⟶ R), FG_Mor (f ▷ g) = FG_Mor f ▷ FG_Mor g := by
          intro f g
          dsimp [FG_Mor]
          have h2 := G.proof (F._Mor f) (F._Mor g)
          rw [← (F.proof f g)] at h2
          exact h2
      .mk FG_Obj FG_Mor proof
    have assoc := by simp ; exact ⟨rfl, rfl⟩
    let id {𝓧 : Category} : Func 𝓧 𝓧 := .mk id id (fun _ _ => rfl)
    have id_left  := by simp
    have id_right := by simp
    .mk Category Func seq assoc id id_left id_right

  def Cat_is_CC : CartesianClosedCategory Cat :=
    let terminal :=
      .mk
        (.mk
          Unit
          (fun _ _ => Unit)
          (fun _ _ => ())
          (by simp only [implies_true])
          ()
          (by simp only [implies_true])
          (by simp only [implies_true])
        )
        (fun _ => .mk
          (fun _ => ())
          (fun _ => ())
          (by grind only)
        )
        (by intro _ _; congr)
    let prod := fun 𝓐 𝓑 => .mk
      (.mk
        (𝓐.Obj × 𝓑.Obj)
        (fun (w,x) (y,z) => (w ⟶ y) × (x ⟶ z))
        (fun a b => (a.fst ▷ b.fst, a.snd ▷ b.snd))
        (by simp only [𝓐.assoc, 𝓑.assoc, implies_true])
        (𝟙, 𝟙)
        (by simp only [← 𝟙▷, implies_true])
        (by simp only [← ▷𝟙, implies_true])
      )
      (.mk
        (by simp only; exact fun a => a.fst)
        (by simp only [id_eq]; exact fun a => a.fst)
        (by simp only [id_eq, implies_true])
      )
      (.mk
        (by simp only; exact fun a => a.snd)
        (by simp only [id_eq]; exact fun a => a.snd)
        (by simp only [id_eq, implies_true])
      )
      (fun f g => .mk
        (fun x => (f._Obj x, g._Obj x))
        (fun x => (f._Mor x, g._Mor x))
        (by simp only [f.proof, g.proof, implies_true])
      )
      (by
        intro _ _ _
        refine And.intro ?_ ?_
        all_goals congr
      )
      (by intro _ _; congr)
    let exp := fun 𝓐 𝓑 => .mk
      (.mk
        (Func 𝓐 𝓑)
        (fun F G => NatTransform F G)
        (fun τ₁ τ₂ => .mk
          (fun a => τ₁.component a ▷ τ₂.component a)
          (by
            simp only [𝓑.assoc, ← τ₂.proof]
            simp only [← 𝓑.assoc, τ₁.proof, implies_true]
          )
        )
        (by simp only [𝓑.assoc, implies_true])
        (.mk (fun x => 𝟙) (by grind only [𝟙▷, ▷𝟙]))
        (by simp only [← 𝟙▷, implies_true])
        (by simp only [← ▷𝟙, implies_true])
      )
      (fun 𝓧 => prod 𝓧 𝓐)
      (fun F => .mk
        (fun x => .mk
          (fun a => F._Obj (x, a))
          (fun f => F._Mor (𝟙, f))
          (by simp only [id_eq, ← F.proof, ← 𝟙▷, implies_true, prod])
        )
        (fun f => .mk
          (fun _ => F._Mor (f, 𝟙))
          (by simp only [id_eq, ← F.proof, ← 𝟙▷, ← ▷𝟙, implies_true, prod])
        )
        (by simp only [id_eq, ← F.proof, ← 𝟙▷, implies_true, prod])
      )
      (.mk
        (by simp only [prod]; exact fun (F, a) => F._Obj a)
        (by simp only [id_eq, prod]; intro (F,_) (_,b) (τ, f); exact F._Mor f ▷ τ.component b)
        (by
          simp only [id_eq, NatTransform.proof, Func.proof, Category.assoc, Prod.forall, prod]
          intros
          simp only [← Category.assoc, NatTransform.proof]
        )
      )
      sorry
      sorry
    .mk terminal prod exp

end CategoryOfCategories
