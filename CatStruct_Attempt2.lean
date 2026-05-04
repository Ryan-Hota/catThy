-- TODO set operator precedences

set_option profiler true

namespace CategoryTheory

  structure Category.{u_1, u_2} : Type (max u_1 u_2 + 1) where
    Obj : Type u_1
    Hom : Obj → Obj → Type u_2
    seq {X Y Z : Obj} : Hom X Y → Hom Y Z → Hom X Z
    assoc {W X Y Z : Obj} {f : Hom W X} {g : Hom X Y} {h: Hom Y Z}
      : seq (seq f g) h = seq f (seq g h)
    id {X : Obj} : Hom X X
    id_left  {X Y : Obj} (f : Hom X Y) : f = seq id f
    id_right {X Y : Obj} (f : Hom X Y) : f = seq f  id

  notation "_Obj" => Category.Obj _
  infixr : 60 " ⟶ " => Category.Hom _
  infixl : 70 " ▷ " => Category.seq _
  -- notation "▷assoc" => Category.assoc _
  -- TODO notation "▷(▷)=(▷)▷" => (Category.assoc _).symm
  notation "𝟙" => Category.id _
  notation "𝟙▷" => Category.id_left _
  notation "▷𝟙" => Category.id_right _

  -----------------------------------------------------------------------

  structure Isomorphic.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} (A B : 𝓒.Obj) where
    fwd : A ⟶ B
    bck : B ⟶ A
    proof : fwd ▷ bck = 𝟙 ∧ bck ▷ fwd = 𝟙

  infixr : 70 " ≅ " => Isomorphic

  structure Initial.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} : Type (max u_1 u_2) where
    obj : 𝓒.Obj
    unique_to (X : _Obj) : obj ⟶ X
    proof_unique {X : _Obj} : ∀ f : obj ⟶ X, f = unique_to X

  notation "⊥" => Initial
  notation "∃!(⊥⟶)" => Initial.proof_unique _

  structure Terminal.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} : Type (max u_1 u_2) where
    obj : 𝓒.Obj
    unique_from (X : _Obj) : X ⟶ obj
    proof_unique {X : _Obj} : ∀ f : X ⟶ obj, f = unique_from X

  infixr : 100 " ⊤ " => Terminal

  structure Product.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} (A B : 𝓒.Obj) : Type (max u_1 u_2) where
    obj : _Obj
    fst : obj ⟶ A
    snd : obj ⟶ B
    pair {X : _Obj} : X ⟶ A → X ⟶ B → X ⟶ obj
    proof_exists {X : _Obj} :
      ∀ fa : X ⟶ A, ∀ fb,
        pair fa fb ▷ fst = fa ∧ pair fa fb ▷ snd = fb
    proof_unique {X : _Obj} : ∀ g : X ⟶ obj,
        g = pair (g ▷ fst) (g ▷ snd)

  infixr : 80 " × " => Product
  notation "_fst" => Product.fst _
  notation "_snd" => Product.snd _
  notation "⟨"f","g"⟩"  => Product.pair _ f g
  notation "∃(⟶×)" => Product.proof_exists _
  notation "∃!(⟶×)" => Product.proof_unique _

  def times.{u_1, u_2} {𝓒 : Category.{u_1, u_2}}
    {D D' C C' : 𝓒.Obj}
    {Prod_of_Ds : D × D'}
    {Prod_of_Cs : C × C'}
    (f : D ⟶ C) (f' : D' ⟶ C')
    : Prod_of_Ds.obj ⟶ Prod_of_Cs.obj :=
      ⟨_fst ▷ f, _snd ▷ f'⟩

  infixl : 80 " × " => times

  structure Coproduct.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} (A B : 𝓒.Obj) : Type (max u_1 u_2) where
    obj : _Obj
    inl : A ⟶ obj
    inr : B ⟶ obj
    either {X : _Obj} : A ⟶ X → B ⟶ X → obj ⟶ X
    proof_exists {X :_Obj} :
      ∀ fa : A ⟶ X,
        ∀ fb : B ⟶ X,
          inl ▷ either fa fb = fa ∧ inr ▷ either fa fb = fb
    proof_unique {X : _Obj} :
      ∀ g : obj ⟶ X,
        g = either (inl ▷ g) (inr ▷ g)

  infixr : 75 " + " => Coproduct
  notation "_inl" => Coproduct.inl _
  notation "_inr" => Coproduct.inr _
  notation "["f","g"]"  => Coproduct.either _ f g

  structure Exponential.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} (A B : 𝓒.Obj) : Type (max u_1 u_2) where
    obj : _Obj
    any_product : (X : _Obj) → X × A
    curry {X : _Obj} : (any_product X).obj ⟶ B → X ⟶ obj
    eval : (any_product obj).obj ⟶ B
    proof_exists {X : _Obj} :
      ∀ f : (any_product X).obj ⟶ B ,
        (curry f × 𝟙) ▷ eval = f
    proof_unique {X : _Obj} :
      ∀ g : X ⟶ obj ,
        g = curry ((g × 𝟙) ▷ eval)

  infixl : 80 " ⟹ " => Exponential
  notation "_×" => Exponential.any_product _
  notation "_curry" => Exponential.curry _
  notation "∃(⟶⟹)" => Exponential.proof_exists _
  notation "∃!(⟶⟹)" => Exponential.proof_unique _
  notation "ε" => Exponential.eval _

  structure Func.{u_1, u_2} (𝓐 𝓑 : Category.{u_1, u_2}) : Type (max u_1 u_2) where
    Obj : 𝓐.Obj → 𝓑.Obj
    Mor {X Y : 𝓐.Obj} : X ⟶ Y → Obj X ⟶ Obj Y
    proof {X Y Z : 𝓐.Obj} :
      ∀ (f : X ⟶ Y) (g : Y ⟶ Z), Mor (f ▷ g) = Mor f ▷ Mor g

  structure NatTransform.{u_1, u_2} {𝓐 𝓑 : Category.{u_1, u_2}} (F G : Func 𝓐 𝓑) : Type (max u_1 u_2) where
    component : (a : 𝓐.Obj) → F.Obj a ⟶ G.Obj a
    proof {X Y : 𝓐.Obj} :
      ∀ f : X ⟶ Y, F.Mor f ▷ component Y = component X ▷ G.Mor f

  structure CartesianClosedCategory.{u_1, u_2} (𝓒 : Category.{u_1, u_2}) : Type (max u_1 u_2) where
    terminal : @Terminal 𝓒
    prod (A B : 𝓒.Obj) : Product A B
    exp  (A B : 𝓒.Obj) : Exponential A B

-----------------------------------------------------------------------

  theorem eq_id_left.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : X ⟶ Y, e ▷ f = f) : e = 𝟙 :=
      (▷𝟙 _).trans (h X 𝟙)

  theorem eq_id_right.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {X : 𝓒.Obj} {e : X ⟶ X}
    (h : ∀ Y, ∀ f : Y ⟶ X, f ▷ e = f) : e = 𝟙 :=
      (𝟙▷ _).trans (h X 𝟙)

  def inits_iso.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} (I I' : @Initial 𝓒) : I.obj ≅ I'.obj :=
    let f (I I' : ⊥) : I.obj ⟶ I'.obj := I.unique_to I'.obj
    have proof (I I' : ⊥) : f I I' ▷ f I' I = 𝟙 := by
      let fwd := f I I' ; let bck := f I' I
      rw[∃!(⊥⟶) (fwd ▷ bck)]
      rw[∃!(⊥⟶) 𝟙]
    .mk (f I I') (f I' I) ⟨proof I I', proof I' I⟩

  def products_iso.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {A B : 𝓒.Obj} (P P' : A × B) : P.obj ≅ P'.obj :=
    let f (P P' : A × B) : P.obj ⟶ P'.obj := ⟨_fst, _snd⟩
    have proof (P P' : A × B) : f P P' ▷ f P' P = 𝟙 := by
      let fwd := f P P' ; let bck := f P' P
      rw [∃!(⟶×) (fwd ▷ bck)]
      repeat rw [𝓒.assoc]
      dsimp [bck]; rw[(∃(⟶×) _fst _snd).left, (∃(⟶×) _fst _snd).right]
      dsimp [fwd]; rw[(∃(⟶×) _fst _snd).left, (∃(⟶×) _fst _snd).right]
      rw [𝟙▷ _fst, 𝟙▷ _snd]
      exact (∃!(⟶×) 𝟙).symm
    .mk (f P P') (f P' P) ⟨proof P P', proof P' P⟩

  theorem pair_seq.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {A B C1 C2 : 𝓒.Obj} {P : C1 × C2}
  : ∀ f (g : B ⟶ _) h, f▷⟨g,h⟩ = (⟨f▷g,f▷h⟩ : A ⟶ P.obj) := by
    intro f g h
    rw[∃!(⟶×) (f▷⟨g,h⟩)]
    repeat rw[𝓒.assoc]
    rw[(∃(⟶×) g h).left, (∃(⟶×) g h).right]

  theorem times_seq.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {X0 X1 X2 Y0 Y1 Y2 : 𝓒.Obj}
    {P0 : X0 × Y0} {P1 : X1 × Y1} {P2 : X2 × Y2}
    : ∀ {a : X0 ⟶ X1} {b : Y0 ⟶ Y1} {c : X1 ⟶ X2} {d : Y1 ⟶ Y2},
    ((a×b : _ ⟶ P1.obj)▷(c×d)) = ((a▷c)×(b▷d) : P0.obj ⟶ P2.obj) := by
    intro a b c d
    dsimp[times]
    rw[pair_seq]
    repeat rw[← 𝓒.assoc]
    rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]

  def exps_iso.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {A B : 𝓒.Obj} (E E' : B ⟹ A) : E.obj ≅ E'.obj :=
    let f (E E' : B ⟹ A) : E.obj ⟶ E'.obj := _curry ( ( 𝟙 × 𝟙 ) ▷ ε )
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
      rw[𝟙▷ (_curry ( ( 𝟙 × 𝟙 ) ▷ ε ))]
      rw[← times_seq]
      rw[𝓒.assoc]
      rw[∃(⟶⟹) _]
      rw[← 𝓒.assoc]
      rw[times_seq]
      repeat rw[← ▷𝟙]
      rw[← ∃!(⟶⟹) 𝟙]
    .mk (f E E') (f E' E) ⟨proof E E', proof E' E⟩

  def exp_dist_prod.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} {A B C : 𝓒.Obj}
  (AxB : A × B) (AxBeC : C ⟹ AxB.obj)
  (AeC : C ⟹ A) (BeC : C ⟹ B) (AeCxBeC : AeC.obj × BeC.obj)
  : AxBeC.obj ≅ AeCxBeC.obj :=
    let curry' {X : _Obj} : _ → X ⟶ _ := fun f =>
      ⟨_curry ((𝟙×𝟙)▷f▷_fst), _curry ((𝟙×𝟙)▷f▷_snd)⟩
    let eval' := ⟨(_fst × 𝟙)▷ε, (_snd × 𝟙)▷ε⟩
    have proof_exists' := by
      intro X f
      dsimp[curry', eval']
      rw[pair_seq]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq]
      repeat rw[(∃(⟶×) _ _).left, (∃(⟶×) _ _).right]
      rw[𝟙▷ (_curry ((𝟙×𝟙)▷f▷_fst))]
      rw[𝟙▷ (_curry ((𝟙×𝟙)▷f▷_snd))]
      repeat rw[← times_seq]
      repeat rw[𝓒.assoc]
      repeat rw[∃(⟶⟹) _]
      repeat rw[← 𝓒.assoc]
      repeat rw[times_seq]
      repeat rw[← 𝟙▷ 𝟙]
      repeat rw[← ∃!(⟶×) _]
      dsimp[times]
      repeat rw[← ▷𝟙]
      rw[𝟙▷ _fst, 𝟙▷ _snd]
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



namespace CategoryOfCategories

  open CategoryTheory

  -- TODO : Switch direction of things like Functor.proof, 𝟙▷, ▷𝟙

  /--
    `Cat.{u}` is the category of all `Category.{u, u}` categories.
  -/
  def Cat.{u} : Category.{u + 1, u} :=
    let seq {𝓧 𝓨 𝓩 : Category} : Func 𝓧 𝓨 → Func 𝓨 𝓩 → Func 𝓧 𝓩 := fun F G =>
      let FG_Obj : 𝓧.Obj → 𝓩.Obj := G.Obj ∘ F.Obj
      let FG_Mor {A B : 𝓧.Obj}
        : A ⟶ B → FG_Obj A ⟶ FG_Obj B := G.Mor ∘ F.Mor
      have proof {P Q R : 𝓧.Obj}
        : ∀ (f : P ⟶ Q) (g : Q ⟶ R), FG_Mor (f ▷ g) = FG_Mor f ▷ FG_Mor g := by
          intro f g
          dsimp [FG_Mor]
          have h2 := G.proof (F.Mor f) (F.Mor g)
          rw [← (F.proof f g)] at h2
          exact h2
      .mk FG_Obj FG_Mor proof
    have assoc := by simp; exact ⟨rfl, rfl⟩
    let id {𝓧 : Category} : Func 𝓧 𝓧 := .mk id id (fun _ _ => rfl)
    have id_left  := by simp
    have id_right := by simp
    .mk Category.{u, u} Func seq assoc id id_left id_right

  def Cat.terminal.{u} : Terminal (𝓒 := Cat.{u}) := {
    obj := {
      Obj := PUnit
      Hom := fun _ _ => PUnit
      seq := fun _ _ => PUnit.unit
      assoc := fun {W X Y Z} {f g h} => PUnit.eq_punit PUnit.unit
      id := PUnit.unit
      id_left := fun {X Y} f => PUnit.eq_punit f
      id_right := fun {X Y} f => PUnit.eq_punit f
    }
    unique_from := fun _ => {
      Obj := fun _ => PUnit.unit
      Mor := fun _ => PUnit.unit
      proof := fun {X Y Z} f g => PUnit.eq_punit PUnit.unit
    }
    proof_unique := by intros; rfl
  }

  def Cat.prod.{u} (𝓐 𝓑 : Cat.{u}.Obj) : 𝓐 × 𝓑 := {
    obj := {
      Obj := 𝓐.Obj × 𝓑.Obj
      Hom := fun (w,x) (y,z) => (w ⟶ y) × (x ⟶ z)
      seq := fun a b => (a.fst ▷ b.fst, a.snd ▷ b.snd)
      assoc := by
        simp [𝓐.assoc, 𝓑.assoc]
      id := (𝟙, 𝟙)
      id_left := by simp [← 𝟙▷]
      id_right := by simp [← ▷𝟙]
    }
    fst := {
      Obj := Prod.fst
      Mor := Prod.fst
      proof := by simp
    }
    snd := {
      Obj := Prod.snd
      Mor := Prod.snd
      proof := by simp
    }
    pair := fun f g => {
      Obj := fun x => (f.Obj x, g.Obj x)
      Mor := fun x => (f.Mor x, g.Mor x)
      proof := by simp [f.proof, g.proof]
    }
    proof_exists := by
      intros
      refine And.intro ?_ ?_
      all_goals rfl
    proof_unique := by intros; rfl
  }

  def Cat.exp.obj.{u} (𝓐 𝓑 : Cat.{u}.Obj) : Cat.Obj := {
    Obj := Func 𝓐 𝓑
    Hom := fun F G => NatTransform F G
    seq := fun τ₁ τ₂ => {
      component := fun a => τ₁.component a ▷ τ₂.component a
      proof := by
        simp only [𝓑.assoc, ← τ₂.proof]
        simp only [← 𝓑.assoc, τ₁.proof, implies_true]
    }
    assoc := by simp only [𝓑.assoc, implies_true]
    id := {
      component := fun x => 𝟙
      proof := by grind only [𝟙▷, ▷𝟙]
    }
    id_left := by simp only [← 𝟙▷, implies_true]
    id_right := by simp only [← ▷𝟙, implies_true]
  }

  def Cat.exp.curry.{u} {𝓐 𝓑 : Cat.{u}.Obj} {𝓧 : Cat.Obj} :
    Cat.Hom (prod 𝓧 𝓐).obj 𝓑 → Cat.Hom 𝓧 (obj 𝓐 𝓑) := fun F => {
        Obj := fun x => {
          Obj := fun a => F.Obj (x, a)
          Mor := fun f => F.Mor (𝟙, f)
          proof := by simp only [prod, ← F.proof, ← 𝟙▷, implies_true]
        }
        Mor := fun f => {
          component := fun _ => F.Mor (f, 𝟙)
          proof := by simp only [prod, ← F.proof, ← 𝟙▷, ← ▷𝟙, implies_true]
        }
        proof := by simp only [prod, ← F.proof, ← 𝟙▷, implies_true, obj]
      }

  def Cat.exp.eval.{u} {𝓐 𝓑 : Cat.{u}.Obj} :
    Cat.Hom (prod (obj 𝓐 𝓑) 𝓐).obj 𝓑 := {
        Obj := fun p => p.fst.Obj p.snd
        Mor := @fun p q r => p.fst.Mor r.snd ▷ r.fst.component q.snd
        proof := by
          simp only [prod, Prod.forall, obj]
          intros; expose_names
          rw [a.proof]
          have h1 := a_3.proof b_4
          rw [𝓑.assoc]
          conv in 𝓑.seq (a.Mor b_4) _ => rw [←𝓑.assoc, h1]
          repeat rw [𝓑.assoc]
      }

  def Cat.exp.proof_exists.{u} {𝓐 𝓑 : Cat.{u}.Obj} :
    ∀ {𝓧 : Cat.Obj} (f : Cat.Hom (prod 𝓧 𝓐).obj 𝓑), Cat.seq (curry f × Cat.id) eval = f := sorry

  def Cat.exp.proof_unique.{u} {𝓐 𝓑 : Cat.{u}.Obj} :
    ∀ {𝓧 : Cat.Obj} (g : Cat.Hom 𝓧 (obj 𝓐 𝓑)), g = curry (Cat.seq (g × Cat.id) eval) := sorry

  /--
  For any `u`, the category of all `Category.{u, u}` categories is cartesian closed.
  -/
  def Cat_is_CC.{u} : CartesianClosedCategory Cat.{u} :=
    {
      terminal := Cat.terminal
      prod := Cat.prod
      exp := fun 𝓐 𝓑 => {
        obj := Cat.exp.obj 𝓐 𝓑
        any_product := fun 𝓧 => Cat.prod 𝓧 𝓐
        curry := Cat.exp.curry
        eval := Cat.exp.eval
        proof_exists := Cat.exp.proof_exists
        proof_unique := Cat.exp.proof_unique
      }
    }

end CategoryOfCategories
