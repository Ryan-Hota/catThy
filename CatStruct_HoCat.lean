namespace CategoryTheory

  @[ext]
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
  notation "𝟙" => Category.id _
  notation "𝟙▷" => Category.id_left _
  notation "▷𝟙" => Category.id_right _

  -----------------------------------------------------------------------

  @[ext]
  structure Terminal.{u_1, u_2} {𝓒 : Category.{u_1, u_2}} : Type (max u_1 u_2) where
    obj : 𝓒.Obj
    unique_from (X : _Obj) : X ⟶ obj
    proof_unique {X : _Obj} : ∀ f : X ⟶ obj, f = unique_from X

  infixr : 100 " ⊤ " => Terminal

  @[ext]
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

  def times.{u_1, u_2} {𝓒 : Category.{u_1, u_2}}
    {D D' C C' : 𝓒.Obj}
    {Prod_of_Ds : D × D'}
    {Prod_of_Cs : C × C'}
    (f : D ⟶ C) (f' : D' ⟶ C')
    : Prod_of_Ds.obj ⟶ Prod_of_Cs.obj :=
      ⟨_fst ▷ f, _snd ▷ f'⟩

  infixl : 80 " × " => times

  @[ext]
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

  @[ext]
  structure Func.{u_1, u_2} (𝓐 𝓑 : Category.{u_1, u_2}) : Type (max u_1 u_2) where
    Obj : 𝓐.Obj → 𝓑.Obj
    Mor {X Y : 𝓐.Obj} : X ⟶ Y → Obj X ⟶ Obj Y
    proof_id {X : 𝓐.Obj} : Mor (@𝓐.id X) = 𝟙
    proof_comp {X Y Z : 𝓐.Obj} :
      ∀ (f : X ⟶ Y) (g : Y ⟶ Z), Mor (f ▷ g) = Mor f ▷ Mor g

  @[ext]
  structure NatTransform.{u_1, u_2} {𝓐 𝓑 : Category.{u_1, u_2}} (F G : Func 𝓐 𝓑) : Type (max u_1 u_2) where
    component : (a : 𝓐.Obj) → F.Obj a ⟶ G.Obj a
    proof {X Y : 𝓐.Obj} :
      ∀ f : X ⟶ Y, F.Mor f ▷ component Y = component X ▷ G.Mor f

  @[ext]
  structure CartesianClosedCategory.{u_1, u_2} (𝓒 : Category.{u_1, u_2}) : Type (max u_1 u_2) where
    terminal : @Terminal 𝓒
    prod (A B : 𝓒.Obj) : Product A B
    exp  (A B : 𝓒.Obj) : Exponential A B

end CategoryTheory


namespace FunctorCategory

  open CategoryTheory

  def FuncCat {𝓐 𝓑 : Category} : Category := {
    Obj := Func 𝓐 𝓑
    Hom f g := NatTransform f g
    seq τ₁ τ₂ := {
      component a := τ₁.component a ▷ τ₂.component a 
      proof := by 
        intros
        rw [← Category.assoc, NatTransform.proof, Category.assoc, 
          NatTransform.proof, ← Category.assoc]
    }
    assoc := by 
      intros
      simp only [NatTransform.mk.injEq]
      ext
      rw [Category.assoc]
    id := {
      component a := 𝓑.id 
      proof := by grind only [𝟙▷, ▷𝟙]
    }
    id_left := by intros; ext; simp only; exact 𝓑.id_left _
    id_right := by intros; ext; simp only; exact 𝓑.id_right _
  }

end FunctorCategory


namespace CategoryOfCategories

  open CategoryTheory
  open FunctorCategory

  -- # Here, we shall attempt to analyse Ho(Cat), the homotopy category of categories
  -- # https://youtu.be/fec8qSBiM4k
  -- # Objects are categories, and Hom(𝓐, 𝓑) is [𝓐, 𝓑] quotiented by natural isomorphism.

  def FuncSetoid (𝓐 𝓑) : Setoid (Func 𝓐 𝓑) := {
      r f g := ∃ (τ₁ : FuncCat.Hom f g) (τ₂ : FuncCat.Hom g f), τ₁ ▷ τ₂ = 𝟙 ∧ τ₂ ▷ τ₁ = 𝟙
      iseqv := by 
        constructor
        . intros
          exists FuncCat.id, FuncCat.id
          grind only [←𝟙▷]
        . intro f g h
          grind only
        . intro f1 f2 f3 h1 h2
          let (Exists.intro τ₁ (Exists.intro τ₂ h1)) := h1
          let (Exists.intro τ₃ (Exists.intro τ₄ h2)) := h2
          exists τ₁ ▷ τ₃, τ₄ ▷ τ₂
          refine ⟨?_, ?_⟩
          . rw [Category.assoc]
            conv in (FuncCat.seq τ₃ _) => rw [← Category.assoc]
            rw [h2.left, ← 𝟙▷, h1.left]
          . rw [Category.assoc]
            conv in (FuncCat.seq τ₂ _) => rw [← Category.assoc]
            rw [h1.right, ← 𝟙▷, h2.right]
    }

  def seq.{u} {𝓧 𝓨 𝓩 : Category.{u, u}} : Func 𝓧 𝓨 → Func 𝓨 𝓩 → Func 𝓧 𝓩 := fun F G =>
    {
      Obj := G.Obj ∘ F.Obj
      Mor := G.Mor ∘ F.Mor
      proof_id := by
        simp [F.proof_id, G.proof_id]
      proof_comp := by
        intro _ _ _ f g
        have h2 := G.proof_comp (F.Mor f) (F.Mor g)
        rw [← (F.proof_comp f g)] at h2
        exact h2
    }

  theorem seqAssoc {𝓦 𝓧 𝓨 𝓩} (f : Func 𝓦 𝓧) (g : Func 𝓧 𝓨) (h : Func 𝓨 𝓩) : 
    seq (seq f g) h = seq f (seq g h) := by
      simp [seq]
      exact ⟨rfl, rfl⟩  

  def seqQuot {𝓧 𝓨 𝓩} : 
    Quotient (FuncSetoid 𝓧 𝓨) → Quotient (FuncSetoid 𝓨 𝓩) → Quotient (FuncSetoid 𝓧 𝓩) :=
      Quotient.lift₂ (fun f g => Quotient.mk _ (seq f g)) ?_
    where finally
      intro f₁ g₁ f₂ g₂ h₁ h₂
      apply Quotient.sound
      let (Exists.intro τ₁ (Exists.intro τ₂ h₁)) := h₁
      let (Exists.intro τ₃ (Exists.intro τ₄ h₂)) := h₂
      exists ?_, ?_
      . exact {
          component a := τ₃.component (f₁.Obj a) ▷ g₂.Mor (τ₁.component a)
          proof := by 
            dsimp [seq]
            intros
            conv => rhs; rw [Category.assoc, ←g₂.proof_comp, ←τ₁.proof, g₂.proof_comp]
            conv => lhs; rw [←Category.assoc, τ₃.proof, Category.assoc]
        }
      . exact {
          component a := τ₄.component (f₂.Obj a) ▷ g₁.Mor (τ₂.component a)
          proof := by
            dsimp [seq]
            intros
            conv => rhs; rw [Category.assoc, ←g₁.proof_comp, ←τ₂.proof, g₁.proof_comp]
            conv => lhs; rw [←Category.assoc, τ₄.proof, Category.assoc]
        }
      refine ⟨?_, ?_⟩
      . apply NatTransform.ext
        conv => lhs; change (fun a => 𝓩.seq _ _)
        ext; rename_i a
        dsimp [seq]
        rw [←τ₃.proof, Category.assoc]
        conv =>
          lhs
          pattern (τ₃.component _) ▷ _
          rw [←Category.assoc]
          pattern (τ₃.component _) ▷ _
          change (τ₃ ▷ τ₄).component _
          rw [h₂.left]
          change 𝟙
        rw [←𝟙▷, ←g₁.proof_comp]
        conv => 
          lhs
          change g₁.Mor ((τ₁ ▷ τ₂).component a)
          rw [h₁.left]
          change g₁.Mor 𝟙
          rw [g₁.proof_id]
        rfl
      . apply NatTransform.ext
        conv => lhs; change (fun a => 𝓩.seq _ _)
        ext; rename_i a
        dsimp [seq]
        rw [←τ₄.proof, Category.assoc]
        conv =>
          lhs
          pattern (τ₄.component _) ▷ _
          rw [←Category.assoc]
          pattern (τ₄.component _) ▷ _
          change (τ₄ ▷ τ₃).component _
          rw [h₂.right]
          change 𝟙
        rw [←𝟙▷, ←g₂.proof_comp]
        conv => 
          lhs
          change g₂.Mor ((τ₂ ▷ τ₁).component a)
          rw [h₁.right]
          change g₂.Mor 𝟙
          rw [g₂.proof_id]
        rfl

  def HoCat.{u} : Category.{u+1, u} := {
    Obj := Category.{u, u}
    Hom 𝓐 𝓑 := Quotient (FuncSetoid 𝓐 𝓑)
    seq := seqQuot 
    assoc := ?_
    id := Quotient.mk _ (.mk id id (by simp) (fun _ _ => rfl))
    id_left := ?_
    id_right := ?_
  }
  where finally
    . dsimp [seqQuot]
      intro W X Y Z f g h
      induction f using Quotient.ind
      induction g using Quotient.ind
      induction h using Quotient.ind
      rename_i a b c
      apply Quotient.sound
      rw [seqAssoc]
      exact (FuncSetoid _ _).refl _
    all_goals (
      dsimp [seqQuot]
      intro X Y f
      induction f using Quotient.ind
      rename_i a
      apply Quotient.sound
      exact (FuncSetoid _ _).refl _
    )

  def HoCat.terminal.{u} : Terminal (𝓒 := HoCat.{u}) := {
    obj := {
      Obj := PUnit
      Hom := fun _ _ => PUnit
      seq := fun _ _ => PUnit.unit
      assoc := fun {W X Y Z} {f g h} => PUnit.eq_punit PUnit.unit
      id := PUnit.unit
      id_left := by simp only [implies_true]
      id_right := by simp only [implies_true]
    }
    unique_from := fun _ => Quotient.mk _ {
      Obj := fun _ => PUnit.unit
      Mor := fun _ => PUnit.unit
      proof_id := by simp only [implies_true]
      proof_comp := by simp only [implies_true]
    }
    proof_unique := by
      intro _ f
      induction f using Quotient.ind
      apply Quotient.sound
      exact (FuncSetoid _ _).refl _
  }

  def HoCat.prod.obj.{u} (𝓐 𝓑 : HoCat.{u}.Obj) : HoCat.{u}.Obj := {
    Obj := 𝓐.Obj × 𝓑.Obj
    Hom := fun (w,x) (y,z) => (w ⟶ y) × (x ⟶ z)
    seq := fun a b => (a.fst ▷ b.fst, a.snd ▷ b.snd)
    assoc := by
      simp only [Prod.mk.injEq, Prod.forall]
      intros; expose_names
      rw [Category.assoc, Category.assoc]
      exact ⟨rfl, rfl⟩
    id := (𝟙, 𝟙)
    id_left := by simp only [← 𝟙▷, implies_true]
    id_right := by simp only [← ▷𝟙, implies_true]
  }

  def HoCat.prod.fst.{u} (𝓐 𝓑 : HoCat.{u}.Obj) : prod.obj 𝓐 𝓑 ⟶ 𝓐 := Quotient.mk _ {
    Obj := Prod.fst
    Mor := Prod.fst
    proof_id := by simp only [implies_true, obj]
    proof_comp := by simp only [implies_true, obj]
  }

  def HoCat.prod.snd.{u} (𝓐 𝓑 : HoCat.{u}.Obj) : prod.obj 𝓐 𝓑 ⟶ 𝓑 := Quotient.mk _ {
    Obj := Prod.snd
    Mor := Prod.snd
    proof_id := by simp only [implies_true, obj]
    proof_comp := by simp only [implies_true, obj]
  }

  def HoCat.prod.pair.{u} (𝓐 𝓑 : HoCat.{u}.Obj) {𝓧} : 
    Quotient (FuncSetoid 𝓧 𝓐) → Quotient (FuncSetoid 𝓧 𝓑) → 𝓧 ⟶ (prod.obj 𝓐 𝓑) := 
      Quotient.lift₂ (fun f g => Quotient.mk _ {
          Obj := fun x => (f.Obj x, g.Obj x)
          Mor := fun x => (f.Mor x, g.Mor x)
          proof_id := by
            simp only [Prod.mk.injEq, prod.obj]
            intros
            rw [f.proof_id, g.proof_id]
            exact ⟨rfl, rfl⟩
          proof_comp := by 
            simp only [Prod.mk.injEq, prod.obj]
            intros; expose_names
            rw [f.proof_comp, g.proof_comp]
            exact ⟨rfl, rfl⟩
        }) ?_
    where finally
      intro a₁ b₁ a₂ b₂ ha hb
      apply Quotient.sound
      let (Exists.intro τ₁ (Exists.intro τ₂ h₁)) := ha
      let (Exists.intro τ₃ (Exists.intro τ₄ h₂)) := hb
      clear ha hb
      dsimp at h₁ h₂
      exists ?_, ?_
      . exact {
          component a := (τ₁.component a, τ₃.component a)
          proof := by 
            simp only
            dsimp [obj]
            intros
            rw [τ₁.proof, τ₃.proof]
        }
      . exact {
          component a := (τ₂.component a, τ₄.component a)
          proof := by 
            simp only
            dsimp [obj]
            intros
            rw [τ₂.proof, τ₄.proof]
        }
      refine ⟨?_, ?_⟩
      all_goals
        apply NatTransform.ext
        change (fun a => (prod.obj 𝓐 𝓑).seq _ _) = _
        dsimp [obj]
        ext
        all_goals
          rename_i a
          dsimp
          conv =>
            lhs
            try change (τ₁ ▷ τ₂).component a
            try change (τ₃ ▷ τ₄).component a
            try change (τ₂ ▷ τ₁).component a
            try change (τ₄ ▷ τ₃).component a
          simp [h₁.left, h₁.right, h₂.left, h₂.right]
          rfl

  def HoCat.prod.{u} (𝓐 𝓑 : HoCat.{u}.Obj) : 𝓐 × 𝓑 := {
    obj := prod.obj 𝓐 𝓑
    fst := prod.fst 𝓐 𝓑
    snd := prod.snd 𝓐 𝓑
    pair := prod.pair 𝓐 𝓑
    proof_exists := by
      intros; expose_names
      refine ⟨?_, ?_⟩
      all_goals
        induction fa using Quotient.ind
        induction fb using Quotient.ind
        apply Quotient.sound
        exact (FuncSetoid _ _).refl _
    proof_unique := by
      intros; expose_names
      induction g using Quotient.ind
      apply Quotient.sound
      exact (FuncSetoid _ _).refl _
  }

  def HoCat.exp.curry.f.{u} {𝓐 𝓑 𝓧 : HoCat.{u}.Obj} (F : Func (prod 𝓧 𝓐).obj 𝓑) :
     HoCat.Hom 𝓧 (@FuncCat 𝓐 𝓑) :=
      let h := @F.proof_id
      Quotient.mk _ { 
        Obj := fun x => {
          Obj := fun a => F.Obj (x, a)
          Mor := fun f => F.Mor (𝟙, f)
          proof_id := by
            simp only [prod, prod.obj, Prod.forall] at h
            simp only [h, implies_true]
          proof_comp := by simp only [prod, ← F.proof_comp, ← 𝟙▷, implies_true, prod.obj]
        }
        Mor := fun f => {
          component := fun _ => F.Mor (f, 𝟙)
          proof := by simp only [prod, ← F.proof_comp, ← 𝟙▷, ← ▷𝟙, implies_true, prod.obj]
        }
        proof_id := by
          simp only [prod, prod.obj, Prod.forall] at h
          simp only [h]
          intros; rfl
        proof_comp := by 
          simp only [prod, prod.obj]
          intros
          apply NatTransform.ext
          simp only
          change _ = fun x => 𝓑.seq _ _
          simp only
          ext; rename_i a
          simp only [← F.proof_comp, prod, prod.obj, ← 𝟙▷]
      }

  theorem HoCat.exp.curry.proof.{u} {𝓐 𝓑 𝓧 : HoCat.{u}.Obj} (F G : Func (prod 𝓧 𝓐).obj 𝓑) : 
    (@FuncSetoid _ _).r F G → curry.f F = curry.f G := by 
      intro h
      dsimp [f]
      apply Quotient.sound
      let (Exists.intro τ₁ (Exists.intro τ₂ h₁)) := h
      clear h; dsimp at h₁
      exists ?_, ?_
      . exact {
          component x := {
            component a := τ₁.component (x, a)
            proof := by 
              intros
              simp only
              rw [τ₁.proof]
          }
          proof := by
            intros
            apply NatTransform.ext
            change (fun x => 𝓑.seq _ _) = _
            change _ = fun x => 𝓑.seq _ _
            ext; rw [τ₁.proof]
        }
      . exact {
          component x := {
            component a := τ₂.component (x, a)
            proof := by 
              intros
              simp only
              rw [τ₂.proof]
          }
          proof := by
            intros
            apply NatTransform.ext
            change (fun x => 𝓑.seq _ _) = _
            change _ = fun x => 𝓑.seq _ _
            ext; rw [τ₂.proof]
        }
      refine ⟨?_, ?_⟩
      all_goals
        apply NatTransform.ext
        change (fun x => FuncCat.seq _ _) = _
        simp
        ext; rename_i x
        apply NatTransform.ext
        change (fun a => 𝓑.seq _ _) = _
        ext; rename_i a
        conv =>
          lhs
          try change (τ₁ ▷ τ₂).component _
          try change (τ₂ ▷ τ₁).component _
        simp [h₁.left, h₁.right]
        rfl

  def HoCat.exp.curry.{u} {𝓐 𝓑 𝓧 : HoCat.{u}.Obj} : 
    (prod.{u} 𝓧 𝓐).obj ⟶ 𝓑 → 𝓧 ⟶ (@FuncCat 𝓐 𝓑) := 
      Quotient.lift curry.f curry.proof

  def HoCat.exp.eval.{u} {𝓐 𝓑 : HoCat.{u}.Obj} : 
    (prod (@FuncCat 𝓐 𝓑) 𝓐).obj ⟶ 𝓑 := Quotient.mk _ {
      Obj := fun p => p.fst.Obj p.snd
      Mor := @fun p q r => p.fst.Mor r.snd ▷ r.fst.component q.snd
      proof_id := by
        simp only [prod, prod.obj, Func.proof_id, ← 𝟙▷, Prod.forall]
        intros; rfl
      proof_comp := by
        simp only [prod, Prod.forall, prod.obj]
        intros; expose_names
        rw [a.proof_comp]
        have h1 := a_3.proof b_4
        rw [𝓑.assoc]
        conv in 𝓑.seq (a.Mor b_4) _ =>
          change 𝓑.seq _ (𝓑.seq _ _)
          rw [← 𝓑.assoc, h1]
        repeat rw [𝓑.assoc]
    }

  theorem HoCat.exp.proof_exists {𝓐 𝓑 𝓧} (F : HoCat.Hom (prod 𝓧 𝓐).obj 𝓑) : 
    HoCat.seq (exp.curry F × HoCat.id) exp.eval = F := by 
      induction F using Quotient.ind
      rename_i F
      apply Quotient.sound
      refine Quotient.exact (congrArg _ ?_)
      ext <;> simp only [prod, prod.obj, seq, Function.comp_apply, Function.id_comp, id_eq,
        heq_eq_eq]
      . rfl
      . ext
        simp only [Function.comp_apply, ← F.proof_comp, prod, prod.obj, ← 𝟙▷, ← ▷𝟙]

  theorem HoCat.exp.proof_unique {𝓐 𝓑 𝓧 : HoCat.Obj} (F : HoCat.Hom 𝓧 (@FuncCat 𝓐 𝓑)) : 
    F = exp.curry (HoCat.seq (F × HoCat.id) exp.eval) := by 
      induction F using Quotient.ind
      rename_i F
      apply Quotient.sound
      simp [prod, prod.obj, seq,]
      exists ?_, ?_
      . exact {
          component x := {
            component a := 𝟙
            proof := by
              intros
              simp only [← ▷𝟙, Func.proof_id, ← 𝟙▷]
              conv in FuncCat.id.component _ => change 𝟙
              simp only [← ▷𝟙]
          }
          proof := by 
            intros
            apply NatTransform.ext
            change (fun a => 𝓑.seq _ _) = _
            change _ = fun a => 𝓑.seq _ _
            simp only [← ▷𝟙, Func.proof_id, ← 𝟙▷]
        }
      . exact {
          component x := {
            component a := 𝟙
            proof := by
              intros
              simp only [← ▷𝟙, Func.proof_id, ← 𝟙▷]
              conv in FuncCat.id.component _ => change 𝟙
              simp only [← ▷𝟙]
          }
          proof := by 
            intros
            apply NatTransform.ext
            change (fun a => 𝓑.seq _ _) = _
            change _ = fun a => 𝓑.seq _ _
            simp only [← ▷𝟙, Func.proof_id, ← 𝟙▷]
        }
      refine ⟨?_, ?_⟩
      all_goals
        apply NatTransform.ext
        change (fun x => FuncCat.seq _ _) = _
        ext
        apply NatTransform.ext
        change (fun a => 𝓑.seq _ _) = _
        ext
        simp only [← 𝟙▷]
        rfl

  def HoCat.exp.{u} (𝓐 𝓑 : HoCat.{u}.Obj) : 𝓐 ⟹ 𝓑 := {
    obj := @FuncCat 𝓐 𝓑
    any_product X := prod X 𝓐
    curry := exp.curry
    eval := exp.eval
    proof_exists := exp.proof_exists
    proof_unique := exp.proof_unique
  }

  def HoCat_is_CCC.{u} : CartesianClosedCategory HoCat.{u} := {
    terminal := HoCat.terminal
    prod := HoCat.prod
    exp := HoCat.exp
  }

end CategoryOfCategories
