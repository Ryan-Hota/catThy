-- TODO set operator precedences

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
          cases h1 with | intro τ₁ h1 =>
          cases h1 with | intro τ₂ h1 =>
          cases h2 with | intro τ₃ h2 =>
          cases h2 with | intro τ₄ h2 =>
          exists τ₁ ▷ τ₃, τ₄ ▷ τ₂
          refine And.intro ?_ ?_
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
      cases h₁ with | intro τ₁ h₁ =>
      cases h₁ with | intro τ₂ h₁ =>
      cases h₂ with | intro τ₃ h₂ =>
      cases h₂ with | intro τ₄ h₂ =>
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
      refine And.intro ?_ ?_
      . apply NatTransform.ext
        conv => lhs; change (fun a => (τ₃.component _ ▷ g₂.Mor _) ▷ (τ₄.component _ ▷ g₁.Mor _))
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
        conv => lhs; change (fun a => (τ₄.component _ ▷ g₁.Mor _) ▷ (τ₃.component _ ▷ g₂.Mor _))
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
      exact @Setoid.refl _ (FuncSetoid _ _) _
    all_goals (
      dsimp [seqQuot]
      intro X Y f
      induction f using Quotient.ind
      rename_i a
      apply Quotient.sound
      exact @Setoid.refl _ (FuncSetoid _ _) _
    )

end CategoryOfCategories
