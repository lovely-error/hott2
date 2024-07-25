
import Simptt.core


def iscontr : Type _ -> Type _ := fun T => sigmaprop T (fun cc => (i:T) -> i = cc)

def min_ps {P:T->Prop} : iscontr T -> (∀ i , P i) = (∃ i , P i) := by
  intro cp
  let (.mksprop cc cp) := cp
  let to : ((i:T) -> P i) -> (∃ i , P i) := fun f => ~( cc , f cc )
  let from_ : (∃ i , P i) -> (i:T) -> P i := fun ~( v2 , p ) k => by
    let eq : v2 = cc := cp v2
    let eq1 : k = cc := cp k
    let eq2 : k = v2 := by
      rw [eq]
      rw [eq1]
    rw [eq2]
    exact p
  exact Eq.propIntro to from_

def cntr_funsp : iscontr T -> iscontr (T -> T) := by
  intro cpf
  let (.mksprop cc cp) := cpf
  unfold iscontr
  exact (.mksprop id fun f => by
    funext k
    rw [cp k]
    simp
    generalize (f cc) = v
    rw [cp v]
  )

def no_autos : iscontr T -> ∀ f:T->T , f = id := by
  intros cp f
  let (.mksprop cc cf) := cp
  let ex : ∃ (f : T -> T) , f cc = cc := ~(id , by simp)
  funext k
  rw [cf k]
  simp
  let ac : ∀ (f : T -> T) , f cc = cc := by
    rw [min_ps (cntr_funsp cp)]
    exact ex
  exact (ac _)


inductive path : {A :Type _} -> {B:Type _} -> A -> B -> Type _
| refl : {k:A} -> path k k
| iso : (f : A -> B) -> (h : B -> A) -> path (f a) b -> path (h b) a -> path a b


def glued_equiv {A B : Type}{a:A}{b:B} : path a b := .iso (fun _ => b) (fun _ => a) .refl .refl

def is_glue : path a b -> Prop := fun i =>
  match i with
  | .refl => false
  | m@(.iso _ _ _ _) => m = glued_equiv

def glued_p : A -> B -> Type _ := fun a b => sigmaprop (path a b) fun i => is_glue i

def glue_p_cc : glued_p a b := .mksprop glued_equiv (by unfold is_glue; simp; unfold glued_equiv; simp)

def glue_p_contr : iscontr (glued_p a b) := .mksprop glue_p_cc fun (.mksprop bcc p) => by
  unfold glue_p_cc
  cases bcc
  . cases p
  . unfold glued_equiv; cases p
    . rfl

def idmap : (∀ a , f a = a) -> f = id := by
  intro p
  funext k
  rw [p k]
  simp

def act_id {f h : A->A} : (∀ a , h (f a) = a) -> ∀ i , h (f i) = id i := by
  intro p i
  rw [p i]
  simp

def act_id2 {f h : A->A} : (∀ a , a = h (f a)) -> ∀ i , h (f i) = id i := by
  intro p i
  rw [<- p i]
  simp

def no_conf {f h:A->A}{a b:A}: (∀ a, h (f a) = a) -> a = h (f b) -> a = b := by
  intro p k
  let eq1 := act_id p b
  rw [eq1] at k
  exact k


def fiber : (A -> B) -> B -> Type _ := fun f m => sigmaprop A fun i => f i = m
def isweq {A:Type _}{B:Type _}: (A -> B) -> Type _ := fun f => ∀ i , iscontr (fiber f i)
def weq : Type _ -> Type _ -> Type _ := fun A B => @Sigma (A -> B) fun f => isweq f

def weqquor : (w:weq A B) -> quor w.fst := by
  intro (.mk f p)
  unfold isweq at p
  simp
  unfold quor
  intro b
  exact (p b).fst



def idwmap {T:Type _} : wmap T T := .mk id (.mksprop id fun i => @rfl _ i)

def contrsp_contr_maps : iscontr T -> iscontr (wmap T T) := by
  intro k
  unfold iscontr
  refine .mksprop ?_ ?_
  exact idwmap
  intro ~(f, (.mksprop h p))
  let rr1 := no_autos k f
  subst rr1
  let rr2 := no_autos k h
  subst rr2
  unfold idwmap
  rfl





def iso_triangle : iso A B -> iso C B -> iso A C := by
  intro m1 m2
  let (.mksprop (.mk f1 (.mksprop h1 k1)) p1) := m1
  let (.mksprop (.mk f2 (.mksprop h2 k2)) p2) := m2
  unfold iscoh_iso at p1 p2
  simp at p1 p2
  unfold iso
  refine .mksprop ?_ ?_
  {
    unfold wmap
    refine mkwmap ?_ ?_ ?_
    intro a
    exact h2 (f1 a)
    intro c
    exact h1 (f2 c)
    intro a
    rw [<- p2, <- k1]
  }
  unfold iscoh_iso mkwmap
  simp
  intro i
  rw [<- p1, <- k2]
