
notation "~(" L "," R ")" => ⟨ L , R ⟩

inductive sigmaprop (T:Type _)(P:T -> Prop) : Type _
| mksprop : (t:T) -> P t -> sigmaprop T P



def sigmaprop.fst : sigmaprop A f -> A
| .mksprop a _ => a

def sigmaprop.snd : (p:sigmaprop A f) -> f p.fst
| .mksprop _ p => p

@[simp]
def sigmaprop_eta : (a : sigmaprop A p) -> (p: p a.fst) -> a = .mksprop a.fst p := by
  intro a _
  cases a
  exact rfl

@[reducible]
def iscoh_wmap {A:Type _}{B:Type _} : (A -> B) -> Type _ :=
  fun f => sigmaprop (B -> A) fun r => ∀ i , i = r (f i)
def wmap : Type _ -> Type _ -> Type _ :=
  fun A B => @Sigma (A -> B) fun f => iscoh_wmap f

def mkwmap (f:A->B)(h:B->A)(p:∀ a, a = h (f a)) : wmap A B := .mk f (.mksprop h p)

def quof {A:Type _}{B:Type _} : (A -> B) -> Type _ := fun f =>
  ∀ a:A , sigmaprop B fun i => f a = i

def quor {A:Type _}{B:Type _} : (B -> A) -> Type _ := fun f =>
  ∀ a:A , sigmaprop B fun i => f i = a

def p2 : (w:wmap A B) -> let (.mk f _) := w; ∀ a:A , sigmaprop B fun i => f a = i :=
  fun ~(f, (.mksprop _ _)) a => .mksprop (f a) rfl

def p1 : (p:wmap A B) -> let (.mk _ (.mksprop f _)) := p ; ∀ a:A , sigmaprop B fun i => f i = a :=
  fun ~(f, (.mksprop _ r)) a => .mksprop (f a) (Eq.symm (r a))



def iscoh_iso : wmap A B -> Prop :=
  fun (.mk f (.mksprop h _)) => ∀ i , i = f (h i)

def iso : Type _ -> Type _ -> Type _ :=
  fun A B => sigmaprop (wmap A B) iscoh_iso

def mkiso (f:A->B)(h:B->A)(p1:∀ i, i = f (h i))(p2:∀ i, i = h (f i)) : iso A B := .mksprop (.mk f (.mksprop h p2)) p1

def invert_iso : iso A B -> iso B A :=
  fun (.mksprop (.mk f ~(h, p1)) p2) => .mksprop (.mk h ~(f , p2)) p1


def p3 : (p:iso A B) -> let (.mksprop (.mk f _) _) := p; ∀ i:A , sigmaprop B fun b => f i = b :=
  fun (.mksprop (.mk f _) _) a => .mksprop (f a) rfl

def comp_iso : iso A B -> iso B C -> iso A C := by
  intros i1 i2
  let (.mksprop (.mk f (.mksprop h p1)) p2) := i1
  let (.mksprop (.mk f2 (.mksprop h2 p12)) p22) := i2
  unfold iso
  refine .mksprop (.mk ?_ (.mksprop ?_ ?_)) ?_
  intro a
  exact f2 (f a)
  intro c
  exact h (h2 c)
  intro a
  rw [<- p12, <- p1]
  simp [iscoh_iso] at *
  intro c
  rw [<- p2, <- p22]



def isotobiwmap (i:iso A B) : Prod (wmap A B) (wmap B A) := by
  let (.mksprop (.mk f ~(h , p1)) p2) := i
  refine Prod.mk ?a ?b
  {
    refine mkwmap ?to ?fr ?coh
    exact f
    exact h
    intro i
    apply p1
  }
  {
    refine .mk ?_ (.mksprop ?_ ?_)
    exact h
    exact f
    intro i
    apply p2
  }


def comp (w1:wmap A B)(w2:wmap B C): wmap A C := by
  let (.mk f1 (.mksprop h1 p1)) := w1
  let (.mk f2 (.mksprop h2 p2)) := w2
  refine mkwmap ?_ ?_ ?_
  intro a
  exact f2 (f1 a)
  intro c
  exact h1 (h2 c)
  intro a
  rw [<-p2, <-p1]
