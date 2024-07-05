
notation "~(" L "," R ")" => ⟨ L , R ⟩

inductive sigmaprop (T:Type _)(P:T -> Prop) : Type _
| mksprop : (t:T) -> P t -> sigmaprop T P


def sigmaprop.fst : sigmaprop A f -> A
| .mksprop a _ => a


def sigmaprop.snd : (p:sigmaprop A f) -> f p.fst
| .mksprop _ p => p

def iscoh_wmap {A:Type _}{B:Type _} : (A -> B) -> Type _ := fun f => sigmaprop (B -> A) fun r => ∀ a , a = r (f a)
def wmap : Type _ -> Type _ -> Type _ := fun A B => @Sigma (A -> B) fun f => iscoh_wmap f



def quof {A:Type _}{B:Type _} : (A -> B) -> Type _ := fun f =>
  ∀ a:A , sigmaprop B fun i => f a = i

def quor {A:Type _}{B:Type _} : (B -> A) -> Type _ := fun f =>
  ∀ a:A , sigmaprop B fun i => f i = a

def p2 : (w:wmap A B) -> let (.mk f _) := w; ∀ a:A , sigmaprop B fun i => f a = i := by
  intros p a;
  let (Sigma.mk f k) := p;
  simp at k
  let (.mksprop h r) := k
  exact (.mksprop (f a) rfl)

def p1 : (p:wmap A B) -> let (.mk _ (.mksprop f _)) := p ; ∀ a:A , sigmaprop B fun i => f i = a := by
  intros p a;
  let (Sigma.mk f k) := p;
  simp at k
  let (.mksprop h r) := k
  exact (.mksprop (f a) (Eq.symm (r a)))


def iscoh_fmap {A:Type _}{B:Type _}: (A -> B) -> Type _ :=
  fun f => sigmaprop (B -> A) fun h => (∀ a , h (f a) = a) ∧ (∀ b , f (h b) = b)
def iso : Type _ -> Type _ -> Type _ :=
  fun A B => @Sigma (A -> B) fun f => iscoh_fmap f

def mkiso : (f:A -> B) -> (h:B->A) -> (∀ a:A , h (f a) = a) -> (∀ b:B , f (h b) = b) -> iso A B :=
  fun f h p1 p2 => .mk f (.mksprop h ~(p1,p2))


def invert : iso A B -> iso B A :=
  fun (.mk f (.mksprop h ~(p1, p2))) => .mk h (.mksprop f ~(p2 , p1))


def p3 : (p:iso A B) -> ∀ a:A , sigmaprop B fun b => p.fst a = b := by
  intro p
  let (.mk f _) := p
  simp
  intro a
  refine .mksprop (f a) rfl
