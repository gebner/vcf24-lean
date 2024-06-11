-- universes
#check (Prop : Type)
#check (Type : Type 1)
#check (Type 1 : Type 2) -- ...

-- dependent function types
#check ∀ n, Fin n → Fin n
#check (n : Nat) → Fin n → Fin n

-- lambdas
#check fun n (i : Fin n) => i + i

-- let
#check
  let i := 42
  -- indentation-sensitive syntax!
  i + i

-- pattern matching
#check
  match [42] with
  | [] => true
  | _ => false

-- definitions
def emptyList {α : Type u} : List α := []

-- pattern matching and recursion
def map {α β} (f : α → β) : List α → List β
  | [] => []
  | x::xs => f x :: map f xs

def map' {α β} (f : α → β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x::xs => f x :: map f xs

-- no subtyping
def natAsInt (n : Nat) : Int :=
  n
#print natAsInt

-- inductive types
inductive MyList (α : Type u)
  | nil
  | cons (x : α) (xs : MyList α)

structure MyPair (α : Type u) (β : Type v) where
  fst : α
  snd : β

def myPair1 : MyPair Nat String :=
  MyPair.mk 1 "b"

def myPair2 : MyPair Nat String :=
  { fst := 1, snd := "b" }

def myPair3 : MyPair Nat String where
  fst := 1
  snd := "b"

def myPair4 : MyPair Nat String :=
  -- ⟨⟩ picks the unique constructor for the expected type (MyPair ...)
  ⟨1, "b"⟩

def myPair5 : MyPair Nat Nat :=
  -- .mk looks up the name mk in the expected type (MyType + mk)
  .mk 1 3

def MyPair.add (p : MyPair Nat Nat) :=
  p.fst + p.2

#eval myPair5.add -- field notation looks up in the namespace of the type


class MyOp (α : Type u) where
  myOp : α → α

instance : MyOp Nat where
  myOp n := n + 42


-- equality
#check 1 = 2            -- propositional equality
#check 1 == 2           -- Boolean equality
#check HEq 1 ""         -- heterogeneous equality

#check (1 = 2 : Bool)
#check (1 == 2 : Prop)
