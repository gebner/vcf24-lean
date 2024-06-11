/-

Lean does not have an effect system

Side-effects are represented using monads

-/

#check bind
#check pure

def func : IO Unit := do
  let r ← IO.mkRef 42
  r.set 10
  let x ← r.get
  IO.println x
#eval func

def desugared : IO Unit :=
  bind (IO.mkRef 42) fun r =>
  bind (r.set 10) fun _ =>
  bind r.get fun x =>
  IO.println x


def inlineBind : IO Unit := do
  IO.println (← (← IO.mkRef 42).get)


def mutable : IO Unit := do
  let mut x := 42
  x := 10
  IO.println x

def forIf : IO Unit := do
  let mut x := 42
  for i in [:100] do
    if i % 10 = 3 then
      x := x + i
  IO.println x



-- Non-IO monads
def state : StateM Nat Nat := do
  set ((← get) + 10)
  get
#eval state.run' 42

theorem state_result : state.run' 42 = 52 :=
  -- pure function!
  rfl


-- Monad stacks
def stack : ReaderT String (StateM String) String := do
  set ((← get) ++ ", " ++ (← read))
  get
#eval (stack.run "world").run' "hello"
