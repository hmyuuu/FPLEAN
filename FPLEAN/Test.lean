import Mathlib.Topology.Basic

#check TopologicalSpace

#eval 1 + 2 * 3

#eval String.append "hello " "Lean!"

#eval ( 1 - 2 : Int )

def add1 (x : Nat) : Nat := x + 1

#eval add1 5

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n


#eval maximum 5 6

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

-- Exercises 1.3.1
def joinStringsWith (m : String) (f : String) (l : String) : String :=
  f ++ " " ++ m ++ " " ++ l

#eval joinStringsWith ", " "one" "and another"

-- Exercises 1.3.2
#check joinStringsWith ":"

-- Exercises 1.3.3
def volum (h : Nat) (w : Nat) (d : Nat) : Nat :=
  h * w * d

#eval volum 3 4 5


abbrev N : Type := Nat

def thirtyNine : N := 39



structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)

#eval origin.x

#eval distance origin { x := 3.0, y := 4.0 }

#check { x := 0.0, y := 0.0 : Point}

def zeroX (p : Point) : Point :=
  { p with x := 0 }

-- Constrcutors
#check Point.mk 1.5 2.8

#check Point.mk

structure Point1 where
  point ::
  x : Float
  y : Float
deriving Repr

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

-- Exercises 1.4.1
structure RectangularPrism where
  x : Float
  y : Float
  z : Float
deriving Repr

-- Exercises 1.4.2
def volume (p : RectangularPrism) : Float :=
  p.x * p.y * p.z

-- Exercises 1.4.3
structure Segment where
  start_point : Point
  end_point : Point
deriving Repr

def length (s : Segment) : Float :=
  distance s.start_point s.end_point

-- Exercises 1.4.4
#check RectangularPrism.x
#check RectangularPrism.y
#check RectangularPrism.z

-- Exercises 1.4.5
structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Hamster.name
#check Hamster.fluffy

#check Book.title
#check Book.author
#check Book.price

inductive myNat where
  | zero : myNat
  | succ (n : Nat) : myNat

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 203

-- Structural Recursion
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 5

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')


def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

-- div 需要手动证明停机
-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then
--     0
--   else Nat.succ (div (n - k) k)


structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check replaceX
#check replaceX Nat
#eval replaceX Nat natOrigin 2

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos

-- List
def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive myList (α : Type) where
  | nil : myList α
  | cons (head : α) (tail : myList α) : myList α

def myNatList : myList Nat := myList.cons 1 (myList.cons 2 (myList.cons 3 (myList.nil)))
def myStringList : myList String := myList.cons "hello" (myList.cons "world" (myList.nil))

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
#eval explicitPrimesUnder10 == primesUnder10

def mylength (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ ( mylength α ys )

#eval mylength Nat primesUnder10

-- Implicit Arguments

def replaceXP {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
#eval replaceXP natOrigin 2

def mylengthP {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ ( mylength α ys )
#eval mylengthP primesUnder10

-- List.length
#eval primesUnder10.length

#check List.length (α := Int )

-- Built-In Datatypes
-- Option

inductive myOption (α : Type) : Type where
  | none : myOption α
  | some (val : α) : myOption α

-- `Option`s in Lean allow multiple players of optionality

def List.myhead {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

#check List.head?
#check List.head!
#check List.headD

#eval primesUnder10.head?
#eval [].head? (α := Int)
#eval ([] : List Int).head?

-- Prod
structure myProd (α : Type) (β : Type) : Type where
  fst : α
  snd : β

def fives : String × Int := { fst := "five", snd := 5}
-- def fives : String × Int := { "five", 5}

-- Sum
inductive mySum (α : Type) (β : Type) : Type where
  | inl : α → mySum α β -- left injection
  | inr : β → mySum α β -- right injection

def PetName : Type := String ⊕ String

def hajimii : List PetName :=
  [Sum.inl "Sopt", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs hajimii

-- Unit
inductive myUnit : Type where
  | unit : myUnit
-- used as a placeholder for missing data

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

def giveMeAZero (_ : Unit) := 0
#eval giveMeAZero ()

-- Empty
#check Empty

-- Exercises 1.6.1
-- ref:  https://github.com/leanprover/lean4/blob/702c31b8071269f0052fd1e0fb3891a079a655bd/src/Init/Data/List/Basic.lean#L255-L257
def getLast? (xs : List α) : Option α :=
  match xs with
  | [] =>  none
  | [x] => some x
  | _ :: ys => getLast? ys
#eval getLast? primesUnder10


-- Exercises 1.6.2

-- Exercises 1.6.3

-- Exercises 1.6.4

-- Exercises 1.6.5

-- Exercises 1.6.6

-- Exercises 1.6.7

-- Exercises 1.6.8
