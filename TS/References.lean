import SFLMeta

import TS.Stlc
import TS.Smallstep
import LF.CustomTactics

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "References: Typing Mutable References" =>
%%%
tag := "References"
htmlSplit := .never
file := some "References"
%%%

::::instructors
The proof of preservation for this system is actually
very interesting.  It is given as an exercise, but if there's
enough class time it would be well worth devoting a lecture to
it!
::::

::::dev PotentialImprovement
The text in this chapter -- especially the terse version --
does not do a great job, early on, of connecting the concepts to
things that students will already know about. This makes the later
parts unnecessarily puzzling.  (Also, the terse slides have way too
much text and not NEARLY enough examples, quizzes, etc.)
Sampsa:
The exercise `factorial_ref` is tricky,
because the definition of `tseq` is unhygienic
with respect to the variable `x`.
Thus, the following does not work unless the variable `x` is renamed.

```
fact = λx : Nat , (λr : Ref (Nat → Nat) ,
  r := λx : Nat , if x == 0 then 1 else x * !r (pred x);
  !r x) (ref (λx : Nat , 0))
    ```

For the TERSE version, there are a bunch of slides in the
two 2006 Chapter 13 lectures that would be great to include
here.

The UPenn 2011 final exam has some good simple questions that
should be repeated here (question 5).

More of the exercises should be marked recommended.
::::

::::full
Up to this point, we have considered a variety of _pure_
language features, including functional abstraction, basic types
such as numbers and booleans, and structured types such as records
and variants.  These features form the backbone of most
programming languages -- including purely functional languages
such as Haskell and "mostly functional" languages such as ML, as
well as imperative languages such as C and object-oriented
languages such as Java, C#, and Scala.

Most practical languages also include various _impure_
features that cannot be described in the simple semantic framework
we have used so far.  In particular, besides just yielding
results, computation in these languages may assign to mutable
variables (reference cells, arrays, mutable record fields, etc.);
perform input and output to files, displays, or network
connections; make non-local transfers of control via exceptions,
jumps, or continuations; engage in inter-process synchronization
and communication; and so on.  In the literature on programming
languages, such "side effects" of computation are collectively
referred to as _computational effects_.

In this chapter, we'll see how one sort of computational effect --
mutable references -- can be added to the calculi we have studied.
The main extension will be dealing explicitly with a _store_ (or
_heap_) and _pointers_ that name store locations.  This extension
is fairly straightforward to define; the most interesting part is
the refinement we need to make to the statement of the type
preservation theorem.
::::

::::terse
Most real languages include _impure_ features
("computational effects")...
- mutable pointer structures
- non-local control constructs (exceptions, continuations, etc.)
- inter-process synchronization and communication
- etc.

Goal for this chapter: Formalize pointers.
::::

# Definitions

::::full
Pretty much every programming language provides some form of
assignment operation that changes the contents of a previously
allocated piece of storage.  (Lean is a rare exception!)

In some languages -- notably ML and its relatives -- the
mechanisms for name binding and those for assignment are kept
separate.  We can have a variable `x` whose _value_ is the number
`5`, or we can have a variable `y` whose value is a
_reference_ (or _pointer_) to a mutable cell whose current
contents is `5`.  These are different things, and the difference
is visible to the programmer.  We can add `x` to another number,
but not assign to it.  We can use `y` to assign a new value to the
cell that it points to (by writing `y:=84`), but we cannot use `y`
directly as an argument to an operation like `+`.  Instead, we
must explicitly _dereference_ it, writing `!y` to obtain its
current contents.

In most other languages -- in particular, in all members of the C
family, including Java -- _every_ variable name refers to a
mutable cell, and the operation of dereferencing a variable to
obtain its current contents is implicit.

For purposes of formal study, it is useful to keep these
mechanisms separate.  The development in this chapter will closely
follow ML's model.  Applying the lessons learned here to C-like
languages is a straightforward matter of collapsing some
distinctions and rendering some operations such as dereferencing
implicit instead of explicit.
::::

::::terse
In most real-world programming languages, the mechanisms of
_name binding_ and _storage allocation_ are (intentionally)
confused: every name refers to a mutable piece of storage.

Conceptually, it's cleaner to separate the two:
    - use the mechanisms we already have for name binding
      (abstraction, let);
    - introduce new operations for allocating, changing,
      and looking up the contents of references (pointers).
::::

## Syntax

::::full
In this chapter, we study adding mutable references to the
simply-typed lambda calculus with natural numbers.
::::

```lean
namespace STLCRef

open scoped MyGetElem
```

The basic operations on references are _allocation_,
_dereferencing_, and _assignment_.

- To allocate a reference, we use the `ref` operator, providing
  an initial value for the new cell.

  For example, `ref 5` creates a new cell containing the value
  `5` and reduces to a reference to that cell.

- To read the current value of this cell, we use the
  dereferencing operator [!].

  For example, `!(ref 5)` reduces to `5`.

- To change the value stored in a cell, we use the assignment
  operator.

  If `r` is a reference, `r := 7` will store the value `7` in
  the cell referenced by `r`.

## Types

::::full
We start with the simply typed lambda calculus over the
natural numbers. Besides the base natural-number type and arrow
types, we add two more types to deal with references. First, we
need the _unit type_, which we will use as the result type of an
assignment operation.  We then add _reference types_.
::::

If `τ` is a type, then `Ref τ` is the type of references to
cells holding values of type `τ`.

```bnf
τ ::= Nat
    | Unit
    | τ "→" τ
    | "Ref" τ ;
```

```lean
inductive Ty : Type :=
  | nat : Ty
  | unit : Ty
  | arrow : Ty → Ty → Ty
  | ref : Ty → Ty
```

## Terms

Besides the usual variables, abstractions, applications,
terms related to natural numbers, and `unit`, we need four
more sorts of terms to handle mutable references:

```bnf
t ::= "ref" t    ("reference")
    | "!"t       ("dereference")
    | t ":=" t   ("assignment")
    | l          ("location");
```

```lean
inductive Tm  : Type :=
  -- STLC with numbers:
  | var    : String → Tm
  | app    : Tm → Tm → Tm
  | abs    : String → Ty → Tm → Tm
  | const  : Nat → Tm
  | succ    : Tm → Tm
  | pred    : Tm → Tm
  | mult    : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- New terms:
  | unit   : Tm
  | ref    : Tm → Tm
  | deref  : Tm → Tm
  | assign : Tm → Tm → Tm
  | loc    : Nat → Tm
```

::::details "Notation"
```lean
scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:60 " * " stlcTm:61 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 stlcTm:60 " := " stlcTm:61 : stlcTm
scoped syntax:60 "Ref " stlcTy:61 : stlcTy
scoped syntax:60 "ref " stlcTm:61 : stlcTm
scoped syntax:60 "loc " stlcTm:61 : stlcTm
scoped syntax:60 "!" stlcTm:61 : stlcTm
scoped syntax:55 stlcTm:56 " ; " stlcTm:55 : stlcTm

abbrev Tm.tseq t₁ t₂ :=
  Tm.app (.abs "X" .unit t₂) t₁

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs
  -- defined later
  subst := `STLCRef.subst
  hasType := `STLCRef.HasType

def extendedTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | `(stlcTy| Unit) =>
        return mkConst ``Ty.unit
    | `(stlcTy| Ref $τ:stlcTy) => do
        let τ ← recur τ
        return mkApp (mkConst ``Ty.ref) τ
    | _ => k T

def tyHandlers : TyElabHandler :=
  extendedTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy <| unsupportedTy language

def extendedTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free )

    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."

    | `(stlcTm| succ $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.succ) t, free)

    | `(stlcTm| pred $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.pred) t, free)

    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) t₁ t₂, free)

    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)

    | `(stlcTm| Unit) => do
        throwError "`Unit` is not a valid term."

    | `(stlcTm| unit) => do
        return (mkConst ``Tm.unit, free)

    | `(stlcTm| ref $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.ref) t, free)

    | `(stlcTm| !$t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.deref) t, free)

    | `(stlcTm| loc $n:num) => do
        return (mkApp (mkConst ``Tm.loc) (mkNatLit n.getNat), free )

    | `(stlcTm| $t₁:stlcTm := $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.assign) t₁ t₂, free)

    | `(stlcTm| $t₁:stlcTm ; $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.tseq) t₁ t₂, free)

    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  extendedTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

def elabCtx : CtxElab := elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

end Elab

open scoped Elab

namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let Nat := mkObjectIdentFrom stx "Nat"
    let T ← `(stlcTy| $Nat:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
    let Unit := mkObjectIdentFrom stx "Unit"
    let T ← `(stlcTy| $Unit:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.ref]
private def Ty.unexpandRef : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ Ref $T':stlcTy }>)
  | _ => throw ()

private def reservedNames : String → Bool
  | "Nat" | "Unit" | "succ" | "pred"
  | "if0" | "ref" | "loc" | "Ref"
  | "unit" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.const]
private def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
private def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
      let succ := mkObjectIdentFrom stx "succ"
      let t' := getTm t
      `(<{ $succ:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
private def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
      let pred := mkObjectIdentFrom stx "pred"
      let t' := getTm t
      `(<{ $pred:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
private def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm * $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.tseq]
private def Tm.unexpandTseq : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm ; $t₂':stlcTm }>)
  | _ => throw ()


@[app_unexpander Tm.ite0]
private def Tm.unexpandIte0 : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{ if0 $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()


@[app_unexpander Tm.unit]
private def Tm.unexpandUnit : Unexpander
  | stx => do
      let unit := mkObjectIdentFrom stx "unit"
      let t ← `(stlcTm| $unit:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.assign]
private def Tm.unexpandAssign : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm := $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ref]
private def Tm.unexpandRef : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ ref $t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.deref]
private def Tm.unexpandDeref : Unexpander
  | `($_ $t₁) => do
      let t₁' := getTm t₁
      `(<{ !$t₁':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.loc]
private def Tm.unexpandLoc : Unexpander
  | `($_ $n:num) => `(<{ loc $n:num }>)
  | _ => throw ()


end Delab
```
::::

:::ignore
```lean -show
/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check <{ unit }>

/-- info: <{ Nat }> : Ty -/
#guard_msgs in
#check (Ty.nat : Ty)

/-- info: <{ Ref Nat }> : Ty -/
#guard_msgs in
#check (Ty.ref Ty.nat : Ty)

/-- info: <{ Unit }> : Ty -/
#guard_msgs in
#check (Ty.unit : Ty)

/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check (Tm.unit : Tm)

/-- info: <{ 0 }> : Tm -/
#guard_msgs in
#check (Tm.const 0 : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := rfl

/-- info: <{ λ X : Nat . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Nat. X }>

/-- info: <{ if0 X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 X then X else X }>

/-- info: <{ if0 Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 Y X then X else X }>

/-- info: <{ if0 Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if0 (Y X) then X else X }>

/-- info: <{ X * Y * Z }> : Tm -/
#guard_msgs in
#check <{ X * Y * Z }>

/-- info: <{ succ (pred X) }> : Tm -/
#guard_msgs in
#check <{ succ (pred X) }>

/-- info: <{ succ X Y }> : Tm -/
#guard_msgs in
#check <{ succ X Y }>

/-- info: <{ ref (λ X : Unit . X) }> : Tm -/
#guard_msgs in
#check <{ ref (λ X : Unit . X) }>

/-- info: <{ !X }> : Tm -/
#guard_msgs in
#check <{ !X }>

/-- info: <{ loc 3 }> : Tm -/
#guard_msgs in
#check <{ loc 3 }>
```
:::

::::full
Intuitively:
- `ref t` (formally, `ref t`) allocates a new reference cell
  with the value `τ` and reduces to the location of the newly
  allocated cell;

- `!t` (formally, `deref t`) reduces to the contents of the
  cell referenced by `τ`;

- `t₁ := t₂` (formally, `assign t₁ t₂`) assigns `t₂` to the
  cell referenced by `t₁`; and

- `l` (formally, `loc l`) is a reference to the cell at
  location `l`.  We'll discuss locations later.
::::

::::full
In informal examples, we'll also freely use the extensions
of the STLC developed in the {ref "MoreStlc"}[MoreStlc] chapter; however, to keep
the proofs small, we won't bother formalizing them again here.  (It
would be easy to do so, since there are no very interesting
interactions between those features and references.)
::::

## Typing (Preview)

Informally, the typing rules for allocation, dereferencing, and
assignment look roughly like this:

```display
                           Γ ⊢ t₁ ⦂ τ₁
                       --------------------                   (ref)
                       Γ ⊢ ref t₁ ⦂ Ref τ₁

                        Γ ⊢ t₁ ⦂ Ref τ₁
                        -------------------                   (deref)
                          Γ ⊢ !t1 ⦂ τ₁

                        Γ ⊢ t₁ ⦂ Ref τ₂
                          Γ ⊢ t₂ ⦂ τ₂
                       --------------------                  (assign)
                       Γ ⊢ t₁ := t₂ : Unit
```

The rule for locations will require a bit more machinery, and this
will motivate some changes to the other rules; we'll come back to
this later.

## Values and Substitution

Besides abstractions, numbers, and the unit value, we have one new
type of value: locations.

A location is a concrete pointer value -- think of it like an address
in memory. Locations should never be written directly by programmers;
they are used to keep track of the intermediate states of programs
involving references. In particular, the result of a `ref` expression
is a location.

```lean
inductive Tm.IsValue : Tm → Prop :=
  | abs : forall x τ₂ t₁,
      IsValue <{λx : τ₂. t₁}>
  | nat : forall (n : Nat),
      IsValue (.const n)
  | unit :
      IsValue <{ unit }>
  | loc : forall (l : Nat),
      IsValue (.loc l)

attribute [StlcRefEval] Tm.IsValue.abs Tm.IsValue.nat Tm.IsValue.unit Tm.IsValue.loc
```
Extending substitution to handle the new syntax of terms is
straightforward: substituting into a pointer leaves it
unchanged.
```lean
def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  -- numbers
  | .const _ =>
      t
  | .succ t₁ =>
      <{ succ ([x := s] t₁) }>
  | .pred t₁ =>
      <{ pred ([x := s] t₁) }>
  | .mult t₁ t₂ =>
      <{ ([x := s] t₁) * ([x := s] t₂) }>
  | .ite0 t₁ t₂ t₃ =>
      <{
        if0 [x := s] t₁
        then [x := s] t₂
        else [x := s] t₃
      }>
  -- unit
  | .unit => <{ unit }>
  -- references
  | .ref t₁ =>  <{ ref ([x := s] t₁) }>
  | .deref t₁ =>  <{ !([x := s] t₁) }>
  | .loc n => .loc n
  | .assign t₁ t₂ =>
      <{ ([x := s] t₁) := ([x := s] t₂) }>
```

:::details "Notation encoding"
```lean
open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst
```
:::


# Pragmatics

## Side Effects and Sequencing

::::full
The fact that we've chosen the result of an assignment
expression to be the trivial value `unit` allows a nice
abbreviation for _sequencing_.  For example, we can write

```
R:=succ(!R); !R
```

as an abbreviation for

```
(λX:Unit, !R) (R:=succ(!R))
```

This has the effect of reducing two expressions in order and
returning the value of the second.  Restricting the type of the
first expression to `Unit` helps the typechecker to catch some
silly errors by permitting us to throw away the first value only
if it is really guaranteed to be trivial.

Notice that, if the second expression is also an assignment, then
the type of the whole sequence will be `Unit`, so we can validly
place it to the left of another `;` to build longer sequences of
assignments:

```
R:=succ(!R); R:=succ(!R); R:=succ(!R); R:=succ(!R); !R
```
::::

::::terse
We can write (for example)

```
R := succ (!R); !R
```

as an abbreviation for

```
(λX:Unit. !R) (r := succ(!R)).
```
::::

::::full
Formally, we introduce sequencing as a _derived form_
`tseq` that expands into an abstraction and an application.
::::

```lean
/-- info: <{ R := succ (!R) ; !R }> : Tm -/
#guard_msgs in
#check <{R := succ (!R); !R}>
```

## References and Aliasing

It is important to bear in mind the difference between the
_reference_ that is bound to some variable `r` and the _cell_
in the store that is pointed to by this reference.

If we make a copy of `r`, for example by binding its value to
another variable `s`, what gets copied is only the reference,
not the contents of the cell itself.

For example, after reducing

``` display
let R = ref 5 in
let S = R in
S := 82;
(!R)+1
```

the cell referenced by `R` will contain the value `82`, while the
result of the whole expression will be `83`.  The references `R`
and `S` are said to be _aliases_ for the same cell.

The possibility of aliasing can make programs with references
quite tricky to reason about.  For example, the expression

```display
R := 5; R := !S
```

assigns `5` to `R` and then immediately overwrites it with `S`'s
current value; this has exactly the same effect as the single
assignment

```display
R := !S
```
_unless_ we happen to do it in a context where `R` and `S` are
aliases for the same cell!

```display
let R = ref 0 in
let S = R in
R := 5; R := !S
```

## Shared State

Of course, aliasing is also a large part of what makes references
useful.  In particular, it allows us to set up "implicit
communication channels" -- shared state -- between different parts
of a program.  For example, suppose we define a reference cell and
two functions that manipulate its contents:

```display
let C = ref 0 in
let Incc = λ_:Unit. (C := succ (!C); !C) in
let Decc = λ_:Unit. (C := pred (!C); !C) in
  ...
```

::::full
Note that, since their argument types are `Unit`, the
arguments to the abstractions in the definitions of `Incc` and
`Decc` are not providing any useful information to the bodies of
these functions (using the wildcard `_` as the name of the bound
variable is a reminder of this).  Instead, their purpose of these
abstractions is to "slow down" the execution of the function
bodies.  Since function abstractions are values, the two `let`s are
executed simply by binding these functions to the names `Incc` and
`Decc`, rather than by actually incrementing or decrementing `C`.
Later, each call to one of these functions results in its body
being executed once and performing the appropriate mutation on
`C`.  Such functions are often called _thunks_.

In the context of these declarations, calling `Incc` results in
changes to `C` that can be observed by calling `Decc`.  For
example, if we replace the `...` with `(Incc unit; Incc unit; Decc
unit)`, the result of the whole program will be `1`.
::::

::::terse
The `Unit`-abstractions ("thunks") are used here to prevent
reduction until later.
::::

## Objects

We can go a step further and write a _function_ that creates `C`,
`Incc`, and `Decc`, packages `Incc` and `Decc` together into a
record, and returns this record:
```
Newcounter =
  λ_:Unit.
      let C = ref 0 in
      let Incc = λ_:Unit. (C := succ (!C); !C) in
      let Decc = λ_:Unit. (C := pred (!C); !C) in
      {i=Incc, d=Decc}
```

Now, each time we call `Newcounter`, we get a new record of
functions that share access to the same storage cell `C`.  The
caller of `Newcounter` can't get at this storage cell directly,
but can affect it indirectly by calling the two functions.  In
other words, we've created a simple form of _object_.
```
let C₁ = newcounter unit in
let C₂ = newcounter unit in
// we've allocated two separate storage cells now!
let R₁ = C₁.i unit in
let R₂ = C₂.i unit in
R₂  // yields 1, not 2!
```


:::::full
::::exercise (rating := 1) (name := "store_draw") (manual := true)
Draw (on paper) the contents of the store at the point in
execution where the first two `let`s have finished and the third
one is about to begin.
::::

:::grade
`GRADE_MANUAL 1: store_draw`
:::
:::::

## References to Compound Types

A reference cell need not contain just a number: the primitives
we've defined above allow us to create references to values of any
type, including functions.  For example, we can use references to
functions to give a(n inefficient) implementation of arrays of
numbers as follows.

Write `NatArray` for the type `Ref (Nat→Nat)`.

::::full
Recall the `Equal` function from the {ref "MoreStlc"}[MoreStlc] chapter:
```display
Equal =
  fix
    (λEq:Nat→Nat→Bool.
        λM:Nat. λN:Nat.
          if M=0 then iszero n
          else if N=0 then false
          else Eq (pred m) (pred n))
```
::::

To build a new array, we allocate a reference cell and fill
it with a function that, when given an index, always returns `0`.

```display
Newarray = λ_:Unit. ref (λN:Nat.0)
```

To look up an element of an array, we apply the function
to the desired index.
```display
Lookup = λA:NatArray, λN:Nat. (!A) N
```

The interesting part of the encoding is the `Update` function.  It
takes an array, an index, and a new value to be stored at that index, and
it does its job by creating (and storing in the reference) a new function
that, when it is asked for the value at this very index, returns the new
value that was given to `Update`, while on all other indices it passes the
lookup to the function that was previously stored in the reference.
```
Update = \A:NatArray, \M:Nat, \V:Nat,
  let Oldf = !A in
  A := (λN:Nat. if Equal M N then V else Oldf N);
```

References to values containing other references can also be very
useful, allowing us to define data structures such as mutable
lists and trees.

:::::full
::::exercise (rating := 2) (name := "compact_update") (manual := true)

If we defined `Update` more compactly like this
```display
Update = \A:NatArray, \M:Nat, \V:Nat,
    A := (λN:Nat. if Equal M N then V else (!A) N);
```
would it behave the same?

:::solution
No: calls to `Lookup` with any index other than the one given to
`Update` will now diverge.  The point is that we need to make sure
we look up the value stored in `A` _before_ we overwrite it with
the new function.  Otherwise, when we get around to doing the
lookup, we will find the new function, not the original one.
:::

:::grade
`GRADE_MANUAL 2: compact_update`
:::
::::
:::::

## Null References

::::full
There is one final significant difference between our
references and C-style mutable variables: in C-like languages,
variables holding pointers into the heap may sometimes have the
value `NULL`.  Dereferencing such a "null pointer" is an error,
and results either in a clean exception (Java and C#) or in
arbitrary and possibly insecure behavior (C and relatives like
C++).  Null pointers cause significant trouble in C-like
languages: the fact that any pointer might be null means that any
dereference operation in the program can potentially fail.

Even in ML-like languages, there are sometimes situations where
we may or may not have a valid pointer in our hands.  Fortunately,
there is no need to extend the basic mechanisms of references to
represent such situations: the sum types introduced in the
{ref "MoreStlc"}[MoreStlc] chapter already give us what we need.

First, we can use sums to build an analog of the `option` types
introduced in the Lists chapter of _Logical Foundations_.
Define `Option τ` to be an abbreviation for `Unit + τ`.

Then a "nullable reference to a `τ`" is simply an element of the
type `Option (Ref τ)`.
::::

::::terse
TERSE: One more difference between our references and C-style
mutable variables: _null pointers_.

- In C, a pointer variable can contain either a valid pointer
into the heap or the special value `NULL`.

- A source of many errors and much tricky reasoning:
  - (any pointer may potentially be "not there")
  - but occasionally useful

- Nullable pointers are easy to implement using references
plus options (which can be built out of disjoint sum types):

```display
Option τ       =  Unit + τ
NullableRef τ  =  Ref (Option τ)
```
::::

## Garbage Collection

A last issue that we should mention before we move on with formalizing
references is storage _de_-allocation.  We have not provided any
primitives for freeing reference cells when they are no longer needed.
Instead, like many modern languages (including OCaml, Haskell, Java,
etc.) we rely on the run-time system to perform _garbage collection_,
automatically identifying and reusing cells that can no longer be
reached by the program.

This is _not_ just a question of taste in language design: it is
extremely difficult to achieve type safety in the presence of an
explicit deallocation operation.

One reason for this is the familiar _dangling reference_ problem:
we allocate a cell holding a number, save a reference to it in
some data structure, use it for a while, then deallocate it and
allocate a new cell holding a boolean, possibly reusing the same
storage.  Now we can have two names for the same storage cell --
one with type `Ref Nat` and the other with type `Ref Bool`.

:::::full
::::exercise (rating := 2) (name := "type_safety_violation") (manual := true)
Show how this can lead to a violation of type safety.

:::solution
Suppose the language provides a primitive `free` that takes a
reference cell as argument and releases its storage so that (say)
the very next allocation of a reference cell will obtain the same
piece of memory.  Then the program
```
    let R = ref 0 in
    let S = R in
    free R;
    let T = ref true in
    T := false;
    succ (!S)
```
will reduce to the stuck term `succ false`.  Note that aliasing
plays a crucial role here in setting up the problem, since it
prevents us from detecting invalid deallocations by simply making
`free r` illegal if the variable `R` appears free in the remainder
of the expression.

This sort of example is easy to mimic in a language like C with
manual memory management (our `ref` constructor corresponds to C's
`malloc`, our `free` to a simplified version of C's `free`).
:::

:::grade
`GRADE_MANUAL 2: type_safety_violation`
:::
::::
:::::

# Operational Semantics

## Locations

::::full
The most subtle aspect of the treatment of references
appears when we consider how to formalize their operational
behavior.  One way to see why is to ask, "What should be the
_values_ of type `Ref τ`?"  The crucial observation that we need
to take into account is that reducing a `ref` operator should
_do_ something -- namely, allocate some storage -- and the result
of the operation should be a reference to this storage.

What, then, is a reference?

The run-time store in most programming-language implementations is
essentially just a big array of bytes.  The run-time system keeps
track of which parts of this array are currently in use.  When we
need to allocate a new reference cell, we allocate a large enough
segment from the free region of the store (4 bytes for integer
cells, 8 bytes for cells storing `Float`s, etc.), record somewhere
that it is being used, and return the index (typically, a 32- or
64-bit integer) of the start of the newly allocated region.  These
indices are references.

For present purposes, there is no need to be quite so concrete.
We can think of the store as an array of _values_, rather than an
array of bytes, abstracting away from the different sizes of the
run-time representations of different values.  A reference, then,
is simply an index into the store.  (If we like, we can even
abstract away from the fact that these indices are numbers, but
for purposes of formalization in Rocq it is convenient to use
numbers.)  We use the word _location_ instead of _reference_ or
_pointer_ to emphasize this abstract quality.

Treating locations abstractly in this way will prevent us from
modeling the _pointer arithmetic_ found in low-level languages
such as C.  This limitation is intentional.  While pointer
arithmetic is occasionally very useful, especially for
implementing low-level services such as garbage collectors, it
cannot be tracked by most type systems: knowing that location `n`
in the store contains a `Float` doesn't tell us anything useful
about the type of location `n+4`.  In C, pointer arithmetic is a
notorious source of type-safety violations.
::::

::::terse
A reference names a location in the _store_ (a.k.a. heap).

What is the store?

  - Concretely: An array of 8-bit bytes, indexed by 32-bit integers.

  - More abstractly: a list or array, of values

  - Even more abstractly: a partial function from locations to values.

We'll choose the middle way here: A store is a list of values, and
a location is a natural-number index into this list.
::::

## Stores

::::full
Recall that, in the small-step operational semantics for
Imp, the step relation needed to carry along an auxiliary state in
addition to the program being executed.  In the same way, once we
have added reference cells to the STLC, our step relation must
carry along a store to keep track of the contents of reference
cells.

We could re-use the same functional representation we used for
states in Imp, but for carrying out the proofs in this chapter it
is actually more convenient to represent a store simply as a
_list_ of values.  (The reason we didn't use this representation
before is that, in Imp, a program could modify any location at any
time, so states had to be ready to map _any_ variable to a value.
However, in the STLC with references, the only way to create a
reference cell is with `ref t₁`, which puts the value of `t₁`
in a new reference cell and reduces to the location of the newly
created reference cell. When reducing such an expression, we can
just add a new reference cell to the end of the list representing
the store.)
::::

::::terse
A store is just a _list_ of values.  (This more concrete
representation will be more convenient for proofs than the
functional representation we used in Imp.)
::::

```lean
def Store := List Tm
```

We use `st[n]` to retrieve the value of the reference
cell at location `n` in the store `st`.  Note that we must give a
default value to `nth` in case we try looking up an index which is
too large. (In fact, we never actually do this, but _proving_
that we don't will require a bit of work.)


```lean
open scoped MyGetElem
instance : MyGetElem Store Nat Tm where
  getElem st n := st.getD n <{unit}>
```

To update the store, we use the {lean}`List.set` function, which replaces
the contents of a cell at a particular index.

```display
def List.set : (l : List α) → (n : Nat) → (a : α) → List α
  | cons _ as, 0,          b => cons b as
  | cons a as, Nat.succ n, b => cons a (set as n b)
  | nil,       _,          _ => nil
```

## Reduction

::::terse
First, we augment existing reduction rules with stores:
```display
                              v₂.IsValue
                -------------------------------------               (appAbs)
                (λx:τ₂. t₁) v₂ / st ⟶ [x:=v₂] t₁ / st

                        t₁ / st ⟶ t₁' / st'
                     ---------------------------                      (app₁)
                     t₁ t₂ / st ⟶ t₁' t₂ / st'

                  v₁.IsValue     t₂ / st ⟶ t₂' / st'
                  ----------------------------------                  (app₂)
                     v₁ t₂ / st ⟶ v₁ t₂' / st'
```

Now we can give the rules for the new constructs:

```display
                   ------------------------------                  (refValue)
                   ref v / st ⟶ loc st.length / st,v

                        t₁ / st ⟶ t₁' / st'
                    -----------------------------                    (ref)
                    ref t₁ / st ⟶ ref t₁' / st'

                               l < st.length
                     ----------------------------------            (derefLoc)
                     !(loc l) / st ⟶ st[l] / st

                        t₁ / st ⟶ t₁' / st'
                       -----------------------                       (deref)
                       !t1 / st ⟶ !t₁' / st'

                               l < st.length
                ------------------------------------------         (assign)
                loc l := v / st ⟶ unit / List.set st l v

                        t₁ / st ⟶ t₁' / st'
                 -----------------------------------               (assign₁)
                 t₁ := t₂ / st ⟶ t₁' := t₂ / st'

                        t₂ / st ⟶ t₂' / st'
                 -----------------------------------               (assign₂)
                 v₁ := t₂ / st ⟶ v₁ := t₂' / st'
```
::::

::::full
Next, we need to extend the operational semantics to take
stores into account.  Since the result of reducing an expression
will in general depend on the contents of the store in which it is
reduced, the evaluation rules should take not just a term but
also a store as argument.  Furthermore, since the reduction of a
term can cause side effects on the store, and these may affect the
reduction of other terms in the future, the reduction rules need
to return a new store.  Thus, the shape of the single-step
reduction relation needs to change from `t ⟶ t'` to `t / st ⟶ t' / st'`,
where `st` and `st` are the starting and ending states of
the store.

To carry through this change, we first need to augment all of our
existing reduction rules with stores:

```display
                               value v₂
                ------------------------------------- (appAbs)
                (λx:τ₂,t₁) v₂ / st ⟶ [x:=v₂]t₁ / st

                        t₁ / st ⟶ t₁' / st'
                     --------------------------- (app₁)
                     t₁ t₂ / st ⟶ t₁' t₂ / st'

                  value v₁     t₂ / st ⟶ t₂' / st'
                  ---------------------------------- (app₂)
                     v₁ t₂ / st ⟶ v₁ t₂' / st'
```

Note that the first rule here returns the store unchanged, since
function application, in itself, has no side effects.  The other
two rules simply propagate side effects from premise to
conclusion.

Now, the result of reducing a `ref` expression will be a fresh
location; this is why we included locations in the syntax of terms
and in the set of values.  It is crucial to note that making this
extension to the syntax of terms does not mean that we intend
_programmers_ to write terms involving explicit, concrete locations:
such terms will arise only as intermediate results during reduction.
This may seem odd, but it follows naturally from our design decision
to represent the result of every reduction step by a modified _term_.
If we had chosen a more "machine-like" model, e.g., with an explicit
stack to contain values of bound identifiers, then the idea of adding
locations to the set of allowed values might seem more obvious.

In terms of this expanded syntax, we can state reduction rules
for the new constructs that manipulate locations and the store.
First, to reduce a dereferencing expression `!t1`, we must first
reduce `t₁` until it becomes a value:

```display
                        t₁ / st ⟶ t₁' / st'
                       --------------------- (deref)
                       !t1 / st ⟶ !t₁' / st'
```
Once `t₁` has finished reducing, we should have an expression of
the form `!l`, where `l` is some location.  (A term that attempts
to dereference any other sort of value, such as a function or
`unit`, is erroneous, as is a term that tries to dereference a
location that is larger than the size st.length of the currently
allocated store; the reduction rules simply get stuck in this
case.  The type-safety properties established below assure us
that well-typed terms will never misbehave in this way.)

```display
                               l < st.length
                     ---------------------------------- (derefLoc)
                     !(loc l) / st ⟶ st[l] / st
```

Next, to reduce an assignment expression `t₁:=t₂`, we must first
reduce `t₁` until it becomes a value (a location), and then
reduce `t₂` until it becomes a value (of any sort):

```display
                        t₁ / st ⟶ t₁' / st'
                 ----------------------------------- (assign₁)
                 t₁ := t₂ / st ⟶ t₁' := t₂ / st'

                        t₂ / st ⟶ t₂' / st'
                  --------------------------------- (assign₂)
                  v₁ := t₂ / st ⟶ v₁ := t₂' / st'
```

Once we have finished with `t₁` and `t₂`, we have an expression of
the form `l:=v`, which we execute by updating the store to make
location `l` contain `v`:

```display
                               l < st.length
                -----------------------------------   (assign)
                loc l := v / st ⟶ unit / [l:=v]st
```

The notation `[l:=v]st` means "the store that maps `l` to `v`
and maps all other locations to the same thing as `st`". Note
that the term resulting from this reduction step is just `unit`;
the interesting result is the updated store.

Finally, to reduct an expression of the form `ref t₁`, we first
reduce `t₁` until it becomes a value:

```display
                        t₁ / st ⟶ t₁' / st'
                    --------------------------- (ref)
                    ref t₁ / st ⟶ ref t₁' / st'
```

Then, to reduce the `ref` itself, we choose a fresh location at
the end of the current store -- i.e., location `st.length` -- and yield
a new store that extends `st` with the new value `v`.

```display
          -------------------------------- (refValue)
          ref v / st ⟶ loc st.length / st, v
```

The value resulting from this step is the newly allocated location
itself.  (Formally, `st, v` means `st ++ [v]` -- i.e., to add
a new reference cell to the store, we append it to the end.)

Note that these reduction rules do not perform any kind of
garbage collection: we simply allow the store to keep growing
without bound as reduction proceeds.  This does not affect the
correctness of the results of reduction (after all, the
definition of "garbage" is precisely parts of the store that are
no longer reachable and so cannot play any further role in
reduction), but it means that a naive implementation of our
evaluator might run out of memory where a more sophisticated
evaluator would be able to continue by reusing locations whose
contents have become garbage.

Here are the rules again, formally:
::::

```lean
section
set_option hygiene false in
local notation:40 t:41 " / " st:41 " ⟶ " t':41 " / " st:41 => Step t st t' st'

inductive Step : Tm → Store → Tm → Store → Prop :=
  | appAbs : forall x τ₂ t₁ v₂ st,
         value v₂ →
         <{ (λx : τ₂, t₁) v₂ }> / st ⟶ <{ [x := v₂] t₁ }> / st
  | app₁ : forall t₁ t₁' t₂ st st',
         t₁ / st ⟶ t₁' / st' →
         <{ t₁ t₂ }> / st ⟶ <{ t₁' t₂ }> / st'
  | app₂ : forall v₁ t₂ t₂' st st',
         value v₁ →
         t₂ / st ⟶ t₂' / st' →
         <{ v₁ t₂ }> / st ⟶ <{ v₁ t₂' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st ⟶ tm_const (S n) / st
  | ST_Succ : forall t₁ t₁' st st',
         t₁ / st ⟶ t₁' / st' →
         <{ succ t₁ }> / st ⟶ <{ succ t₁' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st ⟶ tm_const (n - 1) / st
  | ST_Pred : forall t₁ t₁' st st',
         t₁ / st ⟶ t₁' / st' →
         <{ pred t₁ }> / st ⟶ <{ pred t₁' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st ⟶  tm_const (n1 * n2) / st
  | ST_Mult1 : forall t₁ t₂ t₁' st st',
         t₁ / st ⟶ t₁' / st' →
         <{ t₁ * t₂ }> / st ⟶ <{ t₁' * t₂ }> / st'
  | ST_Mult2 : forall v₁ t₂ t₂' st st',
         value v₁ →
         t₂ / st ⟶ t₂' / st' →
         <{ v₁ * t₂ }> / st ⟶ <{ v₁ * t₂' }> / st'
  | ST_If0 : forall t₁ t₁' t₂ t3 st st',
         t₁ / st ⟶ t₁' / st' →
         <{ if0 t₁ then t₂ else t3 }> / st ⟶ <{ if0 t₁' then t₂ else t3 }> / st'
  | ST_If0_Zero : forall t₂ t3 st,
         <{ if0 0 then t₂ else t3 }> / st ⟶ t₂ / st
  | ST_If0_Nonzero : forall n t₂ t3 st,
         <{ if0 $(S n) then t₂ else t3 }> / st ⟶ t3 / st
  (* references *)
  | refValue : forall v st,
         value v →
         <{ ref v }> / st ⟶ <{ loc $(length st) }> / (st ++ v::nil)
  | ref : forall t₁ t₁' st st',
         t₁ / st ⟶ t₁' / st' →
         <{ ref t₁ }> /  st ⟶ <{ ref t₁' }> /  st'
  | derefLoc : forall st l,
         l < length st →
         <{ !(loc l) }> / st ⟶ <{ $(store_lookup l st) }> / st
  | deref : forall t₁ t₁' st st',
         t₁ / st ⟶ t₁' / st' →
         <{ ! t₁ }> / st ⟶ <{ ! t₁' }> / st'
  | assign : forall v l st,
         value v →
         l < length st →
         <{ (loc l) := v }> / st ⟶ <{ unit }> / replace l v st
  | assign₁ : forall t₁ t₁' t₂ st st',
         t₁ / st ⟶ t₁' / st' →
         <{ t₁ := t₂ }> / st ⟶ <{ t₁' := t₂ }> / st'
  | assign₂ : forall v₁ t₂ t₂' st st',
         value v₁ →
         t₂ / st ⟶ t₂' / st' →
         <{ v₁ := t₂ }> / st ⟶ <{ v₁ := t₂' }> / st'
```

(** FULL: One slightly ugly point should be noted here: In the
    [refValue] rule, we extend the state by writing [st ++ v::nil]
    rather than the more natural [st ++ [v```.  The reason for this is
    that the notation we've defined for substitution uses square
    brackets, which clash with the standard library's notation for
    lists. *)

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '⟶*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** * Typing *)

(** The contexts assigning types to free variables are exactly the
    same as for the STLC: partial maps from identifiers to types. *)

Definition context := partial_map Ty.

(* ################################### *)

(** ** Store typings *)

(** FULL: Having extended our syntax and reduction rules to accommodate
    references, our last job is to write down typing rules for the new
    constructs (and, of course, to check that these rules are sound!).

    Naturally, the key question is, "What is the type of a location?"
*)
(** TERSE: Naturally, the key question is, "What is the type of a
    location?" *)

(** FULL: First of all, notice that this question doesn't arise when
    typechecking terms that programmers actually write.  Concrete
    location constants arise only in terms that are the intermediate
    results of reduction; they are not in the language that
    programmers write.  So we only need to determine the type of a
    location when we're in the middle of a reduction sequence, e.g.,
    trying to apply the progress or preservation lemmas.  Thus, even
    though we normally think of typing as a _static_ program property,
    it makes sense for the typing of locations to depend on the
    _dynamic_ progress of the program too.

    As a first try, note that when we reduce a term containing
    concrete locations, the type of the result depends on the contents
    of the store that we start with.  For example, if we reduce the
    term [!(loc 1)] in the store ```unit, unit```, the result is `unit`;
    if we reduce the same term in the store ```unit, λx:Unit,x```, the
    result is [λx:Unit,x].  With respect to the former store, the
    location [1] has type `Unit`, and with respect to the latter it
    has type [Unit→Unit]. This observation leads us immediately to a
    first attempt at a typing rule for locations:
 *)
(** TERSE: As a first try, observe that the type of a location is
    connected to the contents of the store ```st```.
*)
(**
```display
                             Γ ⊢ lookup l st : τ₁
                             --------------------------
                             Γ ⊢ loc l : Ref τ₁
```
 *)
(** TERSE: But where does ```st``` come from? *)
(** FULL: That is, to find the type of a location `l`, we look up the
    current contents of `l` in the store and calculate the type [τ₁]
    of the contents.  The type of the location is then [Ref τ₁].

    Having begun in this way, we need to go a little further to reach a
    consistent state.  In effect, by making the type of a term depend on
    the store, we have changed the typing relation from a three-place
    relation (between contexts, terms, and types) to a four-place relation
    (between contexts, _stores_, terms, and types).  Since the store is,
    intuitively, part of the context in which we calculate the type of a
    term, let's write this four-place relation with the store to the left
    of the turnstile: [Γ; st ⊢ t : T].  Our rule for typing
    references now has the form
 *)
(** TERSE: *** *)
(** TERSE: We could try adding `st` to the judgment: [Γ; st ⊢ t : T],
    which gives us this rule:
*)
(**
```display
                     Γ; st ⊢ lookup l st : τ₁
                     ------------------------------
                      Γ; st ⊢ loc l : Ref τ₁
```
*)
(** TERSE: But that means the _whole_ store `st`, including all dynamically
    created values, is needed _during typechecking_.  This does not seem
    like something we want.

    Worse yet, it doesn't work at all for _cyclic_ stores.
*)
(** FULL:
    and all the rest of the typing rules in the system are extended
    similarly with stores.  (The other rules do not need to do anything
    interesting with their stores -- just pass them from premise to
    conclusion.)

    However, this rule will not quite do.  For one thing, typechecking
    is rather inefficient, since calculating the type of a location `l`
    involves calculating the type of the current contents [v] of `l`.  If
    `l` appears many times in a term `τ`, we will re-calculate the type of
    [v] many times in the course of constructing a typing derivation for
    `τ`.  Worse, if [v] itself contains locations, then we will have to
    recalculate _their_ types each time they appear.  Worse yet, the
    proposed typing rule for locations may not allow us to derive
    anything at all if the store contains a _cycle_.  For example,
    there is no finite typing derivation for the location [0] with respect
    to this store:
 *)
(** TERSE: For example, what is the type of location [0] in the
    following store? *)
(**
```
   [λx:Nat, (!(loc 1)) x, λx:Nat, (!(loc 0)) x]
```
*)
(* FULL *)
(* EX3 (cyclic_store) *)
(** Can you find a term whose reduction will create this particular
    cyclic store? *)

Theorem cyclic_store:
  exists t,
    t / nil ⟶*
    <{ unit }> / (<{ λx:Nat, (!(loc 1)) x }> :: <{ λx:Nat, (!(loc 0)) x }> :: nil).
Proof.
  (* ADMITTED *)
  Notation "'let' x ':' T '=' t₁ 'in' t₂" :=
    <{ (λx:T, t₂) t₁ }> (in custom stlc_tm at level 3, T custom stlc_ty).
  remember ("r0"%string) as r0.
  remember ("r1"%string) as r1.
  exists <{ let r0 : (Ref (Nat → Nat)) = ref (λx:Nat, x) in
            let r1 : (Ref (Nat → Nat)) = ref (λx:Nat, (!r0) x) in
            (r0 := λx:Nat, (!r1) x) }>.
  subst.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  eapply multi_step. { apply assign. auto. simpl. auto. } simpl.
  eapply multi_refl.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(** TERSE: *** *)

(** FULL: These problems arise from the fact that our proposed
    typing rule for locations requires us to recalculate the type of a
    location every time we mention it in a term.  But this,
    intuitively, should not be necessary.  After all, when a location
    is first created, we know the type of the initial value that we
    are storing into it.  Suppose we are willing to enforce the
    invariant that the type of the value contained in a given location
    _never changes_; that is, although we may later store other values
    into this location, those other values will always have the same
    type as the initial one.  In other words, we always have in mind a
    single, definite type for every location in the store, which is
    fixed when the location is allocated.  Then these intended types
    can be collected together as a _store typing_ -- a finite function
    mapping locations to types.

    As with the other type systems we've seen, this conservative typing
    restriction on allowed updates means that we will rule out as
    ill-typed some programs that could reduce perfectly well without
    getting stuck.

    Just as we did for stores, we will represent a store type simply
    as a list of types: the type at index [i] records the type of the
    values that we expect to be stored in cell [i]. *)
(** TERSE: Instead, we establish an _invariant_ that the type of
    value stored in a location never changes.

     This _static_ representation of the store contents is called a
     _store typing_: *)

Definition store_ty := list Ty.

(** TERSE: Here we represent locations as indices into a _list_ of
    types so the type at index [i] is the type of the values stored in
    cell [i]. *)

(** The [store_Tlookup] function retrieves the type at a particular
    index. *)

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST <{{ Unit }}>.

(** TERSE: *** *)

(** FULL: Suppose we are given a store typing [ST] describing the store
    `st` in which some term `τ` will be reduced.  Then we can use
    [ST] to calculate the type of the result of `τ` without ever
    looking directly at `st`.  For example, if [ST] is ```Unit,
    Unit→Unit```, then we can immediately infer that [!(loc 1)] has
    type [Unit→Unit].  More generally, the typing rule for locations
    can be reformulated in terms of store typings like this: *)
(** TERSE: We can use the store typing [ST] to give a type to
    any location `l` like this: *)
(**
```display
                                 l < |ST|
                   ----------------------------------------------
                   Γ; ST ⊢ loc l : Ref (store_Tlookup l ST)
```
*)
(** FULL: That is, as long as `l` is a valid location, we can compute the
    type of `l` just by looking it up in [ST].  Typing is again a
    four-place relation, but it is parameterized on a store _typing_
    rather than a concrete store.  The rest of the typing rules are
    analogously augmented with store typings. *)

(* ################################### *)
(** ** The Typing Relation *)

(** FULL: We can now formalize the typing relation for the STLC with
    references.  Here, again, are the rules we're adding to the base
    STLC (with numbers and `Unit`): *)

(**
```display
                               l < |ST|
             ----------------------------------------------             (T_Loc)
             Γ; ST ⊢ loc l : Ref (store_Tlookup l ST)

                         Γ; ST ⊢ t₁ : τ₁
                     -----------------------------                      (ref)
                     Γ; ST ⊢ ref t₁ : Ref τ₁

                      Γ; ST ⊢ t₁ : Ref τ₁
                      -------------------------                       (deref)
                        Γ; ST ⊢ !t1 : τ₁

                      Γ; ST ⊢ t₁ : Ref τ₂
                        Γ; ST ⊢ t₂ : τ₂
                    -----------------------------                    (assign)
                    Γ; ST ⊢ t₁ := t₂ : Unit
```
*)

(* HIDEFROMHTML *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* INSTRUCTORS: Begin Definition of template STCL has_type notation MODIFIED *)
Notation "x '|→' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0,
   v custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|→' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

(* NOTATION: If we don't include the following, then <{ empty ⊢ t : T }>
   will print as <{ $(empty) ⊢ t : T }> *)
Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Γ '/' ST '⊢' t '\in' T }>"
            (at level 0, Γ custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).
(* INSTRUCTORS: End STCL has_type notation MODIFIED *)
(* INSTRUCTORS: ------------------------------------------------------------- *)
(* /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
Inductive has_type (ST : store_ty) : contexτ → Tm → Ty → Prop :=
  | T_Var : forall Γ x τ₁,
      Γ x = Some τ₁ →
      <{ Γ / ST ⊢ x ⦂ τ₁ }>
  | T_Abs : forall Γ x τ₁ τ₂ t₁,
      <{ x |→ τ₂; Γ  / ST ⊢ t₁ ⦂ τ₁ }> →
      <{ Γ / ST ⊢ λx:τ₂, t₁ ⦂ τ₂ → τ₁ }>
  | T_App : forall τ₁ τ₂ Γ t₁ t₂,
      <{ Γ / ST ⊢ t₁ ⦂ τ₂ → τ₁ }> →
      <{ Γ / ST ⊢ t₂ ⦂ τ₂ }> →
      <{ Γ / ST ⊢ t₁ t₂ ⦂ τ₁ }>
  | T_Nat : forall Γ (n : nat),
      <{ Γ / ST ⊢ n ⦂ Nat }>
  | T_Succ : forall Γ t₁,
      <{ Γ / ST ⊢ t₁ ⦂ Nat }> →
      <{ Γ / ST ⊢ succ t₁ ⦂ Nat }>
  | T_Pred : forall Γ t₁,
      <{ Γ / ST ⊢ t₁ ⦂ Nat }> →
      <{ Γ / ST ⊢ pred t₁ ⦂ Nat }>
  | T_Mult : forall Γ t₁ t₂,
      <{ Γ / ST ⊢ t₁ ⦂ Nat }> →
      <{ Γ / ST ⊢ t₂ ⦂ Nat }> →
      <{ Γ / ST ⊢ t₁ * t₂ ⦂ Nat }>
  | T_If0 : forall Γ t₁ t₂ t3 T0,
      <{ Γ / ST ⊢ t₁ ⦂ Nat }> →
      <{ Γ / ST ⊢ t₂ ⦂ T0 }> →
      <{ Γ / ST ⊢ t3 ⦂ T0 }> →
      <{ Γ / ST ⊢ if0 t₁ then t₂ else t3 ⦂ T0 }>
  | T_Unit : forall Γ,
      <{ Γ / ST ⊢ unit ⦂ Unit }>
  | T_Loc : forall Γ l,
      l < length ST →
      <{ Γ / ST ⊢ (loc l) ⦂ Ref $(store_Tlookup l ST) }>
  | ref : forall Γ t₁ τ₁,
      <{ Γ / ST ⊢ t₁ ⦂ τ₁ }> →
      <{ Γ / ST ⊢ (ref t₁) ⦂ Ref τ₁ }>
  | deref : forall Γ t₁ τ₁,
      <{ Γ / ST ⊢ t₁ ⦂ Ref τ₁ }> →
      <{ Γ / ST ⊢ (! t₁) ⦂ τ₁ }>
  | assign : forall Γ t₁ t₂ τ₂,
      <{ Γ / ST ⊢ t₁ ⦂ Ref τ₂ }> →
      <{ Γ / ST ⊢ t₂ ⦂ τ₂ }> →
      <{ Γ / ST ⊢ (t₁ := t₂) ⦂ Unit }>

where "<{ Γ '/' ST '⊢' t '\in' T }>" := (has_type ST Γ t T).

Hint Constructors has_type : core.
(* TERSE: /HIDEFROMHTML *)

(** FULL: Of course, these typing rules will accurately predict the results
    of reduction only if the concrete store used during reduction
    actually conforms to the store typing that we assume for purposes
    of typechecking.  This proviso exactly parallels the situation
    with free variables in the basic STLC: the substitution lemma
    promises that, if [Γ ⊢ t : T], then we can replace the free
    variables in `τ` with values of the types listed in [Γ] to
    obtain a closed term of type `τ`, which, by the type preservation
    theorem will reduce to a final result of type `τ` if it yields
    any result at all.  We will see below how to formalize an
    analogous intuition for stores and store typings.

    However, for purposes of typechecking the terms that programmers
    actually write, we do not need to do anything tricky to guess what
    store typing we should use.  Concrete locations arise only in
    terms that are the intermediate results of reduction; they are
    not in the language that programmers write.  Thus, we can simply
    typecheck the programmer's terms with respect to the _empty_ store
    typing.  As reduction proceeds and new locations are created, we
    will always be able to see how to extend the store typing by
    looking at the type of the initial values being placed in newly
    allocated cells; this intuition is formalized in the statement of
    the type preservation theorem below.  *)

(* ################################### *)
(** * Properties *)

(** FULL: Our final task is to check that standard type safety
    properties continue to hold for the STLC with references.  The
    progress theorem ("well-typed terms are not stuck") can be stated
    and proved almost as for the STLC; we just need to add a few
    straightforward cases to the proof to deal with the new
    constructs.  The preservation theorem is a bit more interesting,
    so let's look at it first.  *)
(** TERSE: Standard theorems...
      - Progress -- pretty much same as always
      - Preservation -- needs to be stated more carefully! *)

(* ################################### *)
(** ** Well-Typed Stores *)

(** FULL: Since we have extended both the reduction relation (with
    initial and final stores) and the typing relation (with a store
    typing), we need to change the statement of preservation to
    include these parameters.  But clearly we cannot just add stores
    and store typings without saying anything about how they are
    related -- i.e., this is wrong: *)
(** TERSE: The evaluation and typing relations take more parameters
    now, so at a minumum we have to add these to the statement of
    preservation... *)

Theorem preservation_wrong : forall ST T t st t' st',
  <{ empty / ST ⊢ t ⦂ T }> →
  t / st ⟶ t' / st' →
  <{ empty / ST ⊢ t' ⦂ T }>.
Abort.

(** FULL: If we typecheck with respect to some set of assumptions
    about the types of the values in the store and then reduce with
    respect to a store that violates these assumptions, the result
    will be disaster.  We say that a store `st` is _well typed_ with
    respect a store typing [ST] if the term at each location `l` in
    `st` has the type at location `l` in [ST].  Since only closed
    terms ever get stored in locations (why?), it suffices to type
    them in the empty context. The following definition of
    [store_well_typed] formalizes this.  *)
(** TERSE: Obviously wrong: no relation between assumed store typing
    and provided store! *)

(** TERSE: *** *)

(** TERSE: We need a way of saying "this store satisfies the
    assumptions of that store typing"... *)

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st →
     <{ empty / ST ⊢ $(store_lookup l st)
                           ⦂ $(store_Tlookup l ST) }>).

(** Informally, we will write [ST ⊢ st] for [store_well_typed ST st]. *)

(** FULL: Intuitively, a store `st` is consistent with a store typing
    [ST] if every value in the store has the type predicted by the
    store typing.  The only subtle point is the fact that, when typing
    the values in the store, we supply the very same store typing to
    the typing relation.  This allows us to type circular stores like
    the one we saw above. *)

(* FULL *)
(* EX3 (store_not_unique) *)
(** Can you find a store `st`, and two
    different store typings [ST1] and [ST2] such that both
    [ST1 ⊢ st] and [ST2 ⊢ st]? *)

(* SOLUTION *)
(* Let `st` be a store with a single location [0], such that
      `st`  =  [λx:Unit, (!(loc 0))(x)].
   Then `st` is well typed with
   respect to both of the following store typings:
      ST1  =  [Unit → Unit]
      ST2  =  [Unit → (Unit→Unit)].
   In fact, it is well typed with respect to any store typing of the form
      ST   =  [Uniτ → τ]
   for any type `τ`. *)
(* /SOLUTION *)

Theorem store_not_unique:
  exists st, exists ST1, exists ST2,
    store_well_typed ST1 st /\
    store_well_typed ST2 st /\
    ST1 <> ST2.
Proof.
  (* ADMITTED *)
  exists (<{ λx:Unit, (!(loc 0)) x }> :: nil).
  exists (<{{ Unit → Unit }}> :: nil).
  exists (<{{ Unit → Nat }}> :: nil).
  unfold store_well_typed; simpl. repeat split.
  { intros [|l'].
    { intros _. repeat econstructor.
      replace (<{{ Unit → Unit }}>)
      with (store_Tlookup 0 (<{{ Unit → Unit }}>::nil)) at 2
        by reflexivity.
      repeat econstructor. }
    { intros H. solve_by_inverts 2. } }
  { intros [|l'].
    { intros _. repeat econstructor.
      replace (<{{ Unit → Nat }}>)
      with (store_Tlookup 0 (<{{ Unit → Nat }}>::nil)) at 2
        by reflexivity.
      repeat econstructor. }
    { intros H. solve_by_inverts 2. } }
  { congruence. }
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** TERSE: *** *)

(** We can now state something closer to the desired preservation
    property: *)

Theorem preservation_lesswrong : forall ST T t st t' st',
  <{ empty / ST ⊢ t ⦂ T }> →
  t / st ⟶ t' / st' →
  store_well_typed ST st →
  <{ empty / ST ⊢ t' ⦂ T }>.
Abort.

(** FULL: This statement is fine for all of the reduction rules except
    the allocation rule [refValue].  The problem is that this rule
    yields a store with a larger domain than the initial store, which
    falsifies the conclusion of the above statement: if `st'` includes
    a binding for a fresh location `l`, then `l` cannot be in the
    domain of [ST], and it will not be the case that [t'] (which
    definitely mentions `l`) is typable under [ST]. *)
(** TERSE: This works... for all but _one_ of the reduction rules!
    (Which?) *)
(** TERSE: *** *)
(** TERSE: The [refValue] rule is the problem:
```display
                   -------------------------------- (refValue)
                   ref v / st ⟶ loc |st| / st,v
```
    It allocates a fresh location `l` and adds it to the store, but
    the store typing [ST] doesn't know about `l`, so [t'] won't be
    typeable under [ST]. *)
(** TERSE: *** *)

(** For example, the term `ref 5` is typeable in the empty context and
    empty store typing, but it steps to [loc 0], which is not typeable
    with an empty store typing. *)

(* ############################################ *)
(** ** Extending Store Typings *)

(** FULL: Evidently, since the store can increase in size during
    reduction, we need to allow the store _typing_ to grow during
    reduction as well. This motivates the following definition.  We
    say that the store type [ST'] _extends_ [ST] if [ST'] is just [ST]
    with some new types added to the end. *)
(** TERSE: Intuition: Since the store can grow during reduction, we
    need to let the store _typing_ grow too... *)

Inductive extends : store_ty → store_ty → Prop :=
  | extends_nil  : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST →
      extends (x::ST') (x::ST).

(** For example, the store typing [ [Nat] ] with a single location of
    type [Nat] extends the empty store typing. *)

(* TERSE: HIDEFROMHTML *)
Hint Constructors extends : core.

(** We'll need a few technical lemmas about extended contexts.

    First, looking up a type in an extended store typing yields the
    same result as in the original: *)

Lemma extends_lookup : forall l ST ST',
  l < length ST →
  extends ST' ST →
  store_Tlookup l ST' = store_Tlookup l ST.
(* FOLD *)
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.
(* /FOLD *)

(** Next, if [ST'] extends [ST], the length of [ST'] is at least that
    of [ST]. *)

Lemma length_extends : forall l ST ST',
  l < length ST →
  extends ST' ST →
  l < length ST'.
(* FOLD *)
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply →Nat.succ_lt_mono. apply IHextends. lia.
Qed.
(* /FOLD *)

(** Finally, [ST ++ T] extends [ST], and [extends] is reflexive. *)

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
(* FOLD *)
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.
(* /FOLD *)

Lemma extends_refl : forall ST,
  extends ST ST.
(* FOLD *)
Proof.
  induction ST; auto.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Preservation, Finally *)

(** We can now give the final, correct statement of the type
    preservation property: *)

Definition preservation_theorem := forall ST t t' T st st',
  <{ empty / ST ⊢ t ⦂ T }> →
  store_well_typed ST st →
  t / st ⟶ t' / st' →
  exists ST',
     extends ST' ST /\
     <{ empty / ST' ⊢ t' ⦂ T }> /\
     store_well_typed ST' st'.

(** FULL: Note that the preservation theorem merely asserts that there
    is _some_ store typing [ST'] extending [ST] (i.e., agreeing with
    [ST] on the values of all the old locations) such that the new
    term [t'] is well typed with respect to [ST']; it does not tell us
    exactly what [ST'] is.  It is intuitively clear, of course, that
    [ST'] is either [ST] or else exactly [ST ++ τ₁::nil], where [τ₁]
    is the type of the value [v₁] in the extended store [st ++
    v₁::nil], but stating this explicitly would complicate the
    statement of the theorem without making it any more useful: the
    weaker version above is already in the right form (because its
    conclusion implies its hypothesis) to "turn the crank" repeatedly
    and conclude that every _sequence_ of reduction steps preserves
    well-typedness.  Combining this with the progress property, we
    obtain the usual guarantee that "well-typed programs never go
    wrong."

    In order to prove this, we'll need a few lemmas, as usual. *)
(** TERSE: This gives us just what we need to "turn the
    crank" when applying the theorem to multi-step reduction
    sequences. *)

(* TERSE: HIDEFROMHTML *)
(* ################################### *)
(** ** Substitution Lemma *)

(** TERSE: To prove preservation, we need to re-develop the rest of
    the machinery that we saw for the pure STLC (plus a couple of new
    things about store typings and extension)... *)
(** FULL: First, we need an easy extension of the standard substitution
    lemma, along with the same machinery about context invariance that
    we used in the proof of the substitution lemma for the STLC. *)

Lemma weakening : forall Γ Gamma' ST t T,
     includedin Γ Gamma' →
     <{ Γ / ST ⊢ t ⦂ T }> →
     <{ Gamma' / ST ⊢ t ⦂ T }>.
Proof.
  intros Γ Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Γ ST t T,
     <{ empty / ST ⊢ t ⦂ T }> →
     <{ Γ / ST ⊢ t ⦂ T }>.
Proof.
  intros Γ ST t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Γ ST x U t v T,
  <{ x |→ U; Γ / ST ⊢ t ⦂ T }> →
  <{ empty / ST ⊢ v ⦂ U }>  →
  <{ Γ / ST ⊢ [x:=v]t ⦂ T }>.
(* FOLD *)
Proof.
  intros Γ ST x U t v T Ht Hv.
  generalize dependent Γ. generalize dependent T.
  induction t; intros T Γ H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (String.eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
(* INSTRUCTORS: Inconsistent between 8.12.0 and 8.12.1!
   rename t0 into T. *)
    rename s into y.
    destruct (String.eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Assignment Preserves Store Typing *)

(** Next, we must show that replacing the contents of a cell in the
    store with a new value of appropriate type does not change the
    overall type of the store.  (This is needed for the [assign]
    rule.) *)

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st →
  store_well_typed ST st →
  <{ empty / ST ⊢ t ⦂ $(store_Tlookup l ST) }> →
  store_well_typed ST (replace l t st).
(* FOLD *)
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (l' =? l) eqn: Heqll'.
  - (* l' = l *)
    apply eqb_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply eqb_neq in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.
(* /FOLD *)

(* ######################################## *)
(** ** Weakening for Stores *)

(** Finally, we need a lemma on store typings, stating that, if a
    store typing is extended with a new location, the extended one
    still allows us to assign the same types to the same terms as the
    original. *)

Lemma store_weakening : forall Γ ST ST' t T,
  extends ST' ST →
  <{ Γ / ST ⊢ t ⦂ T }> →
  <{ Γ / ST' ⊢ t ⦂ T }>.
(* FOLD *)
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply T_Loc.
    eapply length_extends...
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** We can use the [store_weakening] lemma to prove that if a store is
    well typed with respect to a store typing, then the store extended
    with a new term `τ` will still be well typed with respect to the
    store typing extended with `τ`'s type. *)

Lemma store_well_typed_app : forall ST st t₁ τ₁,
  store_well_typed ST st →
  <{ empty / ST ⊢ t₁ ⦂ τ₁ }> →
  store_well_typed (ST ++ τ₁::nil) (st ++ t₁::nil).
(* FOLD *)
Proof with auto.
  intros.
  unfold store_well_typed in *.
  destruct H as [Hlen Hmatch].
  rewrite app_length, add_comm. simpl.
  rewrite app_length, add_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      apply <-Nat.succ_lt_mono in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- Hlen.
      rewrite sub_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. }
      rewrite app_nth2; [|lia].
      rewrite sub_diag. simpl. assumption.
Qed.
(* /FOLD *)

(* ################################### *)
(** ** Preservation! *)

(** Now that we've got everything set up right, the proof of
    preservation is actually quite straightforward.  *)

(* TERSE: HIDEFROMHTML *)
(** Begin with one technical lemma: *)

Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
(* FOLD *)
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.
(* /FOLD *)

(** And here, at last, is the preservation theorem: *)

Theorem preservation : forall ST t t' T st st',
  <{ empty / ST ⊢ t ⦂ T }> →
  store_well_typed ST st →
  t / st ⟶ t' / st' →
  exists ST',
     extends ST' ST /\
     <{ empty / ST' ⊢ t' ⦂ T }> /\
     store_well_typed ST' st'.
(* FOLD *)
Proof with eauto using store_weakening, extends_refl.
  remember empty as Γ.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  induction Ht; intros t' HST Hstep;
    subst; try solve_by_invert; inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  (* T_App *)
  - (* appAbs *) exists ST.
    inversion Ht1; subst.
    split; try split... eapply substitution_preserves_typing...
  - (* app₁ *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  - (* app₂ *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  - (* T_Succ *)
    + (* ST_Succ *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty```.
      exists ST'...
  - (* T_Pred *)
    + (* ST_Pred *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty```.
      exists ST'...
  (* T_Mult *)
  - (* ST_Mult1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  - (* ST_Mult2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  - (* T_If0 *)
    + (* ST_If0_1 *)
      eapply IHHt1 in H0...
      destruct H0 as [ST' [Hext [Hty Hsty```.
      exists ST'. split...
  (* ref *)
  - (* refValue *)
    exists (ST ++ τ₁::nil).
    inversion HST; subst.
    split.
    { apply extends_app. }
    split.
    { replace <{{ Ref τ₁ }}>
        with <{{ Ref $(store_Tlookup (length st) (ST ++ τ₁::nil)) }}>.
      { apply T_Loc.
        rewrite <- H. rewrite app_length, add_comm. simpl. lia. }
      unfold store_Tlookup. rewrite <- H. rewrite nth_eq_last.
      reflexivity. }
    apply store_well_typed_app; assumption.
  - (* ref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  (* deref *)
  - (* derefLoc *)
    exists ST. split; try split...
    destruct HST as [_ Hsty].
    replace τ₁ with (store_Tlookup l ST).
    apply Hsty...
    inversion Ht; subst...
  - (* deref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  (* assign *)
  - (* assign *)
    exists ST. split; try split...
    eapply assign_pres_store_typing...
    inversion Ht1; subst...
  - (* assign₁ *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty```.
    exists ST'...
  - (* assign₂ *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty```.
    exists ST'...
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* TERSE: HIDEFROMHTML *)
::::exercise (rating := 3) (name := "preservation_informal") (manual := true)
(** Write a careful informal proof of the preservation theorem,
    concentrating on the [T_App], [deref], [assign], and [ref]
    cases.

(* SOLUTION *)
    _Proof_: By induction on a derivation of [empty / [] ⊢ t : T].

    - If the last rule in the derivation is [T_App], then [t = t₁ t₂]
      for some `t₁` and `t₂` and [T = T12], with [empty / ST ⊢ t₁ :
      T11→T12] and [empty / ST ⊢ t₁ : T11].  There are three cases to
      consider, one for each rule that could have been used to show
      that [t₁ t₂] takes a step to [t'].

        - Suppose [t₁ t₂] takes a step by [app₁], with `t₁`
          stepping to [t₁'] and new store `st'`.  Then by the IH there
          is some store typing [ST'] such that [ST'] extends [ST],
          `st'` is well typed with respect to [ST'], and [empty / ST'
          ⊢ t₁' : T11→T12].  We also know [empty / ST' ⊢ t₂ : T11]
          by the [store_weakening] lemma.  Hence, [empty / ST' ⊢ t₁'
          t₂] by [T_App].

        - The [app₂] case is similar.

        - Suppose [t₁ t₂] takes a step by [appAbs].  Then [t₁ =
          λx:T11,t12] and [t₁ t₂] steps to `[x:=t₂]t12]; the
          desired result now follows from the substitution lemma,
          taking [ST' = ST].

    - If the last rule in the derivation is [ref], then [t = ref t₁]
      for some `t₁` and [empty / ST ⊢ t₁ : τ₁] for some [τ₁], with [T
      = Ref τ₁].  There are two cases to consider, one for each rule
      that could have been used to show that [ref t₁] takes a step to
      [t'].

        - Suppose [ref t₁] takes a step by [ref], with `t₁`
          stepping to [t₁'] and new store `st'`.  Then by the IH there
          is some store typing [ST'] such that [ST'] extends [ST],
          `st'` is well typed with respect to [ST'], and [empty / ST'
          ⊢ t₁' : τ₁].  Hence, [empty / ST' ⊢ ref t₁' : Ref τ₁] by
          [ref].

        - Suppose [ref t₁] takes a step by [refValue].  Then `t₁`
          is a value, [st' = st ++ t₁::nil], and [t'] is the length of
          `st` -- i.e., the location of `t₁` in `st'`.  If we choose
          [ST' = ST ++ τ₁::nil], we obtain
             - [ST'] extends [ST] by construction
             - `st'` is well typed with respect to [ST'] because `st`
               is well typed with respect to [ST] and the last
               element, `t₁`, has type [τ₁] under [ST],
               hence also under [ST'] by the store
               weakening lemma
             - [empty / ST' ⊢ l : Ref τ₁] by [T_Loc]
          as required.

    - If the last rule in the derivation is [deref], then [t = !t1]
      for some `t₁` and [empty / ST ⊢ t₁ : Ref τ].  There are two
      cases to consider, one for each rule that could have been used
      to show that [!t1] takes a step to [t'].

        - Suppose [!t1] takes a step by [deref], with `t₁` stepping
          to [t₁'] and new store `st'`.  Then by the IH there is some
          store typing [ST'] such that [ST'] extends [ST], `st'` is
          well typed with respect to [ST'], and [empty / ST' ⊢ t₁' :
          Ref τ].  Hence, [empty / ST' ⊢ !t₁' : T] by [deref].

        - Suppose [ref t₁] takes a step by [derefLoc].  Then `t₁`
          is some location `l` and [t'] is the contents of `st` at
          location `l`.  Moreover, the typing rule used to derive
          [empty / ST ⊢ l : Ref τ] must be [T_Loc], so the contents of
          [ST] at location `l` is `τ`.  Now, since `st` is well typed
          with respect to [ST], we know that [empty / ST ⊢ t' : T], as
          required.

    - If the last rule in the derivation is [assign], then [t = t₁
      := t₂] for some `t₁` and `t₂`, with [empty / ST ⊢ t₁ : Ref τ₂]
      and [empty / ST ⊢ t₂ : τ₂] for some [τ₂]; moreover, [T = Unit].
      There are now three cases to consider, one for each rule that
      could have been used to show that [t₁ := t₂] takes a step to
      [t'].

        - The cases where [t₁ := t₂] takes a step by either
          [assign₁] or [assign₂] are similar to the congruence
          rule cases above.

        - Suppose [t₁ := t₂] takes a step by [assign].  Then `t₁`
          is some location `l`, `t₂` is some value, [t'] is `unit`,
          and `st'` is formed from `st` by updating the contents of
          location `l` with `t₂`.

          Moreover, the typing rule used to derive [empty / ST ⊢ l :
          Ref τ₂] must be [T_Loc], so the contents of [ST] at location
          `l` is [τ₂].  Now, [empty / ST ⊢ unit : Unit] by [T_Unit].
          Moreover, since `st` is well typed with respect to [ST] and
          we know [empty / ST ⊢ t₂ : τ₂], we know that `st'` is well
          typed with respect to [ST] by lemma
          [assign_pres_store_typing].  So we can take [ST' = ST] and
          finish this case.

    - (Other cases elided...)

(* /SOLUTION *)
*)

(* GRADE_MANUAL 3: preservation_informal *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(* ################################### *)
(** ** Progress *)

(** As we've said, progress for this system is pretty easy to prove;
    the proof is very similar to the proof of progress for the STLC,
    with a few new cases for the new syntactic constructs. *)

Theorem progress : forall ST t T st,
  <{ empty / ST ⊢ t ⦂ T }> →
  store_well_typed ST st →
  (value t \/ exists t' st', t / st ⟶ t' / st').
(* FOLD *)
Proof with eauto.
  intros ST t T st Ht HST. remember empty as Γ.
  induction Ht; subst; try solve_by_invert...
  - (* T_App *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t₂ steps *)
        destruct Ht2p as [t₂' [st' Hstep```.
        exists <{ (λx0 : T0, t0) t₂' }>, st'...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ t₁' t₂ }>, st'...
  - (* T_Succ *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve [ inversion Ht ].
      * (* t₁ is a const *)
        exists <{ $(S n) }>, st...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ succ t₁' }>, st'...
  - (* T_Pred *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve [inversion Ht ].
      * (* t₁ is a const *)
        exists <{ $(n - 1) }>, st...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ pred t₁' }>, st'...
  - (* T_Mult *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t₂ is a value *)
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists <{ $(n * n0) }>, st...
      * (* t₂ steps *)
        destruct Ht2p as [t₂' [st' Hstep```.
        exists <{ n * t₂' }>, st'...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ t₁' * t₂ }>, st'...
  - (* T_If0 *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      * (* n = 0 *) exists t₂, st...
      * (* n = S n' *) exists t3, st...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ if0 t₁' then t₂ else t3 }>, st'...
  - (* ref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ref t₁'}>, st'...
  - (* deref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t₁ is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      eexists. eexists. apply derefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ ! t₁' }>, st'...
  - (* assign *)
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    + (* t₁ is a value *)
      destruct IHHt2 as [Ht2p|Ht2p]...
      * (* t₂ is a value *)
        inversion Ht1p; subst; try solve_by_invert.
        eexists. eexists. apply assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H4...
      * (* t₂ steps *)
        destruct Ht2p as [t₂' [st' Hstep```.
        exists <{ t₁ := t₂' }>, st'...
    + (* t₁ steps *)
      destruct Ht1p as [t₁' [st' Hstep```.
      exists <{ t₁' := t₂ }>, st'...
Qed.
(* /FOLD *)

(* ################################### *)
(** * References and Nontermination *)

(** An important fact about the STLC (proved in chapter \CHAP{Norm})
    is that it is is _normalizing_ -- that is, every well-typed term
    can be reduced to a value in a finite number of steps.

    What about STLC + references?  Surprisingly, adding references
    causes us to lose the normalization property: there exist
    well-typed terms in the STLC + references which can continue to
    reduce forever, without ever reaching a normal form! *)

(** TERSE: *** *)

(** How can we construct such a term?  The main idea is to make a
    function which calls itself.  We first make a function which calls
    another function stored in a reference cell; the trick is that we
    then smuggle in a reference to itself!
```
   (\r:Ref (Unit → Unit),
        r := (λx:Unit,(!r) unit); (!r) unit)
   (ref (λx:Unit,unit))
```
*)

(** FULL: First, [ref (λx:Unit,unit)] creates a reference to a cell of
    type [Unit → Unit].  We then pass this reference as the argument
    to a function which binds it to the name `r`, and assigns to it
    the function [λx:Unit,(!r) unit] -- that is, the function which
    ignores its argument and calls the function stored in `r` on the
    argument `unit`; but of course, that function is itself!  To start
    the divergent loop, we execute the function stored in the cell by
    evaluating [(!r) unit].

   Here is the divergent term in Rocq: *)
(* SOONER: Anton suggests that the program given above would be easier to
   understand for the reader if it was first presented in the form
   [let r = ref (fun (x : unit) → ()) in
    r := (fun (x : unit) → !r ());
    !r ()]
   or even
   [let r = ref (fun (_ : unit) → ()) in
    r := (fun (_ : unit) → !r ());
    !r ()] *)

(* TERSE: HIDEFROMHTML *)
Module ExampleVariables.

(* NOTATION: LATER: Urg: Here they are definitions, not notations.  Try to make
   this consistent with MoreStlc, Stlc, etc. *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".

End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  <{ λx : Unit, (!r) unit }>.

Definition loop :=
  <{ (\r : Ref (Unit → Unit),
        (( r := loop_fun );
        ( (! r) unit ) ))
     (ref (λx : Unit, unit)) }> .
(** This term is well typed: *)

Import ListNotations.

Lemma loop_typeable : exists T, <{ empty / [] ⊢ loop ⦂ T }>.
(* FOLD *)
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply deref. eapply T_Var.
    rewrite update_neq; [|intros; discriminate].
    rewrite update_eq. reflexivity. auto.
  eapply assign.
    eapply T_Var. rewrite update_eq. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply deref. eapply T_Var. reflexivity.
Qed.
(* /FOLD *)

(** To show formally that the term diverges, we first define the
    [step_closure] of the single-step reduction relation, written
    [⟶+].  This is just like the reflexive step closure of
    single-step reduction (which we're been writing [⟶*]), except
    that it is not reflexive: [t ⟶+ t'] means that `τ` can reach
    [t'] by _one or more_ steps of reduction. *)

Inductive step_closure {X:Type} (R: relation X) : X → X → Prop :=
  | sc_one  : forall (x y : X),
                R x y → step_closure R x y
  | sc_step : forall (x y z : X),
                R x y →
                step_closure R y z →
                step_closure R x z.

Definition multistep1 := (step_closure step).
Notation "t₁ '/' st '⟶+' t₂ '/' st'" :=
        (multistep1 (t₁,st) (t₂,st'))
        (at level 40, st at level 39, t₂ at level 39).

(** Now, we can show that the expression [loop] reduces to the
    expression [!(loc 0) unit] and the size-one store
    ```r:=(loc 0)]loop_fun]. *)

(* LATER: Maybe this one belongs in MoreStlc.v? *)
(** As a convenience, we introduce a slight variant of the [normalize]
    tactic, called [reduce], which tries solving the goal with
    [multi_refl] at each step, instead of waiting until the goal can't
    be reduced any more. Of course, the whole point is that [loop]
    doesn't normalize, so the old [normalize] tactic would just go
    into an infinite loop reducing it forever! *)

Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | compute];
            try solve [apply multi_refl]).

(** Next, we use [reduce] to show that [loop] steps to
    [!(loc 0) unit], starting from the empty store. *)

Lemma loop_steps_to_loop_fun :
  loop / nil ⟶*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.

(** Finally, we show that the latter expression reduces in
    two steps to itself! *)

Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil ⟶+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
(* FOLD *)
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply app₁...
  eapply sc_one. compute. apply appAbs...
Qed.
(* /FOLD *)

(* EX4 (factorial_ref) *)
(* GRADE_THEOREM 3: factorial *)
(* GRADE_THEOREM 3: factorial_type *)
(** Use the above ideas to implement a factorial function in STLC with
    references.  (There is no need to prove formally that it really
    behaves like the factorial.  Just uncomment the example below to make
    sure it gives the correct result when applied to the argument
    [4].) *)
(* SOONER: a bit more explanation here?  (YES!) *)

Definition factorial : Tm
  (* ADMITDEF *) :=
<{
  (\r : (Ref (Nat → Nat) ),
        (r := (λx : Nat, if0 x then 1 else (x * ( (!r) (pred x) ) ))); !r  )
  (ref (λx : Nat, x))
  }>.
(* /ADMITDEF *)

Lemma factorial_type : <{ empty / nil ⊢ factorial ⦂ (Nat → Nat) }>.
Proof with eauto.
  (* ADMITTED *)
  unfold factorial.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
  eapply assign...
  eapply T_Abs...
  eapply T_If0...
  eapply T_Mult...
  eapply T_App...
  eapply deref...
Qed.
(* /ADMITTED *)

(** If your definition is correct, you should be able to just
    uncomment the example below; the proof should be fully
    automatic using the [reduce] tactic. *)

(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
Lemma factorial_4 : exists st,
  <{ factorial 4 }> / nil ⟶* tm_const 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(** [] *)

(* ################################### *)
(** * Additional Exercises *)

(* EX5? (garbage_collector) *)
(** Challenge problem: modify our formalization to include an account
    of garbage collection, and prove that it satisfies whatever nice
    properties you can think to prove about it. *)
(** [] *)

End RefsAndNontermination.
End STLCRef.
(* TERSE: /HIDEFROMHTML *)
