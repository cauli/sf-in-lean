import SFLMeta
import Credits

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Preface" =>
%%%
tag := "Preface"
htmlSplit := .never
file := "Preface"
%%%

# Welcome

This is {volumeName}[], volume {volumeNumber}[] of _Software Foundations in
Lean_.  It develops _type systems_: static checks for establishing that _all_
programs in a given language are well behaved, in contrast to
{volumeName "hl"}[], which develops techniques for reasoning about the
behavior of a _specific_ program. The two volumes can be read in either
order, and both build on the material in {volumeName "lf"}[].

# Overview

To reason about a program, we represent it as a mathematical object
together with a mathematical function or relation for describing its
behavior. Our main approach to doing so is called _operational semantics_,
and it amounts to defining a kind of _abstract interpreter_ for
the programs in a language. We present two styles of operational semantics:
the _big-step_ style specifies a program's behavior by relating it directly to its final
value, while the _small-step_ style specifies a program's behavior as
a series of computational steps. The small-step approach is more involved,
but also makes it possible to reason about a program's evaluation in a more
fine-grained manner.

After introducing operational semantics using a simple language of arithmetic
and boolean expressions (Slang), we turn to _types_, the volume's
central subject. A type is a static classification of what a program computes,
and a _type system_ is a static reasoning system that uses types to rule out
whole categories of run-time errors before a program is ever run. Working with a
small language of numbers and booleans, we define a type system for it and
prove the two signature theorems of type-system metatheory — _progress_ (a
well-typed term is either a value or can take a step) and _preservation_
(taking a step preserves well-typedness) — which together guarantee that a
well-typed program can never "go wrong."

Finally, we turn our attention to the _simply typed lambda-calculus_ (STLC),
a much richer language with a more interesting type system. We start from a
small untyped core and extend it with numbers, pairs, sums, lists, and
general recursion, proving progress and preservation anew for the extended
language. We then study _subtyping_, a mechanism that lets a term of one
type stand in for a term of another — motivated by the way record types
behave in object-oriented languages — and prove progress and preservation
once more for a language with subtyping. In so doing, we work our way up
to a fairly full featured programming language.

# Practicalities

This volume assumes you already have Lean and VS Code set up as described in
the {volumeName "lf"}[] Preface, and that you are comfortable with the basic
mechanics of working through an SFL chapter. The exercises here have the
same "advanced"/"optional" markings, and star ratings.

Briefly (see the {volumeName "lf"}[] Preface for detail), to get started:

If you are using this book as part of a class, your instructor will have
created a "student" release for you; download and unzip it, open the
resulting directory in VS Code, and open a `.lean` file (e.g., `TS/Slang.lean`)
to get started.

If you are reading on your own, clone the
[SF-in-Lean](https://github.com/plclub/sf-in-lean) repository and run `make
ts-student` from the root directory to build the student version of this
volume; it is written to `_out/ts/student/`, with an `html/` directory and a
`lean/` directory, exactly as described for {volumeName "lf"}[]. Run `make
student` instead if you want all three volumes built together.

## Building on Your Own Copy of Logical Foundations

This project includes a copy of the {volumeName "lf"}[] files that chapters
in this volume depend on, in their own `LF/` directory, so you do not need a
separate {volumeName "lf"}[] download to build or read this volume. If you
have already worked through {volumeName "lf"}[] and would rather this volume
build on your own work, copy the whole `LF/` directory from your
{volumeName "lf"}[] download over this project's `LF/` directory, then
rebuild.

Exercises in this volume use the same star ratings, and the same
"advanced"/"optional" markings, described in the {volumeName "lf"}[]
Preface.

## Citation Format

If you want to refer to this volume in your own writing, please
do so as follows:

:::citation
:::

# For Potential Contributors

If you find things you'd like to help add or improve, your
contributions are welcome!  To get started, clone the
[SF-in-Lean git repo](https://github.com/plclub/sf-in-lean) and
have a look at `ALPHA-TESTERS.md`.

{include 2 Credits}
