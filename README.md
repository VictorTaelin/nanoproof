# Nanoproof

Nanoproof is a tiny dependently typed proof checker in one Haskell file. It
checks `.npf` files with:

- empty, unit, bit, fixpoint, Pi, Sigma, and equality types
- HOAS internally
- guarded reductions
- `rfl` and rewrite proofs
- a small type-directed enumerator for parsed types

## Install

```sh
ghc -O2 nanoproof.hs -o nanoproof
cp nanoproof ~/.local/bin/nanoproof
```

Make sure `~/.local/bin` is on `PATH`.

## Usage

Check a file:

```sh
nanoproof demo/mul_comm.npf
```

Enumerate inhabitants of a type expression using definitions from the file:

```sh
nanoproof demo/mul_comm.npf --enum Nat
```

## Demo

`demo/mul_comm.npf` defines Peano naturals, addition, multiplication, and proofs
including:

```text
proof : @x:Nat. mul2(x) == add(x, x)
mul_comm : @x:Nat. @y:Nat. mul(x, y) == mul(y, x)
```

## Syntax

Comments:

```text
// line comment
```

Definitions:

```text
Name = term;
name : Type = term;
```

Core forms:

```text
⊥              empty type
⊤              unit type
𝔹              bit type
μX.T           fixpoint
@A.B           non-binding Pi
@x:A.B         binding Pi sugar
&A.B           non-binding Sigma
&x:A.B         binding Sigma sugar
a == b         equality type
()             unit value
0 / 1          bit values
(a,b)          pair
λx.body        lambda
λ{}            empty eliminator
λ()body        unit eliminator
λ{0:a;1:b;}    bit eliminator
λ<>body        pair eliminator
rfl            reflexivity proof
!e; body       rewrite with equality proof e
```

Function application uses parentheses:

```text
add(x,y)
mul(x,y)
```

## Notes

Pi and Sigma codomains are ordinary terms used as families. A constant family is
written directly; a dependent family is written as a lambda or eliminator.

```text
@A.C
@x:A.B
@Bit.λ{0:A;1:B;}
```
