# Nanoproof

Nanoproof is a tiny dependently typed proof checker in one Haskell file. It
checks `.npf` files with:

- empty, unit, bit, fixpoint, Pi, Sigma, and equality types
- `Set`, the type of types
- HOAS internally
- guarded reductions
- `{==}` and rewrite proofs

Nanoproof has no termination checker. Recursive definitions and fixpoints are
accepted as written, so users are responsible for keeping them terminating or
productive.

Nanoproof also uses a single universe, `Set : Set`, rather than a universe
hierarchy.

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

## Demo

`demo/mul_comm.npf` defines Peano naturals, addition, multiplication, and proofs
including:

```text
mul2_add_self : @x:Nat. mul2(x) == add(x, x)
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
name : type = term;
```

Unannotated `Name = term;` declarations are type aliases, so `term` must check
against `Set`. Annotated definitions first require `type : Set`, then check the
body against that type.

Core forms:

```text
Set            type of types
⊥              empty type
⊤              unit type
𝔹              bit type
μX.T           fixpoint
@A.F           Pi over explicit family F
@x:A.B         binding Pi sugar for @A.λx.B
&A.F           Sigma over explicit family F
&x:A.B         binding Sigma sugar for &A.λx.B
a == b         equality type
()             unit value
0 / 1          bit values
(a,b)          pair
λx.body        lambda
λ{}            empty eliminator
λ()body        unit eliminator
λ{0:a;1:b;}    bit eliminator
λ<>body        pair eliminator
{==}           reflexivity proof
!e; body       rewrite with equality proof e
```

Function application uses parentheses:

```text
add(x,y)
mul(x,y)
```

## Notes

Plain Pi and Sigma codomains are ordinary terms used as families, so `@A.F`
requires `F : @A.λ_.Set` and applies `F` to each `A` value. The binding forms
build that family for you. A constant codomain can be written with an unused
binder or an explicit lambda; `@A.C` is not a constant function type unless `C`
is already a family.

Types themselves are not functions. A type alias such as `Nat : Set` cannot be
applied as `Nat(x)`; only term-level functions and type families with Pi types
can be applied.

```text
@x:A.C
@A.λ_.C
@x:A.B
@Bit.λ{0:A;1:B;}
```
