# Software Verification

The promise of theorem provers extends beyond mathematics. We can verify that software does what we claim it does. This chapter builds a small interpreter for an expression language and proves properties about compiler optimizations. Then we demonstrate bisimulation: proving that a production Rust implementation matches a verified Lean specification.

## Intrinsically-Typed Interpreters

The standard approach to building interpreters involves two phases. First, parse text into an untyped abstract syntax tree. Second, run a type checker that rejects malformed programs. This works, but the interpreter must still handle the case where a program passes the type checker but evaluates to nonsense. The runtime carries the burden of the type system's failure modes.

Intrinsically-typed interpreters take a different approach. The abstract syntax tree itself encodes typing judgments. An ill-typed program cannot be constructed. The type system statically excludes runtime type errors, not by checking them at runtime, but by making them unrepresentable.

Consider a small expression language with natural numbers, booleans, arithmetic, and conditionals. We start by defining the types our language supports and a denotation function that maps them to Lean types.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:types}}
```

The `denote` function is key. It interprets our object-level types (`Ty`) as meta-level types (`Type`). When our expression language says something has type `nat`, we mean it evaluates to a Lean `Nat`. When it says `bool`, we mean a Lean `Bool`. This type-level interpretation function is what makes the entire approach work.

## Expressions

The expression type indexes over the result type. Each constructor precisely constrains which expressions can be built and what types they produce.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:expr}}
```

Every constructor documents its typing rule. The `add` constructor requires both arguments to be natural number expressions and produces a natural number expression. The `ite` constructor requires a boolean condition and two branches of matching type.

This encoding makes ill-typed expressions unrepresentable. You cannot write `add (nat 1) (bool true)` because the types do not align. The Lean type checker rejects such expressions before they exist.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:impossible}}
```

## Evaluation

The evaluator maps expressions to their denotations. Because expressions are intrinsically typed, the evaluator is total. It never fails, never throws exceptions, never encounters impossible cases. Every pattern match is exhaustive.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:eval}}
```

The return type `t.denote` varies with the expression's type index. A natural number expression evaluates to `Nat`. A boolean expression evaluates to `Bool`. This dependent return type is what makes the evaluator type-safe by construction.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:examples}}
```

## Verified Optimization

Interpreters become interesting when we transform programs. A constant folder simplifies expressions by evaluating constant subexpressions at compile time. Adding two literal numbers produces a literal. Conditionals with constant conditions eliminate the untaken branch.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:constfold}}
```

The optimization preserves types. If `e : Expr t`, then `e.constFold : Expr t`. The type indices flow through unchanged. This is not a dynamic property we hope holds. It is a static guarantee enforced by the type system.

But type preservation is a weak property. We want semantic preservation: the optimized program computes the same result as the original. This requires a proof.

```lean
{{#include ../../src/ZeroToQED/Verification.lean:correctness}}
```

The theorem states that for any expression, evaluating the constant-folded expression yields the same result as evaluating the original. The proof proceeds by structural induction on the expression. Most cases follow directly from the induction hypotheses.

## Bisimulation: Connecting Specification to Implementation

The interpreter example shows verification within Lean. But real systems are written in languages like Rust, C, or Go. How do we connect a verified specification to a production implementation?

The answer is bisimulation. We write the specification in Lean, prove properties about it, then demonstrate that an implementation in another language computes identical results. If both systems agree on all observable behaviors, the implementation inherits the specification's guarantees.

We need an example small enough to understand, powerful enough to have non-trivial emergent behavior, and simple enough that we can prove things about it. Conway's Game of Life fits perfectly.

## The Game of Life

The Game of Life is a cellular automaton with three rules. A cell is born if it has exactly three neighbors. A cell survives if it has two or three neighbors. Otherwise, it dies. From these three rules emerges Turing-complete computation.

```
The Rules:
  Birth:    Dead cell with exactly 3 neighbors becomes alive
  Survival: Live cell with 2 or 3 neighbors stays alive
  Death:    All other live cells die
```

The state space explodes quickly. A 64x64 grid has 2^4096 possible configurations. Yet the rules fit in three lines. This tension between simple rules and complex behavior makes cellular automata ideal verification targets.

Consider the blinker, the simplest oscillator:

```
Step 0:     Step 1:     Step 2:
.....       .....       .....
..#..       .....       ..#..
..#..  -->  .###.  -->  ..#..
..#..       .....       ..#..
.....       .....       .....
```

The three vertical cells become three horizontal cells, then return to vertical. Period two.

The glider is more interesting. It translates across the grid:

```
Step 0:     Step 1:     Step 2:     Step 3:     Step 4:
.#....      ..#...      ......      ......      ......
..#...      ...#..      .#.#..      ...#..      ..#...
###...  --> .##...  --> ..##..  --> .#.#..  --> ...#..
......      ..#...      ..#...      ..##..      .###..
......      ......      ......      ......      ......
```

After four steps, the glider has moved one cell diagonally and returned to its original shape. This is not obvious from the rules. It is an emergent property that requires proof.

## The Lean Specification

We represent a grid as an array of arrays of booleans. The step function counts neighbors and applies the rules:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:grid}}
```

Neighbor counting handles wraparound at the edges (toroidal topology):

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:neighbors}}
```

The step function applies the rules to every cell:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:step}}
```

We define the patterns we want to verify:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:patterns}}
```

Now the proofs. Because the grid is finite and all operations are decidable, we can use `native_decide` to verify properties by computation:

```lean
{{#include ../../src/ZeroToQED/GameOfLife.lean:proofs}}
```

Four theorems, each proven by exhaustive evaluation. The blinker oscillates between two phases. The blinker has period two. The glider translates after four steps. The block is stable. These are not conjectures. They are machine-verified facts.

## The Rust Implementation

The production implementation lives in `examples/game-of-life/`. It uses const generics for grid dimensions and optimized array operations:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Grid<const N: usize, const M: usize> {
    cells: [[bool; M]; N],
}

impl<const N: usize, const M: usize> Grid<N, M> {
    fn count_neighbors(&self, i: usize, j: usize) -> u8 {
        let mut count = 0u8;
        for di in [N - 1, 0, 1] {
            for dj in [M - 1, 0, 1] {
                if di == 0 && dj == 0 { continue; }
                let ni = (i + di) % N;
                let nj = (j + dj) % M;
                if self.cells[ni][nj] { count += 1; }
            }
        }
        count
    }

    pub fn step(&self) -> Self {
        let mut next = Self::dead();
        for i in 0..N {
            for j in 0..M {
                let neighbors = self.count_neighbors(i, j);
                let alive = self.cells[i][j];
                next.cells[i][j] = matches!(
                    (alive, neighbors),
                    (true, 2) | (true, 3) | (false, 3)
                );
            }
        }
        next
    }
}
```

The Rust tests mirror the Lean theorems:

```rust
#[test]
fn blinker_has_period_2() {
    let b0 = blinker();
    let b1 = b0.step();
    let b2 = b1.step();
    assert_eq!(b1, blinker_phase2());
    assert_eq!(b2, b0);
}

#[test]
fn glider_translates_after_4_steps() {
    let g0 = glider();
    let g4 = g0.step_n(4);
    assert_eq!(g4, glider_translated());
}
```

Both systems compute the same results. The Lean specification is proven correct. The Rust implementation passes the same tests. When they agree, we have confidence that the Rust code inherits the Lean proofs.

## The Verification Gap

This is not full formal verification of the Rust code. We have not machine-checked that the Rust implementation matches the Lean specification for all inputs. We have demonstrated agreement on specific test cases and proven properties of the specification.

Full bisimulation would require either:

1. Extracting executable code from Lean proofs
2. Using a tool like RustBelt to verify Rust code in Coq
3. Building a verified compiler from Lean to Rust

These approaches exist but require significant infrastructure. For many systems, the pattern shown here is the pragmatic middle ground: prove properties of a clean specification, test agreement with the production implementation, and gain confidence without the overhead of full verification.

## What We Proved

The blinker oscillates with period two. The glider translates diagonally after four steps. The block remains stable indefinitely. These facts hold for all initial conditions matching those patterns, on grids of specified sizes, with toroidal boundary conditions.

The proofs are computational. Lean evaluates the step function, compares the results, and confirms equality. For small finite structures, this approach is complete and automatic. The `native_decide` tactic compiles the decision procedure to native code and runs it.

## Closing Thoughts

Finding good verification examples is hard. The system must be small enough to specify cleanly, complex enough to have non-trivial properties, and simple enough that proofs are tractable. The Game of Life threads this needle. Three rules generate gliders, guns, and universal computation. Yet the rules are simple enough to prove properties by exhaustive evaluation.

The pattern extends to real systems. Specify the core algorithm in Lean. Prove the properties you care about. Implement in your production language. Test agreement. This is not the same as full verification, but it catches bugs that testing alone would miss.

Future chapters might explore token ring protocols for distributed systems, or verified state machines for financial systems. The Game of Life is a starting point, not an ending. The techniques demonstrated here apply wherever correctness matters and complexity threatens to overwhelm informal reasoning.
