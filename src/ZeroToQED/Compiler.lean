/-!
# A Verified Compiler

A complete verified compiler in 40 lines. We define a source language,
a target language, compilation, and prove the compiler correct.

This is CompCert in miniature.
-/

namespace ZeroToQED.Compiler

-- ANCHOR: verified_compiler
-- Source: arithmetic expressions
inductive Expr where
  | lit : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
deriving Repr

-- Target: stack machine instructions
inductive Instr where
  | push : Nat → Instr
  | add : Instr
  | mul : Instr
deriving Repr

-- What an expression means: evaluate to a number
def eval : Expr → Nat
  | .lit n => n
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

-- Compile expression to stack code
def compile : Expr → List Instr
  | .lit n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

-- Execute stack code
def run : List Instr → List Nat → List Nat
  | [], stack => stack
  | .push n :: is, stack => run is (n :: stack)
  | .add :: is, b :: a :: stack => run is ((a + b) :: stack)
  | .mul :: is, b :: a :: stack => run is ((a * b) :: stack)
  | _ :: is, stack => run is stack

-- Lemma: execution distributes over concatenation
theorem run_append (is js : List Instr) (s : List Nat) :
    run (is ++ js) s = run js (run is s) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    cases i with
    | push n => exact ih _
    | add => cases s with
      | nil => exact ih _
      | cons b s => cases s with
        | nil => exact ih _
        | cons a s => exact ih _
    | mul => cases s with
      | nil => exact ih _
      | cons b s => cases s with
        | nil => exact ih _
        | cons a s => exact ih _

-- THE THEOREM: the compiler is correct
-- Running compiled code pushes exactly the evaluated result
theorem compile_correct (e : Expr) (s : List Nat) :
    run (compile e) s = eval e :: s := by
  induction e generalizing s with
  | lit n => rfl
  | add a b iha ihb => simp [compile, run_append, iha, ihb, run, eval]
  | mul a b iha ihb => simp [compile, run_append, iha, ihb, run, eval]
-- ANCHOR_END: verified_compiler

-- ANCHOR: compiler_demo
-- Try it: (2 + 3) * 4
def expr : Expr := .mul (.add (.lit 2) (.lit 3)) (.lit 4)

#eval eval expr                  -- 20
#eval compile expr               -- [push 2, push 3, add, push 4, mul]
#eval run (compile expr) []      -- [20]

-- The theorem guarantees these always match. Not by testing. By proof.
-- ANCHOR_END: compiler_demo

end ZeroToQED.Compiler
