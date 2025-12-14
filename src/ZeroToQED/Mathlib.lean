/-
Mathlib Examples

Simple examples demonstrating Mathlib imports and usage.
-/

-- ANCHOR: mathlib_imports
-- Import specific modules for faster compilation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
-- ANCHOR_END: mathlib_imports

namespace ZeroToQED.Mathlib

-- ANCHOR: prime_example
-- Working with prime numbers from Mathlib
example : Nat.Prime 17 := by decide

example : ¬ Nat.Prime 15 := by decide

-- Every number > 1 has a prime factor
example (n : Nat) (h : n > 1) : ∃ p, Nat.Prime p ∧ p ∣ n := by
  have hn : n ≠ 1 := by omega
  exact Nat.exists_prime_and_dvd hn

-- Infinitely many primes: for any n, there's a prime ≥ n
example (n : Nat) : ∃ p, Nat.Prime p ∧ p ≥ n := by
  obtain ⟨p, hn, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, hn⟩
-- ANCHOR_END: prime_example

-- ANCHOR: algebra_example
-- Using algebraic structures

-- Groups: every element has an inverse
example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a

-- Rings: distributivity comes for free
example {R : Type*} [Ring R] (a b c : R) : a * (b + c) = a * b + a * c :=
  mul_add a b c

-- Commutativity in commutative rings
example {R : Type*} [CommRing R] (a b : R) : a * b = b * a :=
  mul_comm a b
-- ANCHOR_END: algebra_example

-- ANCHOR: real_example
-- Real number analysis

-- Reals are a field
example (x : ℝ) (h : x ≠ 0) : x * x⁻¹ = 1 :=
  mul_inv_cancel₀ h

-- Basic inequalities
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y :=
  add_pos hx hy

-- The triangle inequality
example (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le x y
-- ANCHOR_END: real_example

-- ANCHOR: tactic_example
-- Mathlib tactics in action

-- ring solves polynomial identities
example (x y : ℤ) : (x - y) * (x + y) = x^2 - y^2 := by ring

-- linarith handles linear arithmetic
example (x y z : ℚ) (h1 : x < y) (h2 : y < z) : x < z := by linarith

-- field_simp clears denominators
example (x : ℚ) (h : x ≠ 0) : (1 / x) * x = 1 := by field_simp

-- positivity proves positivity goals
example (x : ℝ) : 0 ≤ x^2 := by positivity

-- gcongr for monotonic reasoning
example (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by gcongr
-- ANCHOR_END: tactic_example

-- ANCHOR: search_example
-- Finding lemmas with exact? and apply?

-- When stuck, use exact? to find matching lemmas
example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n  -- exact? would suggest this

-- apply? finds lemmas whose conclusion matches goal
example (a b : Nat) (h : a ∣ b) (h2 : b ∣ a) : a = b := by
  exact Nat.dvd_antisymm h h2  -- apply? would find this
-- ANCHOR_END: search_example

end ZeroToQED.Mathlib
