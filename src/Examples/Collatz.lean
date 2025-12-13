-- Collatz Conjecture Explorer
-- Run with: lake exe collatz [number]

def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

def collatzSequence (n : Nat) (fuel : Nat := 10000) : List Nat :=
  match fuel with
  | 0 => [n]
  | fuel' + 1 =>
    if n <= 1 then [n]
    else n :: collatzSequence (collatzStep n) fuel'

def collatzLength (n : Nat) : Nat :=
  (collatzSequence n).length

def collatzPeak (n : Nat) : Nat :=
  (collatzSequence n).foldl max 0

def longestCollatz (n : Nat) : Nat × Nat :=
  (List.range n).map (· + 1)
    |>.map (fun k => (k, collatzLength k))
    |>.foldl (fun acc pair => if pair.2 > acc.2 then pair else acc) (1, 1)

def formatSequence (seq : List Nat) : String :=
  let parts := seq.map toString
  if parts.length <= 20 then
    String.intercalate " -> " parts
  else
    let first := (parts.take 10).toArray
    let last := (parts.drop (parts.length - 5)).toArray
    String.intercalate " -> " first.toList ++ " -> ... -> " ++
    String.intercalate " -> " last.toList

def main (args : List String) : IO Unit := do
  let n := match args.head? >>= String.toNat? with
    | some n => if n > 0 then n else 27
    | none => 27

  IO.println s!"Collatz Conjecture Explorer"
  IO.println s!"==========================="
  IO.println ""
  IO.println s!"Starting value: {n}"

  let seq := collatzSequence n
  let len := seq.length
  let peak := collatzPeak n

  IO.println s!"Stopping time: {len} steps"
  IO.println s!"Peak value: {peak}"
  IO.println ""
  IO.println s!"Sequence:"
  IO.println (formatSequence seq)

  if n <= 100 then
    IO.println ""
    let (best, bestLen) := longestCollatz 100
    IO.println s!"Longest sequence from 1-100: {best} with {bestLen} steps"

  IO.println ""
  IO.println "The conjecture remains unproven. Will your number reach 1?"
  IO.println "(Spoiler: It will. We just cannot prove it always does.)"
