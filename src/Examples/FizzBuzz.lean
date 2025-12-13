-- FizzBuzz
-- Run with: lake exe fizzbuzz [limit]

def fizzbuzz (n : Nat) : String :=
  match n % 3 == 0, n % 5 == 0 with
  | true,  true  => "FizzBuzz"
  | true,  false => "Fizz"
  | false, true  => "Buzz"
  | false, false => toString n

def runFizzbuzz (limit : Nat) : List String :=
  (List.range limit).map fun i => fizzbuzz (i + 1)

def main (args : List String) : IO Unit := do
  let limit := match args.head? >>= String.toNat? with
    | some n => if n > 0 then n else 15
    | none => 15

  IO.println s!"FizzBuzz 1 to {limit}"
  IO.println "================="
  for s in runFizzbuzz limit do
    IO.println s
