-- Word Frequency Counter
-- Run with: lake exe wordfreq "your text here"

import Std.Data.HashMap

open Std in
def wordFrequency (text : String) : HashMap String Nat :=
  let words := text.toLower.splitOn " "
  words.foldl (init := HashMap.emptyWithCapacity) fun acc word =>
    let count := acc.getD word 0
    acc.insert word (count + 1)

def main (args : List String) : IO Unit := do
  let text := match args.head? with
    | some t => t
    | none => "the spice must flow the spice extends life the spice expands consciousness"

  IO.println "Word Frequency Counter"
  IO.println "======================"
  IO.println s!"Text: \"{text}\""
  IO.println ""
  IO.println "Frequencies:"

  let freq := wordFrequency text
  for (word, count) in freq.toList do
    IO.println s!"  {word}: {count}"
