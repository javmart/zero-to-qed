-- JSON-like Serializer demonstrating type classes and polymorphism
-- Run with: lake exe json

-- A simple JSON value type
inductive Json where
  | null : Json
  | bool : Bool → Json
  | num : Int → Json
  | str : String → Json
  | arr : List Json → Json
  | obj : List (String × Json) → Json
  deriving Repr

-- Type class for things that can become JSON
class ToJson (α : Type) where
  toJson : α → Json

-- Type class for things that can be parsed from JSON
class FromJson (α : Type) where
  fromJson : Json → Option α

-- Basic instances
instance : ToJson Bool where
  toJson b := Json.bool b

instance : ToJson Int where
  toJson n := Json.num n

instance : ToJson Nat where
  toJson n := Json.num n

instance : ToJson String where
  toJson s := Json.str s

instance : FromJson Bool where
  fromJson
    | Json.bool b => some b
    | _ => none

instance : FromJson Int where
  fromJson
    | Json.num n => some n
    | _ => none

instance : FromJson Nat where
  fromJson
    | Json.num n => if n >= 0 then some n.toNat else none
    | _ => none

instance : FromJson String where
  fromJson
    | Json.str s => some s
    | _ => none

-- Polymorphic instance: if α is ToJson, so is List α
instance {α : Type} [ToJson α] : ToJson (List α) where
  toJson xs := Json.arr (xs.map ToJson.toJson)

instance {α : Type} [FromJson α] : FromJson (List α) where
  fromJson
    | Json.arr xs => xs.mapM FromJson.fromJson
    | _ => none

-- Polymorphic instance for Option
instance {α : Type} [ToJson α] : ToJson (Option α) where
  toJson
    | none => Json.null
    | some x => ToJson.toJson x

instance {α : Type} [FromJson α] : FromJson (Option α) where
  fromJson
    | Json.null => some none
    | j => (FromJson.fromJson j).map some

-- Pretty printer for JSON (another type class in action)
class Pretty (α : Type) where
  pretty : α → Nat → String  -- value and indent level

def indent (n : Nat) : String := String.mk (List.replicate (n * 2) ' ')

partial def prettyJson (j : Json) (depth : Nat) : String :=
  let ind := indent depth
  let ind1 := indent (depth + 1)
  match j with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => s!"\"{s}\""
  | .arr [] => "[]"
  | .arr xs =>
    let items := xs.map (prettyJson · (depth + 1))
    "[\n" ++ ind1 ++ (",\n" ++ ind1).intercalate items ++ "\n" ++ ind ++ "]"
  | .obj [] => "{}"
  | .obj kvs =>
    let pairs := kvs.map fun (k, v) =>
      s!"\"{k}\": {prettyJson v (depth + 1)}"
    "{\n" ++ ind1 ++ (",\n" ++ ind1).intercalate pairs ++ "\n" ++ ind ++ "}"

instance : Pretty Json where
  pretty := prettyJson

-- Example: a user-defined type with derived serialization
structure Hero where
  name : String
  level : Nat
  hp : Nat
  alive : Bool
  deriving Repr

-- Manual ToJson instance showing the pattern
instance : ToJson Hero where
  toJson h := Json.obj [
    ("name", ToJson.toJson h.name),
    ("level", ToJson.toJson h.level),
    ("hp", ToJson.toJson h.hp),
    ("alive", ToJson.toJson h.alive)
  ]

instance : FromJson Hero where
  fromJson
    | Json.obj kvs =>
      let lookup (k : String) : Option Json :=
        kvs.find? (·.1 == k) |>.map (·.2)
      do
        let name ← lookup "name" >>= FromJson.fromJson
        let level ← lookup "level" >>= FromJson.fromJson
        let hp ← lookup "hp" >>= FromJson.fromJson
        let alive ← lookup "alive" >>= FromJson.fromJson
        pure { name, level, hp, alive }
    | _ => none

-- A party of heroes
structure Party where
  name : String
  heroes : List Hero
  gold : Nat

instance : ToJson Party where
  toJson p := Json.obj [
    ("party_name", ToJson.toJson p.name),
    ("members", ToJson.toJson p.heroes),
    ("treasury", ToJson.toJson p.gold)
  ]

-- Generic function using multiple constraints
def roundTrip {α : Type} [ToJson α] [FromJson α] [Repr α] (x : α) : String :=
  let json := ToJson.toJson x
  match FromJson.fromJson (α := α) json with
  | some y => s!"Success: {repr y}"
  | none => "Failed to parse"

def main : IO Unit := do
  IO.println "JSON Serializer Demo"
  IO.println "===================="
  IO.println ""

  -- Create some heroes
  let gandalf : Hero := { name := "Gandalf", level := 99, hp := 500, alive := true }
  let frodo : Hero := { name := "Frodo", level := 10, hp := 50, alive := true }
  let boromir : Hero := { name := "Boromir", level := 25, hp := 0, alive := false }

  -- Create a party
  let fellowship : Party := {
    name := "Fellowship of the Ring"
    heroes := [gandalf, frodo, boromir]
    gold := 1000
  }

  IO.println "Serializing a Hero:"
  IO.println (Pretty.pretty (ToJson.toJson gandalf) 0)
  IO.println ""

  IO.println "Serializing a Party (nested polymorphic serialization):"
  IO.println (Pretty.pretty (ToJson.toJson fellowship) 0)
  IO.println ""

  IO.println "Round-trip test:"
  IO.println (roundTrip gandalf)
  IO.println ""

  IO.println "Polymorphic list serialization:"
  IO.println (Pretty.pretty (ToJson.toJson [1, 2, 3, 4, 5]) 0)
  IO.println ""

  IO.println "Option serialization:"
  IO.println s!"some 42 -> {Pretty.pretty (ToJson.toJson (some 42)) 0}"
  IO.println s!"none    -> {Pretty.pretty (ToJson.toJson (none : Option Int)) 0}"
