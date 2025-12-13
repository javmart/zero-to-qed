/-!
# Type-Safe Units of Measurement

A demonstration of using phantom types and type classes to enforce dimensional
correctness at compile time with zero runtime overhead. The types exist only
in the compiler's mind; the generated code manipulates raw floats.
-/

-- Phantom types representing physical dimensions
-- These have no constructors and no runtime representation
structure Meters
structure Seconds
structure Kilograms
structure MetersPerSecond
structure MetersPerSecondSquared
structure Newtons
structure NewtonSeconds

-- A quantity is a value tagged with its unit type
-- At runtime, this is just a Float
structure Quantity (unit : Type) where
  val : Float
  deriving Repr

-- Type class for multiplying quantities with compatible units
class UnitMul (u1 u2 result : Type) where

-- Type class for dividing quantities with compatible units
class UnitDiv (u1 u2 result : Type) where

-- Define the dimensional relationships
instance : UnitDiv Meters Seconds MetersPerSecond where
instance : UnitDiv MetersPerSecond Seconds MetersPerSecondSquared where
instance : UnitMul Kilograms MetersPerSecondSquared Newtons where
instance : UnitMul Newtons Seconds NewtonSeconds where

-- Arithmetic operations that preserve dimensional correctness
def Quantity.add {u : Type} (x y : Quantity u) : Quantity u :=
  ⟨x.val + y.val⟩

def Quantity.sub {u : Type} (x y : Quantity u) : Quantity u :=
  ⟨x.val - y.val⟩

def Quantity.mul {u1 u2 u3 : Type} [UnitMul u1 u2 u3] (x : Quantity u1) (y : Quantity u2) : Quantity u3 :=
  ⟨x.val * y.val⟩

def Quantity.div {u1 u2 u3 : Type} [UnitDiv u1 u2 u3] (x : Quantity u1) (y : Quantity u2) : Quantity u3 :=
  ⟨x.val / y.val⟩

def Quantity.scale {u : Type} (x : Quantity u) (s : Float) : Quantity u :=
  ⟨x.val * s⟩

-- Smart constructors for readability
def meters (v : Float) : Quantity Meters := ⟨v⟩
def seconds (v : Float) : Quantity Seconds := ⟨v⟩
def kilograms (v : Float) : Quantity Kilograms := ⟨v⟩
def newtons (v : Float) : Quantity Newtons := ⟨v⟩
def newtonSeconds (v : Float) : Quantity NewtonSeconds := ⟨v⟩

-- Example: Computing velocity from distance and time
-- This compiles because Meters / Seconds = MetersPerSecond
def computeVelocity (distance : Quantity Meters) (time : Quantity Seconds)
    : Quantity MetersPerSecond :=
  distance.div time

-- Example: Computing force from mass and acceleration
-- This compiles because Kilograms * MetersPerSecondSquared = Newtons
def computeForce (mass : Quantity Kilograms) (accel : Quantity MetersPerSecondSquared)
    : Quantity Newtons :=
  mass.mul accel

-- Example: Computing impulse from force and time
-- This compiles because Newtons * Seconds = NewtonSeconds
def computeImpulse (force : Quantity Newtons) (time : Quantity Seconds)
    : Quantity NewtonSeconds :=
  force.mul time

-- The Mars Climate Orbiter scenario:
-- One team computes impulse in Newton-seconds
-- Another team expects the same units
-- The type system ensures they match

def thrusterImpulse : Quantity NewtonSeconds :=
  let force := newtons 450.0
  let burnTime := seconds 10.0
  computeImpulse force burnTime

-- This would NOT compile - you cannot add NewtonSeconds to Meters:
-- def nonsense := thrusterImpulse.add (meters 100.0)

-- This would NOT compile - you cannot pass Meters where Seconds expected:
-- def badVelocity := computeVelocity (meters 100.0) (meters 50.0)

-- The key insight: all the Quantity wrappers and phantom types vanish at runtime.
-- The generated code is just floating-point arithmetic.
-- The safety is free.

def main : IO Unit := do
  let distance := meters 100.0
  let time := seconds 9.58  -- Usain Bolt's 100m record
  let velocity := computeVelocity distance time

  IO.println s!"Distance: {distance.val} m"
  IO.println s!"Time: {time.val} s"
  IO.println s!"Velocity: {velocity.val} m/s"

  let mass := kilograms 1000.0
  let accel : Quantity MetersPerSecondSquared := ⟨9.81⟩
  let force := computeForce mass accel

  IO.println s!"Mass: {mass.val} kg"
  IO.println s!"Acceleration: {accel.val} m/s²"
  IO.println s!"Force: {force.val} N"

  let impulse := computeImpulse force (seconds 5.0)
  IO.println s!"Impulse: {impulse.val} N·s"
