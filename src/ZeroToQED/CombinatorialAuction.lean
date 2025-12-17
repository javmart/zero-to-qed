/-
Combinatorial Auctions: Why Bundles Matter

When bidders have complementary preferences (items worth more together),
combinatorial auctions achieve higher welfare than separate auctions.
-/

-- Items in our simple market
inductive Item | A | B
  deriving DecidableEq, Repr

-- A bundle is a set of items
abbrev Bundle := List Item

def emptyBundle : Bundle := []
def bundleA : Bundle := [Item.A]
def bundleB : Bundle := [Item.B]
def bundleAB : Bundle := [Item.A, Item.B]

-- Substitutes: items are interchangeable, no synergy
-- v({A,B}) = v({A}) + v({B})
def isSubstitutes (v : Bundle → Nat) : Prop :=
  v bundleAB = v bundleA + v bundleB

-- Complements: items are worth more together
-- v({A,B}) > v({A}) + v({B})
def isComplements (v : Bundle → Nat) : Prop :=
  v bundleAB > v bundleA + v bundleB

-- Synergy: the extra value from combining items
def synergy (v : Bundle → Nat) : Int :=
  (v bundleAB : Int) - (v bundleA : Int) - (v bundleB : Int)

/-
The Key Example: Complements Create Efficiency Gains

Bidder 0: Values A at 5, B at 5, {A,B} at 10 (no synergy, substitutes)
Bidder 1: Values A at 1, B at 1, {A,B} at 12 (synergy of 10, complements)
-/

def bidder0Value : Bundle → Nat
  | [] => 0
  | [Item.A] => 5
  | [Item.B] => 5
  | [Item.A, Item.B] => 10
  | [Item.B, Item.A] => 10
  | _ => 0

def bidder1Value : Bundle → Nat
  | [] => 0
  | [Item.A] => 1
  | [Item.B] => 1
  | [Item.A, Item.B] => 12
  | [Item.B, Item.A] => 12
  | _ => 0

-- Verify preference types
#eval synergy bidder0Value  -- 0 (substitutes)
#eval synergy bidder1Value  -- 10 (strong complements)

-- Allocation: who gets what bundle
inductive Allocation
  | bidder0_gets_both   -- Bidder 0 gets {A, B}
  | bidder1_gets_both   -- Bidder 1 gets {A, B}
  | split               -- Bidder 0 gets A, Bidder 1 gets B
  deriving DecidableEq, Repr

-- Total welfare for each allocation
def welfare : Allocation → Nat
  | .bidder0_gets_both => bidder0Value bundleAB  -- 10
  | .bidder1_gets_both => bidder1Value bundleAB  -- 12
  | .split => bidder0Value bundleA + bidder1Value bundleB  -- 5 + 1 = 6

-- Separate Auctions: Each item sold independently
-- Bidder 0 bids 5 on A, Bidder 1 bids 1 on A → Bidder 0 wins A
-- Bidder 0 bids 5 on B, Bidder 1 bids 1 on B → Bidder 0 wins B
-- Result: Bidder 0 wins both
def separateAuctionResult : Allocation := .bidder0_gets_both

-- Combinatorial Auction: Bidders submit bundle values
-- Bidder 0's package bid: {A,B} at 10
-- Bidder 1's package bid: {A,B} at 12
-- Optimal allocation: Bidder 1 wins
def combinatorialAuctionResult : Allocation := .bidder1_gets_both

-- The welfare comparison
#eval welfare separateAuctionResult      -- 10
#eval welfare combinatorialAuctionResult -- 12

/-
Theorem: Combinatorial auctions achieve strictly higher welfare when
complementarities exist.
-/

theorem combinatorial_dominates :
    welfare combinatorialAuctionResult > welfare separateAuctionResult := by
  native_decide

theorem efficiency_gap :
    welfare combinatorialAuctionResult - welfare separateAuctionResult = 2 := by
  native_decide

-- The optimal allocation maximizes welfare
theorem combinatorial_is_optimal :
    ∀ a : Allocation, welfare combinatorialAuctionResult ≥ welfare a := by
  intro a
  cases a <;> native_decide

/-
Why Separate Auctions Fail:

In separate auctions, Bidder 1 faces the "exposure problem":
- If they bid high on A and B separately, they might win one but lose the other
- Winning just A (value 1) while paying close to 5 is a disaster
- So they bid conservatively and lose both items

The combinatorial auction lets Bidder 1 express: "I want {A,B} together at 12"
without risk of getting stuck with just one item.
-/

-- Bidder 1 has positive synergy (complements)
theorem bidder1_has_complements : isComplements bidder1Value := by
  unfold isComplements bundleAB bundleA bundleB bidder1Value
  native_decide

-- Bidder 0 has zero synergy (substitutes)
theorem bidder0_has_substitutes : isSubstitutes bidder0Value := by
  unfold isSubstitutes bundleAB bundleA bundleB bidder0Value
  native_decide

/-
General Principle:

Separate auctions are efficient when all bidders have substitute preferences.
When complementarities exist, combinatorial auctions capture the synergy.

The welfare gain from combinatorial matching = synergy of winner - synergy of
the bidder who would have won under separate auctions.

This is why expressive bidding matters for matching complex orders.
-/
