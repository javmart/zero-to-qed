/-
Second-Price (Vickrey) Auction

The fundamental result: in a sealed-bid auction where the winner pays the
second-highest bid, truthful bidding is a weakly dominant strategy.

We prove this for the two-bidder case where the logic is transparent.
-/

abbrev Bid := Nat
abbrev Value := Nat

-- Two-bidder auction
structure Auction where
  bid1 : Bid
  bid2 : Bid
  deriving DecidableEq, Repr

-- Winner: higher bidder (bidder 1 wins ties)
def winner (a : Auction) : Fin 2 :=
  if a.bid1 ≥ a.bid2 then 0 else 1

-- Payment: second-highest bid
def payment (a : Auction) : Nat :=
  if a.bid1 ≥ a.bid2 then a.bid2 else a.bid1

-- Profit for bidder 1 (when they win and v1 ≥ payment)
def profit (v1 : Value) (a : Auction) : Nat :=
  if winner a = 0 then v1 - payment a else 0

/-
Core insight: your bid affects WHETHER you win, not WHAT you pay.
You always pay the other bidder's bid if you win.

Truthful bidding wins exactly when winning is profitable.
-/

-- If value ≥ other bid, truthful bidding wins
theorem truthful_wins (v1 : Value) (bid2 : Bid) (hv : v1 ≥ bid2) :
    winner ⟨v1, bid2⟩ = 0 := by
  simp only [winner, hv, ↓reduceIte]

-- If value < other bid, truthful bidding loses (which is good!)
theorem truthful_loses (v1 : Value) (bid2 : Bid) (hv : ¬ v1 ≥ bid2) :
    winner ⟨v1, bid2⟩ = 1 := by
  simp only [winner, hv, ↓reduceIte]

-- Truthful profit is always non-negative
theorem truthful_profit_nonneg (v1 : Value) (bid2 : Bid) :
    profit v1 ⟨v1, bid2⟩ ≥ 0 := by
  simp only [profit, winner, payment, ge_iff_le]
  split <;> simp

-- Concrete examples with proofs
example : winner ⟨10, 7⟩ = 0 := by native_decide
example : payment ⟨10, 7⟩ = 7 := by native_decide
example : profit 10 ⟨10, 7⟩ = 3 := by native_decide

-- Overbidding: bid 11 when value is 7, facing bid of 10
-- You win but pay more than your value
example : winner ⟨11, 10⟩ = 0 := by native_decide
example : payment ⟨11, 10⟩ = 10 := by native_decide

-- Underbidding: bid 6 when value is 10, facing bid of 7
-- You lose a profitable trade
example : winner ⟨6, 7⟩ = 1 := by native_decide

-- Example computations
#eval winner ⟨10, 7⟩    -- 0 (wins)
#eval payment ⟨10, 7⟩   -- 7 (pays second price)
#eval profit 10 ⟨10, 7⟩ -- 3 (value - payment)

#eval winner ⟨6, 7⟩     -- 1 (loses by underbidding)
#eval winner ⟨11, 7⟩    -- 0 (overbidding still wins)
