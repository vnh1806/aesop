import Aesop.Search.Expansion.Norm
import Lean.Meta
open Lean Meta

/-
def setupGoal : IO MVarId := do
  let goalType := mkConst`Nat
  let goalExpr ← mkFreshExprMVar goalType
  return goalExpr.mvarId

def testReduceAllInGoal : MetaM Bool := do
  let goal ← setupGoal
  let originalType ← goal.getType
  let reducedGoal ← reduceAllInGoal goal
  let newType ← reducedGoal.getType
  return originalType ≠ newType

def runTest : IO Unit := do
  let env ← MetaM.run testReduceAllInGoal
  if env then
    IO.println "Test passed: Goal was reduced."
  else
    IO.println "Test failed: Goal was not reduced."
-/

abbrev Foo := Nat

run_meta show MetaM Unit from do
 sorry
example : Foo := by
  run_tac do
    let e <- Elab.Tactic.getMainTarget
    let e' <- reduceAll e
    logInfo e'


def test1 (a b : Nat) : Bool :=
  a >= b && (a + 2 >= b + 2)
run_meta show MetaM Unit from do

example : test1 := by
  run_tac do
    let e <- Elab.Tactic.getMainTarget
    let e' <- reduceAll e
    logInfo e'
