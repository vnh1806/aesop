/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Data.Options

open Lean

namespace Aesop

-- TODO The following setup is unnecessarily complicated. We should just define
-- a new `Aesop.CheckOption` type with a custom `isEnabled` function.

def registerCheckOption (checkName : Name) (defValue : Bool)
    (descr : String) : IO (Lean.Option Bool) :=
  Option.register (`aesop.check ++ checkName)
    { defValue := defValue, group := "aesop", descr := descr }

initialize checkAllOption : Lean.Option Bool ←
  registerCheckOption `all false
    "(aesop) Enable all runtime checks. Individual checks can still be disabled."

initialize checkProofReconstructionOption : Lean.Option Bool ←
  registerCheckOption `proofReconstruction false
    "(aesop) Typecheck partial proof terms during proof reconstruction."

initialize checkTreeOption : Lean.Option Bool ←
  registerCheckOption `tree false
    "(aesop) Check search tree invariants after every iteration of the search loop. Very expensive."

initialize checkUnificationGoalAssignmentsOption : Lean.Option Bool ←
  registerCheckOption `unificationGoalAssignments false
    "(aesop) Typecheck assignments to unification goal metavariables."

initialize checkRulesOption : Lean.Option Bool ←
  registerCheckOption `rules false
    "(aesop) Check that information reported by rules is correct."

initialize checkScriptOption : Lean.Option Bool ←
  registerCheckOption `script false
    "(aesop) Check that the tactic script generated by Aesop proves the goal. When this check is active, Aesop generates a tactic script even if the user did not request one."

initialize checkScriptStepsOption : Lean.Option Bool ←
  registerCheckOption `script.steps false
    "(aesop) Check each step of the tactic script generated by Aesop."

inductive Check
  | all
  | tree
  | proofReconstruction
  | unificationGoalAssignments
  | rules
  | script
  | scriptSteps

namespace Check

@[inline_if_reduce]
def toOption : Check → Lean.Option Bool
  | all => checkAllOption
  | tree => checkTreeOption
  | proofReconstruction => checkProofReconstructionOption
  | unificationGoalAssignments => checkUnificationGoalAssignmentsOption
  | rules => checkRulesOption
  | script => checkScriptOption
  | scriptSteps => checkScriptStepsOption

def isEnabled [Monad m] [MonadOptions m] : Check → m Bool
  | all => return all.toOption.get (← getOptions)
  | c => do
    let opts ← getOptions
    match c.toOption.get? opts with
    | none => return all.toOption.get opts
    | some v => return v

def name (c : Check) : Name := c.toOption.name

end Check

end Aesop
