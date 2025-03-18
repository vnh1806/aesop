/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Forward.State.ApplyGoalDiff
import Aesop.RuleTac
import Aesop.RuleTac.ElabRuleTerm
import Aesop.Script.SpecificTactics
import Aesop.Search.Expansion.Basic
import Aesop.Search.Expansion.Simp
import Aesop.Search.RuleSelection
import Aesop.Search.SearchM
import Aesop.Tree.State
import Batteries.Lean.HashSet

open Lean Lean.Meta Aesop.Script

namespace Aesop

namespace NormM

structure Context where
  options : Options'
  ruleSet : LocalRuleSet
  normSimpContext : NormSimpContext
  statsRef : StatsRef

structure State where
  forwardState : ForwardState
  forwardRuleMatches : ForwardRuleMatches
  deriving Inhabited

end NormM

abbrev NormM := ReaderT NormM.Context $ StateRefT NormM.State BaseM

def getForwardState : NormM ForwardState :=
  return (← getThe NormM.State).forwardState

def getResetForwardState : NormM ForwardState := do
  modifyGetThe NormM.State λ s => (s.forwardState, { s with forwardState := ∅ })

def updateForwardState (fs : ForwardState) (newMatches : Array ForwardRuleMatch)
    (erasedHyps : Std.HashSet FVarId) : NormM Unit :=
  modifyThe NormM.State λ s => { s with
    forwardState := fs
    forwardRuleMatches :=
      s.forwardRuleMatches.update newMatches erasedHyps
        (consumedForwardRuleMatch? := none) -- We erase the consumed matches separately.
  }

def eraseForwardRuleMatch (m : ForwardRuleMatch) : NormM Unit := do
  modifyThe NormM.State λ s => { s with forwardRuleMatches := s.forwardRuleMatches.erase m }

def applyDiffToForwardState (diff : GoalDiff) : NormM Unit := do
  let fs ← getResetForwardState
  let (fs, ms) ← fs.applyGoalDiff (← read).ruleSet diff
  updateForwardState fs ms diff.removedFVars

inductive NormRuleResult
  | succeeded (goal : MVarId) (steps? : Option (Array Script.LazyStep))
  | proved (steps? : Option (Array Script.LazyStep))

namespace NormRuleResult

def newGoal? : NormRuleResult → Option MVarId
  | succeeded goal .. => goal
  | proved .. => none

def steps? : NormRuleResult → Option (Array Script.LazyStep)
  | .succeeded (steps? := steps?) .. | .proved (steps? := steps?) .. => steps?

end NormRuleResult

def optNormRuleResultEmoji : Option NormRuleResult → String
  | some (.succeeded ..) => ruleSuccessEmoji
  | some (.proved ..) => ruleProvedEmoji
  | none => ruleFailureEmoji

@[inline, always_inline]
def withNormTraceNode (ruleName : DisplayRuleName)
    (k : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) :=
  withAesopTraceNode .steps fmt do
    let result? ← k
    if let some newGoal := result?.bind (·.newGoal?) then
      aesop_trace[steps] newGoal
    return result?
  where
    fmt (r : Except Exception (Option NormRuleResult)) : NormM MessageData := do
      let emoji := exceptRuleResultToEmoji (optNormRuleResultEmoji ·) r
      return m!"{emoji} {ruleName}"

/-- On success, returns the rule tactic's result, the new forward state and the
new forward rule matches. If `rule` corresponds to a forward rule match,
returns that match as well. -/
def runNormRuleTac (rule : NormRule) (input : RuleTacInput) (fs : ForwardState)
    (rs : LocalRuleSet) :
    NormM $
      Option (NormRuleResult × ForwardState × Array ForwardRuleMatch × Std.HashSet FVarId) ×
      Option ForwardRuleMatch := do
  let preMetaState ← show MetaM _ from saveState
  let result? ← runRuleTac rule.tac.run rule.name preMetaState input
  let forwardRuleMatch? := rule.tac.forwardRuleMatch?
  match result? with
  | Sum.inl e =>
    aesop_trace[steps] e.toMessageData
    return (none, forwardRuleMatch?)
  | Sum.inr result =>
    let #[rapp] := result.applications
      | err m!"rule did not produce exactly one rule application."
    show MetaM _ from restoreState rapp.postState
    if rapp.goals.isEmpty then
      return (some (.proved rapp.scriptSteps?, fs, #[], ∅), forwardRuleMatch?)
    let (#[{ diff }]) := rapp.goals
      | err m!"rule produced more than one subgoal."
    let (fs, ms) ← fs.applyGoalDiff rs diff
    let g := diff.newGoal
    if ← Check.rules.isEnabled then
      let mvars := .ofArray input.mvars.toArray
      let actualMVars ← rapp.postState.runMetaM' g.getMVarDependencies
      if ! actualMVars == mvars then
         err "the goal produced by the rule depends on different metavariables than the original goal."
    let result := .succeeded g rapp.scriptSteps?
    return (some (result, fs, ms, diff.removedFVars), forwardRuleMatch?)
  where
    err {α} (msg : MessageData) : MetaM α := throwError
      "aesop: error while running norm rule {rule.name}: {msg}\nThe rule was run on this goal:{indentD $ MessageData.ofGoal input.goal}"

def runNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rule : IndexMatchResult NormRule) : NormM (Option NormRuleResult) := do
  profilingRule (.ruleName rule.rule.name) (λ result => result.isSome) do
    let ruleInput := {
      indexMatchLocations := rule.locations
      patternSubsts? := rule.patternSubsts?
      options := (← read).options
      hypTypes := (← get).forwardState.hypTypes
      goal, mvars
    }
    withNormTraceNode (.ruleName rule.rule.name) do
      let fs ← getForwardState
      let (result?, consumedForwardRuleMatch?) ←
        runNormRuleTac rule.rule ruleInput fs (← read).ruleSet
      if let some m := consumedForwardRuleMatch? then
        eraseForwardRuleMatch m
      let (some (result, fs, ms, removedFVars)) := result?
        | return none
      updateForwardState fs ms removedFVars
      return result

def runFirstNormRule (goal : MVarId) (mvars : UnorderedArraySet MVarId)
    (rules : Array (IndexMatchResult NormRule)) :
    NormM (Option (DisplayRuleName × NormRuleResult)) := do
  for rule in rules do
    let result? ← runNormRule goal mvars rule
    if let some result := result? then
      return some (rule.rule.name, result)
  return none

def mkNormSimpScriptStep
    (preGoal : MVarId) (postGoal? : Option MVarId)
    (preState postState : Meta.SavedState) (usedTheorems : Simp.UsedSimps) :
    NormM Script.LazyStep := do
  let ctx := (← read).normSimpContext
  let simpBuilder :=
    TacticBuilder.simpAllOrSimpAtStar (simpAll := ctx.useHyps) preGoal
      ctx.configStx? usedTheorems
  let simpOnlyBuilder :=
    TacticBuilder.simpAllOrSimpAtStarOnly (simpAll := ctx.useHyps) preGoal
      ctx.configStx? usedTheorems
  let tacticBuilders :=
    if (← read).options.useDefaultSimpSet then
      #[simpOnlyBuilder, simpBuilder]
    else
      #[simpOnlyBuilder]
  return {
    postGoals := postGoal?.toArray
    tacticBuilders
    tacticBuilders_ne := by simp only [tacticBuilders]; split <;> simp
    preGoal, preState, postState
  }

def normSimpCore (goal : MVarId) (goalMVars : Std.HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  let ctx := (← read).normSimpContext
  goal.withContext do
    let preState ← show MetaM _ from saveState
    let localRules := (← read).ruleSet.localNormSimpRules
    let result ←
      if ctx.useHyps then
        let (ctx, simprocs) ←
          addLocalRules localRules ctx.toContext ctx.simprocs
            (isSimpAll := true)
        Aesop.simpAll goal ctx simprocs
      else
        let (ctx, simprocs) ←
          addLocalRules localRules ctx.toContext ctx.simprocs
            (isSimpAll := false)
        Aesop.simpGoalWithAllHypotheses goal ctx simprocs

    -- It can happen that simp 'solves' the goal but leaves some mvars
    -- unassigned. In this case, we treat the goal as unchanged.
    let result ←
      match result with
      | .solved .. =>
        let anyMVarDropped ← goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)
        if anyMVarDropped then
          aesop_trace[steps] "Normalisation simp solved the goal but dropped some metavariables. Skipping normalisation simp."
          show MetaM _ from restoreState preState
          pure .unchanged
        else
          pure result
      | .unchanged .. =>
        aesop_trace[steps] "norm simp left the goal unchanged"
        pure result
      | .simplified .. =>
        pure result

    let postState ← show MetaM _ from saveState
    match result with
    | .unchanged => return none
    | .solved usedTheorems => do
      let step ←
        mkNormSimpScriptStep goal none preState postState usedTheorems
      return some $ .proved #[step]
    | .simplified newGoal usedTheorems => do
      let step ←
        mkNormSimpScriptStep goal newGoal preState postState usedTheorems
      applyDiffToForwardState (← diffGoals goal newGoal)
      return some $ .succeeded newGoal #[step]
where
  addLocalRules (localRules : Array LocalNormSimpRule) (ctx : Simp.Context)
      (simprocs : Simp.SimprocsArray) (isSimpAll : Bool) :
      NormM (Simp.Context × Simp.SimprocsArray) :=
    localRules.foldlM (init := (ctx, simprocs)) λ (ctx, simprocs) r =>
      try
        elabRuleTermForSimpMetaM goal r.simpTheorem ctx simprocs isSimpAll
      catch _ =>
        return (ctx, simprocs)

@[inline, always_inline]
def checkSimp (name : String) (mayCloseGoal : Bool) (goal : MVarId)
    (x : NormM (Option NormRuleResult)) : NormM (Option NormRuleResult) := do
  if ! (← Check.rules.isEnabled) then
    x
  else
    let preMetaState ← show MetaM _ from saveState
    let result? ← x
    let newGoal? := result?.bind (·.newGoal?)
    let postMetaState ← show MetaM _ from saveState
    let introduced :=
        (← getIntroducedExprMVars preMetaState postMetaState).filter
        (some · != newGoal?)
    unless introduced.isEmpty do throwError
        "{Check.rules.name}: {name} introduced mvars:{introduced.map (·.name)}"
    let assigned :=
        (← getAssignedExprMVars preMetaState postMetaState).filter (· != goal)
    unless assigned.isEmpty do throwError
        "{Check.rules.name}: {name} assigned mvars:{introduced.map (·.name)}"
    if ← pure (! mayCloseGoal && newGoal?.isNone) <&&> goal.isAssigned then
        throwError "{Check.rules.name}: {name} solved the goal"
    return result?

def normSimp (goal : MVarId) (goalMVars : Std.HashSet MVarId) :
    NormM (Option NormRuleResult) := do
  profilingRule .normSimp (wasSuccessful := λ _ => true) do
    checkSimp "norm simp" (mayCloseGoal := true) goal do
      try
        withNormTraceNode .normSimp do
          withMaxHeartbeats (← read).options.maxSimpHeartbeats do
            normSimpCore goal goalMVars
      catch e =>
        throwError "aesop: error in norm simp: {e.toMessageData}"

def normUnfoldCore (goal : MVarId) : NormM (Option NormRuleResult) := do
  let unfoldRules := (← read).ruleSet.unfoldRules
  let (result, steps) ← unfoldManyStarS goal (unfoldRules.find? ·) |>.run
  match result with
  | none =>
    aesop_trace[steps] "nothing to unfold"
    return none
  | some newGoal =>
    applyDiffToForwardState (← diffGoals goal newGoal)
    return some $ .succeeded newGoal steps

def normUnfold (goal : MVarId) : NormM (Option NormRuleResult) := do
  profilingRule .normUnfold (wasSuccessful := λ _ => true) do
    checkSimp "unfold simp" (mayCloseGoal := false) goal do
      try
        withNormTraceNode .normUnfold do
          withMaxHeartbeats (← read).options.maxUnfoldHeartbeats do
            normUnfoldCore goal
      catch e =>
        throwError "aesop: error in norm unfold: {e.toMessageData}"

inductive NormSeqResult where
  | proved (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | changed (goal : MVarId)
      (script : Array (DisplayRuleName × Option (Array Script.LazyStep)))
  | unchanged

def NormRuleResult.toNormSeqResult (ruleName : DisplayRuleName) :
    NormRuleResult → NormSeqResult
  | .proved steps? => .proved #[(ruleName, steps?)]
  | .succeeded goal steps? => .changed goal #[(ruleName, steps?)]

def optNormRuleResultToNormSeqResult :
    Option (DisplayRuleName × NormRuleResult) → NormSeqResult
  | some (ruleName, r) => r.toNormSeqResult ruleName
  | none => .unchanged

abbrev NormStep :=
  MVarId → Array (IndexMatchResult NormRule) →
  Array (IndexMatchResult NormRule) → NormM NormSeqResult

def runNormSteps (goal : MVarId) (steps : Array NormStep)
    (stepsNe : 0 < steps.size) : NormM NormSeqResult := do
  let ctx ← readThe NormM.Context
  let maxIterations := ctx.options.maxNormIterations
  let mut iteration := 0
  let mut step : Fin steps.size := ⟨0, stepsNe⟩
  let mut goal := goal
  let mut scriptSteps := #[]
  let mut preSimpRules := ∅
  let mut postSimpRules := ∅
  let mut anySuccess := false
  while iteration < maxIterations do
    if step.val == 0 then
      let rules ←
        selectNormRules ctx.ruleSet (← getThe NormM.State).forwardRuleMatches
          goal
      let (preSimpRules', postSimpRules') :=
        rules.partition λ r => r.rule.extra.penalty < (0 : Int)
      preSimpRules := preSimpRules'
      postSimpRules := postSimpRules'
    match ← steps[step] goal preSimpRules postSimpRules with
    | .changed newGoal scriptSteps' =>
      anySuccess := true
      goal := newGoal
      scriptSteps := scriptSteps ++ scriptSteps'
      iteration := iteration + 1
      step := ⟨0, stepsNe⟩
    | .proved scriptSteps' =>
      scriptSteps := scriptSteps ++ scriptSteps'
      return .proved scriptSteps
    | .unchanged =>
      if h : step.val + 1 < steps.size then
        step := ⟨step.val + 1, h⟩
      else
        if anySuccess then
          return .changed goal scriptSteps
        else
          return .unchanged
  throwError "aesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."

namespace NormStep

def runPreSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, preSimpRules, _ => do
    optNormRuleResultToNormSeqResult <$>
      runFirstNormRule goal mvars preSimpRules

def runPostSimpRules (mvars : UnorderedArraySet MVarId) : NormStep
  | goal, _, postSimpRules =>
    optNormRuleResultToNormSeqResult <$>
      runFirstNormRule goal mvars postSimpRules

def unfold : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).options.enableUnfold then
      aesop_trace[steps] "norm unfold is disabled (options := \{ ..., enableUnfold := false })"
      return .unchanged
    let r := (← normUnfold goal).map (.normUnfold, ·)
    return optNormRuleResultToNormSeqResult r

def simp (mvars : Std.HashSet MVarId) : NormStep
  | goal, _, _ => do
    if ! (← readThe NormM.Context).normSimpContext.enabled then
      aesop_trace[steps] "norm simp is disabled (simp_options := \{ ..., enabled := false })"
      return .unchanged
    let r := (← normSimp goal mvars).map (.normSimp, ·)
    return optNormRuleResultToNormSeqResult r
--NVU


/-def _root_.Aesop.reduceAllInGoal (goal : MVarId)
  (skipProofs skipTypes skipImplicitArguments rpinf: Bool) : BaseM MVarId := do
  goal.withContext do
    withReducible do
      let type ← goal.getType
      let newType ←
        if rpinf then
          let r <- Aesop.rpinf type
          pure r.toExpr
        else
          reduce type skipImplicitArguments skipTypes skipProofs

      let mut changed := false -- Track if the goal or its context changes
      let mut newLCtx : LocalContext := {}

      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then
          -- Directly add implementation details without modification
          newLCtx := newLCtx.addDecl ldecl
        else
          -- Skip reducing types if the option is enabled
          let type := ldecl.type
          let newType ←
            if rpinf then
              let r <- Aesop.rpinf type
              pure r.toExpr
            else
              reduce type skipImplicitArguments skipTypes skipProofs
          let mut newLDecl := ldecl.setType newType

          -- Check if the type has changed
          if newType != type then
            changed := true

          -- Reduce the value if it exists and skip proofs if needed
          if let some val := ldecl.value? then
            let newVal ←
              if rpinf then
                let r <- Aesop.rpinf val
                pure r.toExpr
              else
                reduce val skipImplicitArguments skipTypes skipProofs
            if newVal != val then
              changed := true
            newLDecl := newLDecl.setValue newVal

          -- Add the (potentially updated) declaration to the new local context
          newLCtx := newLCtx.addDecl newLDecl

      -- If nothing has changed, return the original goal without creating a new one
      if not changed && newType == type then
        return goal

      -- Otherwise, create a new goal with the updated context and type
      let newGoal ← mkFreshExprMVarAt newLCtx (← getLocalInstances) newType
      goal.assign newGoal
      return newGoal.mvarId!-/
def processExpr (e : Expr)
  (skipImplicitArguments skipTypes skipProofs rpinf : Bool)
  (seen : Std.HashSet Expr) : BaseM (Expr × Std.HashSet Expr) := do
  let iterationLimit := 10 -- set the iterations limit
  let mut current := e
  let mut i := 0
  let mut localSeen := seen

  -- If this expression has been seen before, return immediately to avoid infinite loops
  if seen.contains e then return (e, seen)

  localSeen := localSeen.insert e -- Add the initial expression to the seen set

  while i < iterationLimit do
    let newExpr ←
      if rpinf then
        let r ← Aesop.rpinf current
        pure r.toExpr
      else
        reduce current skipImplicitArguments skipTypes skipProofs

    -- Check if the expression has changed
    if newExpr == current ∨ localSeen.contains newExpr then
      break -- If there is no change or it has been seen before, stop the loop

    current := newExpr
    localSeen := localSeen.insert newExpr
    i := i + 1

  return (current, localSeen)


def _root_.Aesop.reduceAllInGoal (goal : MVarId)
  (skipProofs skipTypes skipImplicitArguments rpinf: Bool) : BaseM MVarId := do
  goal.withContext do
    withReducible do
      let globalIterationLimit := 50 -- Global iteration limit
      let mut iterationCount := 0
      let seenExprs : Std.HashSet Expr := {} -- Use an immutable variable, updated manually
      let (newType, seenExprs') ← processExpr (← goal.getType) skipImplicitArguments skipTypes skipProofs rpinf seenExprs
      let mut changed := false
      let mut newLCtx : LocalContext := {}

      for ldecl in ← getLCtx do
        if iterationCount > globalIterationLimit then
          throwError "Aesop: Maximum normalisation iterations reached globally."

        if ldecl.isImplementationDetail then
          newLCtx := newLCtx.addDecl ldecl
        else
          let (newType, seenExprs'') ← processExpr ldecl.type skipImplicitArguments skipTypes skipProofs rpinf seenExprs'
          let mut newLDecl := ldecl.setType newType
          if newType != ldecl.type then changed := true

          if let some val := ldecl.value? then
            let (newVal, seenExprs''') ← processExpr val skipImplicitArguments skipTypes skipProofs rpinf seenExprs''
            if newVal != val then changed := true
            newLDecl := newLDecl.setValue newVal

          newLCtx := newLCtx.addDecl newLDecl
          iterationCount := iterationCount + 1

      if not changed && newType == (← goal.getType) then
        return goal

      let newGoal ← mkFreshExprMVarAt newLCtx (← getLocalInstances) newType
      goal.assign newGoal
      return newGoal.mvarId!




def reduceAllInGoal : NormStep
  | goal, _, _ => do
      let rpinf := true
      let skipProofs := false
      let skipTypes := false
      let skipImplicitArguments := false
      let (newGoal, time) ← time (Aesop.reduceAllInGoal goal skipProofs skipTypes skipImplicitArguments rpinf)
      trace[debug] "Execution time for `reduceAllInGoal`: {time.printAsMillis}"
      modifyCurrentStats λ stats => {stats with reduceAllInGoal := stats.reduceAllInGoal + time}
      if newGoal == goal then
        return .unchanged
      else
        return .changed newGoal #[]

end NormStep

  /-def NormStep.reduceAllInGoal : NormStep
  | goal, _, _ => do
      let (newGoal, time) ← time (Aesop.reduceAllInGoal goal false false false)
      trace[debug] "Execution time for reduceAllInGoal: {time.printAsMillis}"
      modifyCurrentStats λ stats => {stats with reduceAllInGoal := stats.reduceAllInGoal + time}
      if newGoal == goal then
        return .unchanged
      else
        return .changed newGoal #[]

upstream/rpinf-precomp in case
import precomp rpinf
--
-/

--NVU
partial def normalizeGoalMVar (goal : MVarId)
    (mvars : UnorderedArraySet MVarId) : NormM NormSeqResult := do
  let mvarsHashSet := .ofArray mvars.toArray
  let mut normSteps := #[
    NormStep.reduceAllInGoal,
    NormStep.runPreSimpRules mvars,
    NormStep.unfold,
    NormStep.simp mvarsHashSet,
    NormStep.runPostSimpRules mvars --NVU
  ]
  runNormSteps goal normSteps
    (by simp (config := { decide := true }) [normSteps])

-- Returns true if the goal was solved by normalisation.
def normalizeGoalIfNecessary (gref : GoalRef) [Aesop.Queue Q] :
    SearchM Q Bool := do
  let g ← gref.get
  let preGoal := g.preNormGoal
  if ← g.isRoot then
    -- For the root goal, we skip normalization.
    let rootState ← getRootMetaState
    gref.modify (·.setNormalizationState (.normal preGoal rootState #[]))
    return false
  match g.normalizationState with
  | .provenByNormalization .. => return true
  | .normal .. => return false
  | .notNormal => pure ()
  let normCtx := { (← read) with }
  let normState := {
    forwardState := g.forwardState
    forwardRuleMatches := g.forwardRuleMatches
  }
  let ((normResult, { forwardState, forwardRuleMatches }), postState) ←
    g.runMetaMInParentState do
      normalizeGoalMVar preGoal g.mvars |>.run normCtx |>.run normState
  match normResult with
  | .changed postGoal script? =>
    gref.modify λ g =>
      g.setNormalizationState (.normal postGoal postState script?)
        |>.setForwardState forwardState
        |>.setForwardRuleMatches forwardRuleMatches
    return false
  | .unchanged =>
    gref.modify (·.setNormalizationState (.normal preGoal postState #[]))
    return false
  | .proved script? =>
    gref.modify
      (·.setNormalizationState (.provenByNormalization postState script?))
    gref.markProvenByNormalization
    return true

end Aesop
