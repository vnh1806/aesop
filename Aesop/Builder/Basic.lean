/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule

open Lean
open Lean.Meta

namespace Aesop

/--
Options for the builders. Most options are only relevant for certain builders.
-/
structure RuleBuilderOptions where
  immediatePremises? : Option (Array Name)
  indexingMode? : Option IndexingMode
  casesPatterns? : Option (Array CasesPattern)
  /-- The transparency used by the rule tactic. -/
  transparency? : Option TransparencyMode
  /-- The transparency used for indexing the rule. Currently, the rule is not
  indexed unless this is `.reducible`. -/
  indexTransparency? : Option TransparencyMode
  deriving Inhabited

namespace RuleBuilderOptions

protected def default : RuleBuilderOptions :=
  ⟨none, none, none, none, none⟩

instance : EmptyCollection RuleBuilderOptions :=
  ⟨.default⟩

def getIndexingModeM [Monad m] (dflt : m IndexingMode)
    (opts : RuleBuilderOptions) : m IndexingMode :=
  match opts.indexingMode? with
  | none => dflt
  | some imode => return imode

end RuleBuilderOptions


inductive RuleBuilderKind
  | global (decl : Name)
  | «local» (fvarUserName : Name) (goal : MVarId)

def RuleBuilderKind.toRuleIdent : RuleBuilderKind → RuleIdent
  | global decl => RuleIdent.const decl
  | «local» fvarUserName .. => RuleIdent.fvar fvarUserName

structure RuleBuilderInput where
  phase : PhaseName
  kind : RuleBuilderKind
  options : RuleBuilderOptions

structure RegularRuleBuilderResult where
  builder : BuilderName
  tac : RuleTacDescr
  indexingMode : IndexingMode
  deriving Inhabited

inductive RuleBuilderResult
  | regular (r : RegularRuleBuilderResult)
  | globalSimp (entries : Array SimpEntry)
  | localSimp (userName : Name)
  | unfold (r : UnfoldRule)
  deriving Inhabited

inductive RuleBuilderOutput
  | global (r : RuleBuilderResult)
  | «local» (goal : MVarId) (r : RuleBuilderResult)

/--
Invariant: if the `RuleBuilderInput` contains a `RuleBuilderKind.local`,
then the builder returns a `RuleBuilderOutput.local`, and similar for
`RuleBuilderKind.global`.
-/
abbrev RuleBuilder := RuleBuilderInput → MetaM RuleBuilderOutput

namespace RuleBuilder

def checkConstIsInductive (builderName : BuilderName) (decl : Name) :
    MetaM InductiveVal := do
  let info ← getConstInfo decl
    <|> throwError "aesop: {builderName} builder: unknown constant '{decl}'"
  let (ConstantInfo.inductInfo info) ← pure info
    | throwError "aesop: {builderName} builder: expected '{decl}' to be an inductive type"
  return info

def ofGlobalRuleBuilder (name : BuilderName)
    (globalBuilder : PhaseName → Name → RuleBuilderOptions → MetaM RuleBuilderResult) :
    RuleBuilder := λ input =>
  match input.kind with
  | RuleBuilderKind.local .. =>
    throwError "aesop: {name} builder does not support local hypotheses"
  | RuleBuilderKind.global decl =>
    RuleBuilderOutput.global <$> globalBuilder input.phase decl input.options

end RuleBuilder
