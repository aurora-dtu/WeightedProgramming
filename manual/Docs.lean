import VersoManual
import WeightedProgramming

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.exampleModule "Wnetkat.Wspp.Defs"

set_option verso.docstring.allowMissing true

open scoped Computability

structure PaperConfig : Type where
  full : Option Lean.Name

section
open Lean Verso ArgParse Scopes Elab

variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT TermElabM m]

def PaperConfig.parse : ArgParse m PaperConfig :=
  PaperConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref)
where
  ref : ValDesc m (Option Name) := {
    description := "reference name"
    signature := .Ident
    get := fun
      | .name x =>
        try
          let resolved ← liftM (runWithOpenDecls (runWithVariables fun _ => realizeGlobalConstNoOverloadWithInfo x))
          return some resolved
        catch
          | .error ref e => throwErrorAt ref e
          | _ => return none
      | other => throwError "Expected reference name, got {repr other}"
  }

instance : FromArgs PaperConfig m := ⟨PaperConfig.parse⟩
end

section

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets ExpectString
open Lean Elab

open SubVerso.Highlighting

open Verso.SyntaxUtils (runParserCategory' SyntaxError parseStrLitAsCategory strLitInputContext)

open Lean.Doc.Syntax
open Lean.Elab.Tactic.GuardMsgs

open Qq
open Verso.Doc.Elab

@[role]
def paper : RoleExpanderOf PaperConfig
  | cfg, #[arg] => do
    let `(inline|code( $name:str )) := arg
    | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)
    let e ← Lean.Elab.Term.elabTermAndSynthesize identStx none
    let e ← instantiateMVars e
    let e ← Meta.mkAppM ``Lean.toExpr #[e]
    let e ← unsafe Lean.Meta.evalExpr Expr q(Expr) e (safety := .unsafe)

    ``(Inline.bold #[Inline.text $(quote (e.dbgToString.drop 1 |>.dropEnd 1).toString)])
  | _, _ => `(Inline)

end

namespace Labels

def Def (n : String) := s!"Definition {n}"
/-- This is mostly to ensure that we haven't missed any numbers -/
def Exm (n : String) := s!"Example {n}"
def Thm (n : String) := s!"Theorem {n}"
def Lem (n : String) := s!"Lemma {n}"
def Cor (n : String) := s!"Corollary {n}"

open Verso.Genre
open Verso.Doc.Concrete

/-! ## Section 3 -/

def def'monoid := Def "3.1"
def exm'3_2 := Exm "3.2"
def def'module := Def "3.4"
def exm'3_4 := Exm "3.4"
def exm'3_5 := Exm "3.5"
def def'naturally_ordered_module := Def "3.6"
def exm'3_7 := Exm "3.7"
def def'cont_module := Def "3.8"
def lem'countable_sums := Lem "3.8"

/-! ## Section 4 -/

def def'weighted_reward_module := Def "4.1"
def exm'4_2 := Exm "4.2"
def def'wGCL := Def "4.3"
def exm'4_4 := Exm "4.4"
def exm'4_5 := Exm "4.5"
def def'scoring := Def "4.6"
def lem'wp_mono := Lem "4.8"
def thm'knaster_tarski := Thm "4.9"
def cor'knaster_tarski_park := Cor "4.10"

/-! ## Section 5 -/

def def'wdp := Def "5.1"
def exm'mpd_is_wdp := Exm "5.2"

end Labels

open Labels

open OmegaCompletePartialOrder

#doc (Manual) "Weighted Programming with Unbounded Demonic Nondeterminism in Lean (Lean documentation)" =>
%%%
authors := []
shortTitle := "Weighted Programming with Unbounded Demonic Nondeterminism in Lean"
%%%

{index}[example]

This is the accompanying Lean manual to the paper _Weighted Programming with Unbounded Demonic Nondeterminism in Lean_ submitted to POPL'27. The manual is built using [Verso](https://verso.lean-lang.org/), which enabled hoverable code excerpts.

# Introduction

_No definitions in this section._

# Related Work

_No definitions in this section._

# Preliminaries

:::leanSection

Much of the foundational structures and theories we use, we can inherit from [mathlib](https://mathlib.org/), which we attempt to do as much as possible. However, some of these are _slightly_ different from the requirements we have, which we will make clear as necessary.

{paper}`def'monoid`, which introduces _monoids_, are present in mathlib under {name}`Monoid` (where the operator is `*` and unit is `1`) and {name}`AddMonoid` (where the operator is `+` and unit is `0`). They each have commutative variants {name}`CommMonoid` and {name}`AddCommMonoid`, of which we will use the latter more often.

{paper}`def'module` introduces _modules_, which in mathlib terms is a {name}`MonoidWithZero` with a {name}`AddCommMonoid`.

```lean
variable {𝒲 ℛ : Type} [MonoidWithZero 𝒲] [AddCommMonoid ℛ]
```

The scalar multiplication joining the two are given by {name}`SMul` and it's associative, distributive, annihalation and neutrality properties are given by {name}`DistribMulAction`.

> The below definition is extracted from the lean source code. Click the checkbox next to {lean}`MulAction` under *Extends* to see the full definition.

{docstring DistribMulAction}

Note that we are _not_ using {name}`Module` from mathlib, as that would require {lean}`𝒲` to be a {lean}`Semiring`, which we do not require, while {name}`DistribMulAction` has exactly the properties we want.

We consider only structures {lean}`ℛ` with orders being {name}`CompleteLattice`'s, which provide {name}`sSup` and {name}`sInf` as supremum and infimum over sets. {paper}`def'naturally_ordered_module` defines _naturally ordered_ captured by {name}`CanonicallyOrderedAdd`.

```lean
variable [CompleteLattice ℛ] [CanonicallyOrderedAdd ℛ]
```

{paper}`def'cont_module` defines ω-continuity which we formalize as two type classes {name}`ωScottContinuousAdd` and {name}`ωScottContinuousSMul`. These build on the notion of {name}`ωScottContinuous` from the {name}`OmegaCompletePartialOrder` module (a weaker order than {name}`CompleteLattice` and this we have an instance {inst}`OmegaCompletePartialOrder ℛ`). This bears a connection to continuity in the Scott topology {name}`Topology.scott`, but the only property we rely on is preservation of {name}`ωSup`, the chain/countable analouge of {name}`iSup`.

{paper}`lem'countable_sums` introduces _countable sums_. There is not, at the time of writing, a direct correspondence to this notion of a countable sum defined for {name}`CompleteLattice`'s with {name}`AddCommMonoid` and {name}`CanonicallyOrderedAdd`. The closest is {name}`tsum`, short for topological sum and defined as a topological limit. However, since we do not impose a topological space on our structure, we use an alternative definition based on {name}`ωSup` namely {name}`ωSum`, heavily inspired by Weighted NetKAT's definition under the same name.

{docstring ωSum}

:::

# Weighted Programming

In this section we introduce {name}`wGCL`, its syntax and its semantics.

{paper}`def'weighted_reward_module` defines a _weighted-reward module_ which we replicate as a collection of type classes.

```lean -show
open WDP
```

```lean
variable {𝒲 ℛ : Type}
  [MonoidWithZero 𝒲] [AddCommMonoid ℛ]
  [DistribMulActionWithZero 𝒲 ℛ]
  -- Order requirements
  [CompleteLattice ℛ] [CanonicallyOrderedAdd ℛ]
  -- Monotonicity of operators
  [AddLeftMono ℛ] [SMulMonoRight 𝒲 ℛ]
  -- Continuity of operators
  [SMulContinuous 𝒲 ℛ] [ωScottContinuousSMul 𝒲 ℛ]
  [AddBicontinuous ℛ] [ωScottContinuousAdd ℛ]
```

Generally we attempt the use the minimal set of requirements per theorem and pick as choose as needed, but for the purpose of this demonstration the above cover most of the requirements for all theorems.

## Program States and Expressions

:::leanSection

```lean -show
variable {D : Type} {Γ : D → Type} {σ : Σ[Γ]} {d : D}
```

We assume a set (a {lean}`Type`) of variables {lean}`(D : Type)` and a typing context {lean}`(Γ : D → Type)` that assign types to all members of {lean}`D`. This is a slight deviation from the paper, which has all variables as {name}`Nat`'s, but for the purpose of the mechanization it was trivial to parameterize the type of the variables; the only requirement is adding a {name}`Countable` constraint in certain places, otherwise the theory remains exactly the same.

We introduce _memories_ over these variables as dependent maps where we write {lean}`(σ : Σ[Γ])` as a shorthand of {lean}`(σ : ((d : D) → Γ d))` saying that {lean}`σ` takes elements {lean}`d` from {lean}`D` and returns a value of type {lean}`Γ d`.

:::

```lean
variable {D : Type} {Γ : D → Type} {σ : Σ[Γ]}
-- Example variable and value
variable {d : D} {v : Γ d}
-- For the purpose of updating memories
variable [DecidableEq D]
```

We introduce notation for _substitution_ through the type class {name}`Substitution`, allowing us to write {lean}`σ[d ↦ v]`, setting the value of {lean}`d` to {lean}`v`.

We _do not_ impose a deep embedding on the expressions of {name}`wGCL`, instead we model these as functions from {lean}`Σ[Γ]` to specific types. Since we have a typing context, these are often dependent on the context, however, some general expressions are:

- Boolean expression: {lean}`Σ[Γ] → Bool`
- Reward expression: {lean}`Σ[Γ] → ℛ`
- Weight expression: {lean}`Σ[Γ] → 𝒲`
- General expression over a variable {lean}`d`: {lean}`Σ[Γ] → Γ d`

For distributions we introduce the type {name}`wGCL.Dist` parametrized over a type.

{docstring wGCL.Dist}

{name}`Substitution` also applies to expressions with the same notation.

## Program Syntax

{paper}`def'wGCL` introduces the syntax of {name}`wGCL`, shown in the definition bewlow.

{docstring wGCL}

> In the formalization we've encoded `if b then C₁ else C₂` by way of the weighted choice with Iverson brackets $`C₁ {}_{[b]}⊕_{[¬b]} C₂`. This is semantically equivalent to the paper definition of `if b then C₁ else C₂`, but eases the proof burden a little bit.

## Weakest Precondition Semantics

```lean -show
open wGCL
```

We define the denotational semantics of {name}`wGCL` in terms of a _backward-moving weakest
prescoring transformer_ {name}`wp`. The transformer is defined as an {name}`OrderHom`, described as a _"Bundled monotone (aka, increasing) function"_, i.e. the proof of monotonicity is shown at time of definition thus showing {paper}`lem'wp_mono`.

{docstring wGCL.wp}

Scorings, as per {paper}`def'scoring` are not defined explicitly, but rather as functions point-wise lifting the properties of their codomain.

{paper}`thm'knaster_tarski` and {paper}`cor'knaster_tarski_park` are covered by mathlibs {name}`OrderHom.lfp` and associated theorems, {name}`OrderHom.lfp_le` (the underpinning of {paper}`cor'knaster_tarski_park`) and {name}`OrderHom.le_lfp` are both used extensively the proofs of following theorems.

# Operational Semantics via Weighted Decision Processes

In this section we introduce an operation semantics for {name}`wGCL` by way of a _weighted decision process_ ({name}`WDP`).

{docstring WDP}

For the purpose of proofs, it turned out to be easier _not_ to bundle the reward function `ρ` with the {name}`WDP`.

```lean
variable {S A : Type} {M : WDP 𝒲 S A}
```
## The Operational Weighted Decision Process

definition 5.3

{name}`Conf`

{name}`Conf.τ`

{name}`ρ` and {name}`ρ'`

## Minimal Weighted Rewards

definition 5.5 {name}`Sched` {name}`MSched`

definition 5.6 {name}`WDP.Path`
definition 5.7 {name}`WDP.Path.Weight`

definition 5.8 {name}`WRew` {name}`WRew'` {name}`MinWRew`

definition 5.9 {name}`op`

definition 5.11 sound iff wp = op {name}`wp_eq_op`

## Recursive Characterization of Minimal Weighted Rewards

definition 5.12 {name}`T` {name}`T'`

{name}`lp` as a short hand for `lfp T`

theorem 5.13 {name}`wp_eq_lp`

# When are minimal weighted rewards (not) equal to least fixed points?

lemma 6.1 {name}`T_MinWRew_le_MinWRew`

## Module Level: A Necessary Condition for the LFP Property

definition 6.4 𝓀-inf-distrib

leamm 6.6 we did not formalize

leamm 6.7 {name}`T_MinWRew_eq_MinWRew`

## WDP Level: A Sufficient Condition for the LFP property

definition 6.8 {name}`WDP.WellBehaved`

{docstring WDP.WellBehaved}

example 6.9 {name}`mdp_wellBehaved`

theorem 6.10 {name}`lfp_T_eq_MinWRew`

{name}`WellBehavedModule`

theorem 6.12 {name}`WellBehavedModule.pi`

## Transporting the LFP Property through Normalization

_This section has not been mechanized in Lean._

## Classes of WDPs with the Least Fixed Point Property

corollary 6.24 {name}`wp_eq_op_of_isProb`

corollary 6.25 actic not formalized

corollary 6.26 formal languages not formalized

# Case Studies

_This section has not been mechanized in Lean._

{name}`HSched`

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
