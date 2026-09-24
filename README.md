# Braided Notions of a Dialogue Category

## On Dialogue Categories

Dialogue categories were introduced by Paul-André Melliès to formalise several intuitions standing behind the game semantics 
of tensorial logic, a ramification of linear logic. According to Melliès, one can think of game semantics as the diagrammatic syntax for negation.
In this setting, game semantics provides an interactive approach to computation and proof theory, where we have a dialogue between Prover and Denier.
If there are the bridges between propositions and types in constructive mathematics, one has similar bridges between propositions and games. Computationally, one can think of this syntax as gamification of linear continuations. Mathematically, a dialogue category is a monoidal category $\mathcal{C}$ with a distinguished object $\bot$ such that for any $A \in \mathcal{C}$
there are internal homs $[A, \bot]_l$ and $[A, \bot]_r$.

In this library, I first of all try to formalise the basic concepts related to dialogue category. A dialogue category itself
is defined as a typeclass:
```lean 4
class DialogueCategory (C : Type v) [Category.{v} C] [MonoidalCategory C] where
  bot : C
  [leftClosed : LeftClosedAt bot]
  [rightClosed : RightClosedAt bot]
```

