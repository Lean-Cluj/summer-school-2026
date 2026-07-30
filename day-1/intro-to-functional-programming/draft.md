# Intro to Functional Programming

## 1. Entscheidungsproblem (Decision Problem)
Will talk about David Hilbert, the problem itself, Turing and Church.

## 2. Turing Machine
Imperative programs. Turing Machine. Mutations. Variables.

References:
[1] Alan Turing - On Computable Numbers, with an Application to the Entscheidungsproblem
<https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf>

## 3. Lambda Calculus
Definition, examples, problems
Example for booleans, maybe numbers.

Backus-Naur Form of Lambda Calculus
```
T := a      -- variable
   | (λa.T) -- abstraction
   | (T T)  -- application
```

```
((λa.a) b) = b
((λa.a) (λa.a)) = (λa.a) 
```

References:
[1] Alonzo Church - An Unsolvable Problem of Elementary Number Theory
<https://www.cis.upenn.edu/~cis5110/Church-UnsolvableProblemElementary-1936.pdf>

## 4. Typed Lambda Calculus
Some examples, talk about types. Calculus of Constructions?

## 5. Lean
Syntax, examples, problems.

## 6. Dependent Types
Show it, explain it, maybe do a proof of equality.


