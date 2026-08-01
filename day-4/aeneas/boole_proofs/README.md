# Examples using the Boole language

Boole is an intermediate verification language inspired by Boogie and embedded within Lean. It lets classical imperative constructs be interspersed with specifications written in Lean. Implementation-wise it extends the Strata/Core intermediate language, and both are written in Lean 4.

The code lives on a `Boole-sandbox` branch of the cslib repo and is described as a research playground for experimenting with verification features. The contributing guide notes that a prototype translation based on a deep embedding in Strata exists but isn't fully foundational, and that proving Lean metatheorems showing VC discharge actually implies correctness is a long-term goal.