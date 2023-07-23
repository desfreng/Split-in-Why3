# Split-in-Why3

Here you'll find my work on the Why3 ``split-goal-right`` transformation. The aim of this transformation is to split the proof of a large logical formula into several proofs of smaller formulas.

The ``Split Right`` files concern the definition of a transformation that introduces no axioms into the context.

The ``Split Right Sequents`` files concern the definition of a transformation that introduces elements into the context. This transformation operates directly on the proofs. A possible, but inefficient, implementation is given in the ``split.ml`` file.

This project was carried out as part of an internship in the Toccata team at Inria, supervised by Jean-Christophe Filliatre and Andrei Paskievich. The other part of the internship is available on the following GitHub repository: [ROBDD-in-Why3](https://github.com/desfreng/ROBDD-in-Why3).
