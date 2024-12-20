1. Introduction
    - List of contributions with forward references to subsequent chapters
2. Background
    - Syntax
    - Operational semantics
    - Hoare logic
    - Separation logic
3. Incorrectness separation logic
    - Differences with the literature
        New: variable substitution vs registers, Iris style
             Frame baking
             Control flow
    - Over- vs underapproximation
    - Version based on triples
4. Incorrectness logic with post
    - Differences with the literature
        New: incorrectness *separation* logic with *post*
    - Idea of weakestpre
    - Post analogous to weakestpre
    - Post rules
    - Defining triples in terms of post
    - Advantages of post
5. Our formulation vs the formulation in the literature
    - Registers vs variables with substitution
    - Frame baking
    - Control flow
6. Coq mechanization
    New: mechanization of incorrectness logic
7. Related work

Plan:
1. Make section & paragraph structure.
2. Write down the definitions, and the inference rules.
